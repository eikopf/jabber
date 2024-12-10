//! Import resolution implementation

use std::collections::HashMap;

use crate::{
    ast::{
        common::{Qualifier, ViSp, Vis},
        unbound_lowered as ubd,
    },
    span::{Span, Spanned},
    symbol::Symbol,
};

use super::{
    unbound::UnboundEnv, Env, FileId, Loc, ModId, Module, Name, Res, Type,
    TypeId,
};

/// An environment where imports have been resolved and type constructor name
/// conflicts have been removed.
pub type ImportResEnv =
    Env<Spanned<ubd::Term>, Spanned<ubd::SymType>, HashMap<Symbol, ViSp<Res>>>;

#[derive(Debug, Clone)]
pub enum ImportResError {
    /// A `Res` vs `Res` name conflict.
    ItemNameConflict {
        module: ModId,
        name: Symbol,
        first: Spanned<Res>,
        second: Spanned<Res>,
    },
    /// A `NormalImport` vs `Res` name conflict.
    ImportItemNameConflict {
        module: ModId,
        name: Name,
        item: Spanned<Res>,
        import: Spanned<NormalImport>,
    },
    /// A `NormalImport` vs `NormalImport` name conflict.
    ImportNameConflict {
        module: ModId,
        name: Name,
        first: Spanned<NormalImport>,
        second: Spanned<NormalImport>,
    },
    /// There is no `super` in the package root module.
    UsedSuperInRootModule { span: Span, package: Symbol },
    /// A normalization error.
    Normalization(ImportNormalizationError),
    /// A prefix resolution error.
    Prefix(PrefixResError),
    /// A direct resolution error.
    Direct(DirectResError),
    /// Two constructors of the same type cannot have the same name.
    DuplicateTyConstrNames {
        ty: TypeId,
        first: Name,
        second: Name,
    },
    /// There is at least one cycle among these imports.
    Cycle(Box<[Loc<NormalImport>]>),
}

impl ImportResEnv {
    pub fn from_unbound_env(
        Env {
            files,
            packages,
            modules,
            terms,
            types,
            interner,
        }: UnboundEnv,
    ) -> (Self, Box<[ImportResError]>) {
        let mut errors = Vec::new();
        let mut imports = Vec::new();

        // NOTE: it's important that we don't invalidate any IDs while building
        // the new environment, so we *must not* remove any elements; we can
        // only mark them as necessary

        // move most of the old environment into the new environment, only
        // allocating new buffers for the tables that actually need to be
        // modified. we have to initialize the environment in this invalid
        // state so we can use its methods
        let mut env = ImportResEnv {
            files,
            packages,
            terms,
            types: Vec::with_capacity(types.len()),
            interner,
            modules: Vec::with_capacity(modules.len()),
        };

        // before doing anything else, we scan through the types to check for
        // duplicate constructors and to intern as many strings as possible.
        // importantly, we *cannot* read from the environment's module table
        // during this process, since it hasn't been initialized yet.
        for (
            raw_id,
            Type {
                name,
                module,
                ast: Spanned { item, span },
            },
        ) in types.into_iter().enumerate()
        {
            let id = TypeId(raw_id);
            let file = modules[module.0].file; // grab file id from old module

            let ast = span.with(match item {
                ubd::Type::Adt(ubd::Adt {
                    name,
                    opacity,
                    params,
                    constructors,
                }) => {
                    let name =
                        env.intern_ident_in_invalid_module(name, module, file);
                    let params = params
                        .iter()
                        .map(|&param| {
                            env.intern_ident_in_invalid_module(
                                param, module, file,
                            )
                        })
                        .collect::<Box<_>>();

                    // collect constructors into a hashmap and remove any
                    // constructors with duplicate names, emitting errors
                    // in the process
                    let constructors = {
                        let mut table: HashMap<_, Spanned<ubd::ast::TyConstr>> =
                            HashMap::with_capacity(constructors.len());

                        for constr in constructors {
                            let name = env.intern_ident_in_invalid_module(
                                constr.name,
                                module,
                                file,
                            );
                            let symbol = name.item.item;

                            match table.get(&symbol) {
                                Some(conflict) => {
                                    let second = env
                                        .intern_ident_in_invalid_module(
                                            conflict.name,
                                            module,
                                            file,
                                        );

                                    errors.push(
                                        ImportResError::DuplicateTyConstrNames {
                                            ty: id,
                                            first: name,
                                            second
                                        }
                                    );
                                }
                                None => {
                                    let __prev = table.insert(symbol, constr);
                                    debug_assert!(__prev.is_none());
                                }
                            }
                        }

                        table.shrink_to_fit();
                        table
                    };

                    ubd::Type::Adt(ubd::Adt {
                        name,
                        opacity,
                        params,
                        constructors,
                    })
                }
                ubd::Type::Alias(ubd::TypeAlias { name, params, ty }) => {
                    let name =
                        env.intern_ident_in_invalid_module(name, module, file);
                    let params = params
                        .iter()
                        .map(|&param| {
                            env.intern_ident_in_invalid_module(
                                param, module, file,
                            )
                        })
                        .collect();

                    ubd::Type::Alias(ubd::TypeAlias { name, params, ty })
                }
                ubd::Type::Extern(ubd::ExternType { name, params }) => {
                    let name =
                        env.intern_ident_in_invalid_module(name, module, file);
                    let params = params
                        .iter()
                        .map(|&param| {
                            env.intern_ident_in_invalid_module(
                                param, module, file,
                            )
                        })
                        .collect();

                    ubd::Type::Extern(ubd::ExternType { name, params })
                }
            });

            env.types.push(Type { name, module, ast });
        }

        // convert modules into a flat {Symbol -> Res} mapping, and push
        // their imports into the resolution queue.
        for (
            raw_id,
            Module {
                name,
                parent,
                file,
                package,
                items,
            },
            // HACK: this clone should be avoided!
        ) in modules.clone().into_iter().enumerate()
        {
            let id = ModId(raw_id);
            let mut module = Module {
                name,
                parent,
                file,
                package,
                items: HashMap::<_, Vis<_>>::new(),
            };

            // move imports into the resolution queue
            items
                .imports
                .into_iter()
                .map(|import| (id, import))
                .for_each(|im| imports.push(im));

            let terms = items.terms.into_iter().map(
                |Vis {
                     visibility,
                     item: Spanned { item, span },
                 }| {
                    let name = env.get_term(item).name;
                    (name, visibility.with(span.with(Res::Term(item))))
                },
            );

            let types = items.types.into_iter().map(
                |Vis {
                     visibility,
                     item: Spanned { item, span },
                 }| {
                    let ty = env.get_type(item);
                    let name = ty.name;

                    // explicitly distinguish struct types
                    let res = match ty.ast.is_struct() {
                        true => Res::StructType(item),
                        false => Res::Type(item),
                    };

                    (name, visibility.with(span.with(res)))
                },
            );

            // TODO: give submodules special handling for collisions, since
            // they are "weak symbols" and local items are allowed to shadow
            // them in module scopes

            let submodules = items.submodules.into_iter().map(
                |Vis {
                     visibility,
                     item: Spanned { item, span },
                 }| {
                    // NOTE: this is the call that requires the clone above
                    let name = modules[item.0].name;
                    (name, visibility.with(span.with(Res::Module(item))))
                },
            );

            for (name, item) in terms.chain(types).chain(submodules) {
                match module.items.get(&name) {
                    Some(conflict) => {
                        let err = ImportResError::ItemNameConflict {
                            module: id,
                            name,
                            first: item.item,
                            second: conflict.item,
                        };

                        errors.push(err);
                    }

                    None => {
                        module.items.insert(name, item);
                    }
                };
            }

            env.modules.push(module);
        }

        // resolve all imports simultaneously
        env.resolve_imports(imports, &mut errors);

        // return both the environment *and* the errors
        let errors = errors.into_boxed_slice();
        (env, errors)
    }
}

/// An well-formed import that can be resolved directly.
#[derive(Debug, Clone)]
pub enum NormalImport {
    /// An import like `use package as foo`.
    AliasedPackage { alias: Name },
    /// A standard import whose terminal element is an identifier.
    QualifiedIdent {
        qualifier: Option<Spanned<Qualifier>>,
        prefix: Box<[Name]>,
        item: Name,
        alias: Option<Name>,
    },
    /// An import whose terminal element is the `self` keyword; it must
    /// appear within a tree item and may be aliased.
    QualifiedSelf {
        qualifier: Option<Spanned<Qualifier>>,
        /// INVARIANT: this list cannot be empty
        prefix: Box<[Name]>,
        item: Name,
        alias: Option<Name>,
    },
}

#[derive(Debug, Clone)]
pub enum ImportNormalizationError {
    /// The import `use package` is illegal unless it has an alias.
    UnaliasedPackageItem {
        import_span: Span,
        span: Span,
        module: ModId,
    },
    /// An import like `use foo.bar.package` is obviously malformed.
    IndirectPackageItem {
        import_span: Span,
        span: Span,
        module: ModId,
    },
    /// The import `use super` is illegal, even with an alias.
    SuperItem {
        import_span: Span,
        span: Span,
        module: ModId,
    },
    /// The item `self` can only appear within a tree item.
    DirectSelfItem {
        import_span: Span,
        span: Span,
        module: ModId,
    },
    /// Qualifiers can only appear at the beginning or end of an import.
    InvalidQualifierPosition {
        import_span: Span,
        qualifier: Spanned<Qualifier>,
        module: ModId,
    },
}

impl NormalImport {
    /// Converts an [`unbound::Import`] into a [`NormalImport`].
    fn normalize(
        env: &mut ImportResEnv,
        module: ModId,
        Spanned {
            item:
                ubd::Import {
                    prefix,
                    item,
                    alias,
                },
            span: import_span,
        }: Spanned<ubd::Import>,
    ) -> Result<Spanned<Self>, ImportNormalizationError> {
        let (qualifier, prefix) = match prefix.first() {
            Some(Spanned {
                item: ubd::PathElement::Qualifier(qualifier),
                span,
            }) => (Some(span.with(*qualifier)), &prefix[1..]),
            _ => (None, prefix.as_ref()),
        };

        let prefix = prefix
            .iter()
            .map(|Spanned { item, span }| match *item {
                ubd::PathElement::Qualifier(qualifier) => {
                    Err(ImportNormalizationError::InvalidQualifierPosition {
                        import_span,
                        qualifier: span.with(qualifier),
                        module,
                    })
                }
                ubd::PathElement::Ident(ident) => {
                    Ok(env.intern_ident_in_module(span.with(ident), module))
                }
            })
            // this is basically a stable impl of try_collect
            .try_fold(Vec::new(), |mut buf, res| {
                buf.push(res?);
                Ok(buf)
            })?
            .into_boxed_slice();

        let Spanned { item, span } = item;
        let alias = alias.map(|Spanned { item, span }| {
            env.intern_ident_in_module(span.with(item), module)
        });

        // TODO: add some machinery to track whether imports come from item
        // trees or not, since this is required to handle `self` item imports
        // correctly.

        match (item, alias, prefix.is_empty()) {
            // `super` is always invalid as an item
            (ubd::PathElement::Qualifier(Qualifier::Super), _, _) => {
                Err(ImportNormalizationError::SuperItem {
                    import_span,
                    span,
                    module,
                })
            }
            // any indirect import of `package` is malformed
            (ubd::PathElement::Qualifier(Qualifier::Package), _, false) => {
                Err(ImportNormalizationError::IndirectPackageItem {
                    import_span,
                    span,
                    module,
                })
            }
            // `use package` is an invalid import
            (ubd::PathElement::Qualifier(Qualifier::Package), None, true) => {
                Err(ImportNormalizationError::UnaliasedPackageItem {
                    import_span,
                    span,
                    module,
                })
            }
            // `use package as <alias>` is a well-formed import
            (
                ubd::PathElement::Qualifier(Qualifier::Package),
                Some(alias),
                true,
            ) => Ok(NormalImport::AliasedPackage { alias }),
            // `self` is invalid as a direct item
            (ubd::PathElement::Qualifier(Qualifier::Self_), _, true) => {
                Err(ImportNormalizationError::DirectSelfItem {
                    import_span,
                    span,
                    module,
                })
            }
            // `self` can be imported indirectly in a tree item
            (ubd::PathElement::Qualifier(Qualifier::Self_), _, false) => {
                Ok(NormalImport::QualifiedSelf {
                    qualifier,
                    prefix,
                    item: Loc {
                        item: span.with(env.interner.intern_static("self")),
                        module,
                    },
                    alias,
                })
            }
            // identifiers are always valid items
            (ubd::PathElement::Ident(ident), _, _) => {
                let item = env.intern_ident_in_module(span.with(ident), module);

                Ok(NormalImport::QualifiedIdent {
                    qualifier,
                    prefix,
                    item,
                    alias,
                })
            }
        }
        .map(|import| import_span.with(import))
    }

    /// Returns the [`Name`] that `self` introduces into `module`.
    ///
    /// When `self` is [`NormalImport::QualifiedSelf`], the resulting name is
    /// the penultimate identifier in the import prefix.
    fn nickname(&self) -> Name {
        match self {
            NormalImport::AliasedPackage { alias, .. } => *alias,
            NormalImport::QualifiedIdent { item, alias, .. } => {
                alias.unwrap_or(*item)
            }
            NormalImport::QualifiedSelf { prefix, alias, .. } => {
                alias.unwrap_or_else(|| prefix.last().copied().unwrap())
            }
        }
    }
}

#[derive(Debug, Clone)]
pub enum PrefixResError {
    NotAModuleOrType(Name),
    /// A type can only be the last element of an import prefix, since the
    /// item immediately afterwards must be one of its constructors.
    NonTerminalType(Name),
    ItemDne(Name),
    Private(Name),
}

/// An ID obtained by resolving the prefix of an import.
#[derive(Debug, Clone, Copy)]
pub enum PrefixId {
    Mod(ModId),
    Type(TypeId),
}

#[derive(Debug, Clone, Copy)]
pub enum DirectResError {
    PrefixIsExternType(TypeId),
    PrefixIsTypeAlias(TypeId),
    PrefixIsOpaqueType(TypeId),
    NoSuchTyConstr(TypeId, Symbol),
    ItemIsPrivate(Loc<Res>),
}

impl ImportResEnv {
    fn resolve_imports(
        &mut self,
        imports: Vec<(ModId, ViSp<ubd::Import>)>,
        errors: &mut Vec<ImportResError>,
    ) {
        let mut imports = {
            // build a table to check for duplicates
            let mut import_table = HashMap::<_, ViSp<NormalImport>>::new();

            for (id, Vis { visibility, item }) in imports {
                let import = match NormalImport::normalize(self, id, item) {
                    Ok(import) => visibility.with(import),
                    Err(err) => {
                        errors.push(ImportResError::Normalization(err));
                        continue;
                    }
                };

                let name = import.nickname();

                // handle name collisions with non-import items
                if let Some(Vis { item, .. }) =
                    self.resolve_symbol_in_module(name.item.item, id)
                {
                    errors.push(ImportResError::ImportItemNameConflict {
                        module: id,
                        name,
                        item,
                        import: import.item,
                    });
                    continue;
                }

                // handle name collisions with other imports
                if let Some(Vis { item, .. }) = import_table.get(&name) {
                    errors.push(ImportResError::ImportNameConflict {
                        module: id,
                        name,
                        first: item.clone(),
                        second: import.item,
                    });
                    continue;
                }

                import_table.insert(name, import);
            }

            import_table.into_iter().collect::<Vec<_>>()
        };

        // we're going to do the stupid thing here: if we loop over all the
        // imports and can't resolve any of them (i.e. the length of the queue
        // doesn't change) then we presume we have at least one import cycle,
        // and return that as an error.
        //
        // this is horrifically O(n^2), but users are unlikely to create import
        // cycles in the first place, and even if they do their size is likely
        // to be very small — maybe two or three imports apiece

        loop {
            // we could probably get away without this allocation,
            // but again: we're doing the stupid thing here
            let mut unresolved_imports =
                Vec::<(Name, ViSp<NormalImport>)>::new();
            let remaining_imports = imports.len();

            while let Some((name, import)) = imports.pop() {
                // remember that we've already checked there can be no
                // name collisions

                let (vis, span, import) = import.spread();
                match import {
                    NormalImport::AliasedPackage { alias } => {
                        let module = alias.module;
                        let package = self.get_module(module).package;
                        let root_module = self.get_package(package).root_module;
                        let res = vis.with(span.with(Res::Module(root_module)));

                        let __prev = self
                            .get_module_mut(module)
                            .items
                            .insert(name.item.item, res);

                        debug_assert!(__prev.is_none());
                    }
                    NormalImport::QualifiedIdent {
                        qualifier,
                        ref prefix,
                        item,
                        ..
                    }
                    | NormalImport::QualifiedSelf {
                        qualifier,
                        ref prefix,
                        item,
                        ..
                    } => {
                        let start_module = qualifier
                            .and_then(|qualifier| {
                                self.resolve_qualifier_in_module(
                                    qualifier.item,
                                    name.module,
                                )
                            })
                            .unwrap_or(name.module);

                        let prefix = match self
                            .resolve_import_prefix(start_module, prefix)
                        {
                            Ok(id) => id,
                            Err(err) => {
                                errors.push(ImportResError::Prefix(err));
                                continue;
                            }
                        };

                        match self.resolve_item_with_prefix(item, prefix) {
                            // found it!
                            Ok(Some(Vis {
                                visibility,
                                item: res,
                            })) => {
                                let module = self.get_module_mut(name.module);
                                let __prev = module.items.insert(
                                    name.item.item,
                                    visibility.with(res.item),
                                );
                                debug_assert!(__prev.is_none());
                            }
                            // maybe — push it to the unresolved queue
                            Ok(None) => unresolved_imports
                                .push((name, vis.with(span.with(import)))),
                            // resolution is definitely impossible
                            Err(err) => {
                                errors.push(ImportResError::Direct(err))
                            }
                        }
                    }
                }
            }

            match unresolved_imports.len() {
                // done with no cycles
                0 => break,
                // made some progress, need to go over remaining imports
                x if x < remaining_imports => {
                    imports = unresolved_imports;
                    continue;
                }
                // made no progress, so we have at least one cycle
                x if x == remaining_imports => {
                    let cycle = ImportResError::Cycle(
                        unresolved_imports
                            .into_iter()
                            .map(|(loc, import)| Loc {
                                item: import.item,
                                module: loc.module,
                            })
                            .collect(),
                    );
                    errors.push(cycle);
                    break;
                }
                _ => unreachable!(),
            }
        }
    }

    /// Resolves the given [`Name`] with respect to `prefix` in `self`.
    fn resolve_item_with_prefix(
        &mut self,
        Loc { item, .. }: Name,
        prefix: PrefixId,
    ) -> Result<Option<Vis<Loc<Res>>>, DirectResError> {
        match prefix {
            PrefixId::Mod(id) => match self.get_module(id).items.get(&item) {
                Some(Vis {
                    visibility,
                    item: res,
                }) => match visibility {
                    vis @ ubd::ast::Visibility::Pub(_) => {
                        Ok(Some(vis.with(Loc {
                            item: *res,
                            module: id,
                        })))
                    }
                    ubd::ast::Visibility::Priv => {
                        Err(DirectResError::ItemIsPrivate(Loc {
                            item: *res,
                            module: id,
                        }))
                    }
                },
                // we found no conclusive evidence that we *can't* resolve
                // that name in this module, so we return Ok(None) as the
                // "maybe" value — the caller might want to look again later
                None => Ok(None),
            },
            PrefixId::Type(id) => {
                let Type { name, module, ast } = self.get_type(id);
                let name = *name;
                let module = *module;

                match ast.item() {
                    ubd::Type::Adt(adt) => match adt.is_opaque() {
                        true => Err(DirectResError::PrefixIsOpaqueType(id)),
                        false => {
                            // get the visibility of the prefix in its module
                            let vis = self
                                .get_module(module)
                                .items
                                .get(&name)
                                .unwrap()
                                .visibility;

                            match adt.constructors.get(&item) {
                                Some(constr) => Ok(Some(vis.with(Loc {
                                    item: constr.span.with(Res::TyConstr {
                                        ty: id,
                                        name: item.item,
                                    }),
                                    module,
                                }))),
                                None => Err(DirectResError::NoSuchTyConstr(
                                    id, item.item,
                                )),
                            }
                        }
                    },
                    ubd::Type::Alias(_) => {
                        Err(DirectResError::PrefixIsTypeAlias(id))
                    }
                    ubd::Type::Extern(_) => {
                        Err(DirectResError::PrefixIsExternType(id))
                    }
                }
            }
        }
    }

    fn resolve_import_prefix(
        &mut self,
        module: ModId,
        prefix: &[Name],
    ) -> Result<PrefixId, PrefixResError> {
        let id = PrefixId::Mod(module);
        self.resolve_import_prefix_rec(id, prefix)
    }

    fn resolve_import_prefix_rec(
        &mut self,
        id: PrefixId,
        prefix: &[Name],
    ) -> Result<PrefixId, PrefixResError> {
        match (id, prefix) {
            (_, []) => Ok(id),
            (PrefixId::Mod(local_module), [head, tail @ ..]) => {
                let res =
                    self.resolve_symbol_in_module(head.item.item, local_module);
                match res {
                    Some(res) if !res.is_visible() => {
                        Err(PrefixResError::Private(*head))
                    }
                    Some(res) => match res.as_prefix() {
                        Some(id) => self.resolve_import_prefix_rec(id, tail),
                        None => Err(PrefixResError::NotAModuleOrType(*head)),
                    },
                    None => Err(PrefixResError::ItemDne(*head)),
                }
            }
            // types can only appear as the last element in an import prefix
            (PrefixId::Type(_), [head, ..]) => {
                Err(PrefixResError::NonTerminalType(*head))
            }
        }
    }

    fn intern_ident_in_module(
        &mut self,
        Spanned { span, .. }: Spanned<ubd::ast::Ident>,
        module: ModId,
    ) -> Name {
        let symbol = self
            .intern_source_span_in_module(module, span)
            .expect("Idents always span valid UTF-8 bytes");

        let item = span.with(symbol);

        Name { item, module }
    }

    /// An alternative to [`Env::intern_ident_in_module`] for use during the
    /// construction phase where the module table is invalid.
    ///
    /// In the primary constructor for [`ImportResEnv`], the new environment is
    /// invalid for most of the duration of the function call. In order to
    /// process the `types` field of the `env` parameter, we need to reference
    /// module IDs *and* file IDs, but we don't need the modules to be valid
    /// while doing so.
    fn intern_ident_in_invalid_module(
        &mut self,
        Spanned { span, .. }: Spanned<ubd::ast::Ident>,
        module: ModId,
        file: FileId,
    ) -> Name {
        let symbol = self
            .intern_source_span_in_file(file, span)
            .expect("Idents always span valid UTF-8 bytes");

        let item = span.with(symbol);

        Name { item, module }
    }

    fn resolve_symbol_in_module(
        &mut self,
        name: Symbol,
        module: ModId,
    ) -> Option<ViSp<Res>> {
        self.get_module(module).items.get(&name).copied()
    }

    /// Resolves `qualifier` to a [`ModId`], returning `None` if and only if
    /// `qualifier` is `Super` and `module` is a package root module.
    fn resolve_qualifier_in_module(
        &self,
        qualifier: Qualifier,
        module: ModId,
    ) -> Option<ModId> {
        match qualifier {
            Qualifier::Super => self.get_module(module).parent,
            Qualifier::Self_ => Some(module),
            Qualifier::Package => Some(
                self.get_package(self.get_module(module).package)
                    .root_module,
            ),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::{path::PathBuf, str::FromStr};

    use crate::cst::Parser;
    use crate::package as pkg;

    use super::*;

    #[test]
    fn build_import_res_env_from_core() {
        let path = PathBuf::from_str("../../libs/core").unwrap();
        let package = pkg::Package::load_files(path).unwrap();
        let mut parser = Parser::new().unwrap();

        let package = package
            .map_modules(|file| parser.parse(file))
            .transpose()
            .unwrap()
            .map_modules(crate::ast::unbound::Ast::try_from)
            .transpose()
            .unwrap()
            .map_modules(crate::ast::unbound_lowered::Ast::from);

        let mut env = UnboundEnv::new();
        let (core_symbol, ingest_warnings, ingest_errors) =
            env.consume_package(package, Box::new([]));

        dbg!(ingest_warnings);
        dbg!(ingest_errors);

        let (mut env, errors) = ImportResEnv::from_unbound_env(env);
        dbg!(errors.len());

        let root_module =
            env.get_module(env.get_package(core_symbol).root_module);
        dbg!(root_module.items.len());

        for (key, value) in root_module.items.iter() {
            let key = env.interner.resolve(*key).unwrap();
            eprintln!("{} : {:?}", key, value);
        }

        let prelude_symbol = env.interner.intern_static("prelude");
        let prelude = env.get_module(
            env.get_module(env.get_package(core_symbol).root_module)
                .items
                .get(&prelude_symbol)
                .unwrap()
                .item()
                .as_module()
                .unwrap(),
        );

        for (name, item) in prelude.items.iter() {
            let name = env.interner.resolve(*name).unwrap();

            eprintln!(
                "(public={:?}) {} := {:#?}",
                item.is_visible(),
                name,
                item,
            );
        }

        dbg!(&env.interner);

        //panic!();
    }
}
