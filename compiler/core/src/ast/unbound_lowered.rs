//! A slightly-lowered form of [`crate::ast::unbound`] that splits declarations
//! into their separate namespaces, as well as flattening imports into a
//! uniform representation.

use std::collections::HashMap;

use crate::{
    source_file::SourceFile,
    span::{Span, SpanSeq, Spanned},
};

use super::{
    common::{Qualifier, ViSp},
    SpannedModuleTrivia,
};

pub use super::unbound as ast;

#[derive(Debug, Clone)]
pub struct Ast {
    pub trivia: SpannedModuleTrivia,
    pub file: SourceFile,
    pub imports: Box<[ViSp<Import>]>,
    pub modules: Box<[ViSp<Mod>]>,
    pub terms: Box<[ViSp<Term>]>,
    pub types: Box<[ViSp<Type>]>,
}

impl From<ast::Ast> for Ast {
    fn from(value: ast::Ast) -> Self {
        AstLowerer::lower(value)
    }
}

/// Unified representation of a use item.
#[derive(Debug, Clone)]
pub struct Import {
    pub prefix: SpanSeq<PathElement>,
    pub item: Spanned<PathElement>,
    pub alias: Option<Spanned<ast::Ident>>,
}

#[derive(Debug, Clone, Copy)]
pub enum PathElement {
    Qualifier(Qualifier),
    Ident(ast::Ident),
}

#[derive(Debug, Clone, Copy)]
pub struct Mod {
    pub name: Spanned<ast::Ident>,
}

#[derive(Debug, Clone)]
pub enum Term {
    Fn(Fn),
    ExternFn(ExternFn),
    Const(Const),
}

impl Term {
    pub fn name<'a, 'b: 'a>(&'a self, source: &'b [u8]) -> &'b str {
        let name = match self {
            Term::Fn(Fn { name, .. })
            | Term::ExternFn(ExternFn { name, .. })
            | Term::Const(Const { name, .. }) => name,
        };

        name.span.in_source(source).unwrap()
    }
}

#[derive(Debug, Clone)]
pub struct Fn {
    pub name: Spanned<ast::Ident>,
    pub params: Spanned<SpanSeq<ast::Parameter>>,
    pub return_ty: Option<Spanned<ast::Ty>>,
    pub body: Spanned<ast::FnBody>,
}

#[derive(Debug, Clone)]
pub struct ExternFn {
    pub name: Spanned<ast::Ident>,
    pub params: Spanned<SpanSeq<ast::Parameter>>,
    pub return_ty: Option<Spanned<ast::Ty>>,
}

#[derive(Debug, Clone)]
pub struct Const {
    pub name: Spanned<ast::Ident>,
    pub ty: Spanned<ast::Ty>,
    pub value: Spanned<ast::Expr>,
}

/// A partially interned type AST for use during import resolution.
pub type SymType = Type<
    crate::env::Name,
    Box<[crate::env::Name]>,
    HashMap<crate::symbol::Symbol, Spanned<ast::TyConstr>>,
>;

/// The AST of a type item.
///
/// # Type Parameters
/// - `N` defines the type of the name field in all members;
/// - `P` defines the type of the params field in all members;
/// - `C` defines the type of the constructors field in [`Adt`].
#[derive(Debug, Clone)]
pub enum Type<
    N = Spanned<ast::Ident>,
    P = SpanSeq<ast::Ident>,
    C = SpanSeq<ast::TyConstr>,
> {
    Adt(Adt<N, P, C>),
    Alias(TypeAlias<N, P>),
    Extern(ExternType<N, P>),
}

impl Type {
    pub fn name<'a, 'b: 'a>(&'a self, source: &'b [u8]) -> &'b str {
        let name = match self {
            Type::Adt(Adt { name, .. })
            | Type::Alias(TypeAlias { name, .. })
            | Type::Extern(ExternType { name, .. }) => name,
        };

        name.span.in_source(source).unwrap()
    }
}

impl SymType {
    /// Returns `true` iff `self` is a non-opaque ADT and has a single
    /// constructor whose name is exactly the same as the name of `self`.
    pub fn is_struct(&self) -> bool {
        match self {
            Type::Adt(Adt {
                name,
                opacity: None,
                constructors,
                ..
            }) if constructors.len() == 1 => {
                constructors.contains_key(&name.item)
            }
            _ => false,
        }
    }
}

impl<N, P, C> Type<N, P, C> {
    pub fn is_opaque(&self) -> bool {
        !matches!(self, Type::Adt(Adt { opacity: None, .. }))
    }
}

#[derive(Debug, Clone)]
pub struct Adt<
    N = Spanned<ast::Ident>,
    P = SpanSeq<ast::Ident>,
    C = SpanSeq<ast::TyConstr>,
> {
    pub name: N,
    pub opacity: Option<Span>,
    pub params: P,
    pub constructors: C,
}

impl<N, P, C> Adt<N, P, C> {
    pub fn is_opaque(&self) -> bool {
        matches!(
            self,
            Adt {
                opacity: Some(_),
                ..
            }
        )
    }
}

#[derive(Debug, Clone)]
pub struct TypeAlias<N = Spanned<ast::Ident>, P = SpanSeq<ast::Ident>> {
    pub name: N,
    pub params: P,
    pub ty: Spanned<ast::Ty>,
}

#[derive(Debug, Clone)]
pub struct ExternType<N = Spanned<ast::Ident>, P = SpanSeq<ast::Ident>> {
    pub name: N,
    pub params: P,
}

struct AstLowerer {
    imports: Vec<ViSp<Import>>,
    modules: Vec<ViSp<Mod>>,
    terms: Vec<ViSp<Term>>,
    types: Vec<ViSp<Type>>,
}

impl AstLowerer {
    fn new() -> Self {
        Self {
            imports: Vec::new(),
            modules: Vec::new(),
            terms: Vec::new(),
            types: Vec::new(),
        }
    }

    fn lower(
        ast::Ast {
            trivia,
            decls,
            file,
        }: ast::Ast,
    ) -> Ast {
        let mut lowerer = Self::new();

        for decl in decls {
            lowerer.visit_decl(decl);
        }

        Ast {
            trivia,
            file,
            imports: lowerer.imports.into_boxed_slice(),
            modules: lowerer.modules.into_boxed_slice(),
            terms: lowerer.terms.into_boxed_slice(),
            types: lowerer.types.into_boxed_slice(),
        }
    }

    fn visit_decl(&mut self, decl: Spanned<ast::Decl>) {
        let ast::Decl {
            visibility,
            kind: Spanned { item, span },
            ..
        } = decl.item;

        match item {
            ast::DeclKind::Use { item } => {
                let mut imports = self
                    .lower_use_item(item)
                    .into_iter()
                    .map(|import| visibility.with(import))
                    .collect::<Vec<_>>();

                self.imports.append(&mut imports);
            }
            ast::DeclKind::Mod { name } => {
                let module = visibility.with(span.with(Mod { name }));
                self.modules.push(module);
            }
            ast::DeclKind::TypeAlias { name, params, ty } => {
                let alias = Type::Alias(TypeAlias { name, params, ty });
                let ty = visibility.with(span.with(alias));
                self.types.push(ty);
            }
            ast::DeclKind::Type {
                name,
                opacity,
                params,
                constructors,
            } => {
                let adt = Adt {
                    name,
                    opacity,
                    params,
                    constructors,
                };

                let ty = visibility.with(span.with(Type::Adt(adt)));
                self.types.push(ty);
            }
            ast::DeclKind::ExternType { name, params } => {
                let extern_ty = ExternType { name, params };
                let ty = visibility.with(span.with(Type::Extern(extern_ty)));
                self.types.push(ty);
            }
            ast::DeclKind::Fn {
                name,
                params,
                return_ty,
                body,
            } => {
                let func = Fn {
                    name,
                    params,
                    return_ty,
                    body: *body,
                };

                let term = visibility.with(span.with(Term::Fn(func)));
                self.terms.push(term);
            }
            ast::DeclKind::ExternFn {
                name,
                params,
                return_ty,
            } => {
                let extern_fn = ExternFn {
                    name,
                    params,
                    return_ty,
                };

                let term =
                    visibility.with(span.with(Term::ExternFn(extern_fn)));
                self.terms.push(term);
            }
            ast::DeclKind::Const { name, ty, value } => {
                let const_ = Const { name, ty, value };
                let term = visibility.with(span.with(Term::Const(const_)));
                self.terms.push(term);
            }
        }
    }

    fn lower_use_item(
        &mut self,
        item: Spanned<ast::UseItem>,
    ) -> Vec<Spanned<Import>> {
        let mut items = Vec::new();
        lower_use_item_rec(&mut items, Vec::new(), item);
        items
    }
}

fn lower_use_item_rec(
    items: &mut Vec<Spanned<Import>>,
    mut prefix: Vec<Spanned<PathElement>>,
    Spanned { item, span }: Spanned<ast::UseItem>,
) {
    match item {
        ast::UseItem::Name(name) => {
            let item = strip_prefix(&mut prefix, span.with(name));
            let import = Import {
                prefix: prefix.into_boxed_slice(),
                item,
                alias: None,
            };

            items.push(span.with(import));
        }
        ast::UseItem::Alias { item, alias } => {
            let item = strip_prefix(&mut prefix, item);
            let import = Import {
                prefix: prefix.into_boxed_slice(),
                item,
                alias: Some(alias),
            };

            items.push(span.with(import));
        }
        ast::UseItem::Tree {
            root,
            items: use_items,
        } => {
            if let Some(root) = root {
                let item = strip_prefix(&mut prefix, root);
                prefix.push(item);
            }

            for item in use_items {
                lower_use_item_rec(items, prefix.clone(), item);
            }
        }
    }
}

fn strip_prefix(
    prefix: &mut Vec<Spanned<PathElement>>,
    Spanned { item, span }: Spanned<ast::Name>,
) -> Spanned<PathElement> {
    match item {
        ast::Name::Ident(ident) => span.with(PathElement::Ident(ident)),
        ast::Name::Path(Some(qualifier), idents) if idents.is_empty() => {
            qualifier.map(PathElement::Qualifier)
        }
        ast::Name::Path(qualifier, idents) => {
            if let Some(qualifier) = qualifier {
                prefix.push(qualifier.map(PathElement::Qualifier));
            }

            let (item, prefix_idents) = idents.split_last().expect(
                "idents cannot be empty due to the previous guard expression",
            );

            for ident in prefix_idents {
                prefix.push(ident.map(PathElement::Ident));
            }

            item.map(PathElement::Ident)
        }
    }
}
