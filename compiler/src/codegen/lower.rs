//! Primary lowering implementation.

use std::collections::HashMap;

use crate::{
    ast::{
        attr::{Attr, AttrArg, AttrName},
        typed::{self as ast, TyConstrIndex},
    },
    codegen::{blame::Blame, scm::MatchArm},
    env::{
        FileId, ModId, Package, Res, Term, TermId, TypeId,
        resolve::BoundResult,
        typed::{TyVar, TypedEnv},
    },
    span::Spanned,
    symbol::Symbol,
    unique::Uid,
};

use super::{
    blame::Blamed,
    repr::{MonoTyId, Shape, Variant},
    scm::{Builtin, Expr, Literal, Pattern},
};

#[derive(Debug, Clone, Copy)]
pub struct Def<T> {
    pub module: ModId,
    pub name: Blamed<Symbol>,
    pub value: T,
}

#[derive(Debug, Clone)]
pub struct LoweredPackage {
    pub name: Symbol,
    pub root_file: FileId,
    pub externals: Vec<Def<Symbol>>,
    pub constrs: Vec<Def<Blamed<Expr>>>,
    pub functions: Vec<Def<Blamed<Expr>>>,
    pub constants: Vec<Def<Blamed<Expr>>>,
}

impl LoweredPackage {
    pub fn new(name: Symbol, root_file: FileId) -> Self {
        Self {
            name,
            root_file,
            externals: Default::default(),
            constrs: Default::default(),
            functions: Default::default(),
            constants: Default::default(),
        }
    }
}

#[derive(Debug)]
pub struct Lowerer<'a> {
    /// The typechecked environment.
    env: &'a mut TypedEnv,
    /// The canonical names for each term.
    canonical_term_names: HashMap<TermId, Symbol>,
    /// The canonical names for each type constructor.
    canonical_constr_names: HashMap<TyConstrIndex, Symbol>,
    /// The cached per-type shapes.
    named_type_shapes: HashMap<TypeId, Shape>,
    /// The type constructor definitions generated while lowering.
    type_constr_definitions: HashMap<TyConstrIndex, Def<Blamed<Expr>>>,
    /// The canonical orderings of the fields of record constructors.
    field_indices: HashMap<(TyConstrIndex, Symbol), usize>,
    /// Lowered monotype representations.
    type_reprs: HashMap<MonoTyId, Shape>,
    /// The next unused monotype ID.
    next_mono_ty_id: MonoTyId,
    /// The symbol for the string `scheme`.
    scheme_symbol: Symbol,
}

macro_rules! call {
    ($callee:expr; $args:expr) => {
        crate::codegen::scm::Expr::Call {
            callee: std::boxed::Box::new($callee),
            args: $args.into(),
        }
    };

    ($callee:expr, $($arg:expr),+) => {
        crate::codegen::scm::Expr::Call {
            callee: std::boxed::Box::new($callee),
            args: vec![$($arg,)+].into_boxed_slice(),
        }
    };

    ($callee:expr) => {
        crate::codegen::scm::Expr::Call {
            callee: std::boxed::Box::new($callee),
            args: std::default::Default::default(),
        }
    };
}

impl<'a> Lowerer<'a> {
    pub fn new(env: &'a mut TypedEnv) -> Self {
        let scheme_symbol = env.interner.intern_static("scheme");

        Self {
            env,
            canonical_term_names: Default::default(),
            canonical_constr_names: Default::default(),
            named_type_shapes: Default::default(),
            type_constr_definitions: Default::default(),
            field_indices: Default::default(),
            type_reprs: Default::default(),
            next_mono_ty_id: MonoTyId::MIN,
            scheme_symbol,
        }
    }

    pub fn lower_package(&mut self, package: Symbol) -> LoweredPackage {
        let Package {
            root_module,
            version: _,
            dependencies: _,
        } = self.env.get_package(package);

        // create an empty lowered package
        let mut lowered_package = LoweredPackage::new(
            package,
            self.env.get_module(*root_module).file,
        );

        // accumulate the IDs for the terms in the package
        let terms = {
            let mut terms = Vec::new();
            collect_terms(self.env, *root_module, &mut terms);
            terms.into_boxed_slice()
        };

        // lower the terms in arbitrary order, writing the results to lowered_package
        for term_id in terms {
            let Term { module, ast, .. } = self.env.get_term(term_id);
            let file = self.env.get_module(*module).file;

            let blame = Blame {
                file,
                span: ast.span(),
            };

            // HACK: evil unnecessary clone!!!
            let term = ast.item().clone();
            self.lower_term(&mut lowered_package, blame, *module, &term);
        }

        // finally, dump the type constructor defs generated during lowering into the package
        let constrs = self.type_constr_definitions.drain();
        lowered_package.constrs.extend(constrs.map(|(_, def)| def));

        // return the package
        lowered_package
    }

    pub fn lower_term(
        &mut self,
        package: &mut LoweredPackage,
        blame: Blame,
        module: ModId,
        ast::Term {
            attrs,
            name,
            ty: _,
            kind,
        }: &ast::Term<TyVar>,
    ) {
        let name = {
            let file = self.env.get_module(module).file;
            let span = name.content.span();
            let blame = Blame { file, span };

            blame.with(name.content.item)
        };

        match kind {
            ast::TermKind::ExternFn { .. } => {
                let value = self
                    .get_scheme_external(attrs)
                    .expect("missing scheme external for extern function");

                let def = Def {
                    module,
                    name,
                    value,
                };

                package.externals.push(def);
            }
            ast::TermKind::Fn { params, body, .. } => {
                let body = self.lower_expr(body.item().as_ref());
                let value = blame.with(self.lower_params(params, body));

                let def = Def {
                    module,
                    name,
                    value,
                };

                package.functions.push(def);
            }
            ast::TermKind::Const { value, .. } => {
                dbg![value];
            }
        }
    }

    fn lower_params(
        &mut self,
        params: &[Spanned<ast::Parameter<TyVar>>],
        body: Expr,
    ) -> Expr {
        let patterns = params
            .iter()
            .map(|param| self.lower_pattern(param.pattern.item()))
            .collect();

        let body = Box::new(body);

        Expr::MatchLambdaVariadic { patterns, body }
    }

    fn lower_expr(
        &mut self,
        ast::Typed { item, ty: _ }: ast::Typed<&ast::Expr<TyVar>, TyVar>,
    ) -> Expr {
        match item {
            ast::Expr::Local(name) => Expr::Symbol(name.content.item),
            ast::Expr::Global(ast::Name { id, .. }) => match *id {
                Res::Term(term) => Expr::Symbol(self.get_canonical_name(term)),
                Res::TyConstr { ty, name } => Expr::Symbol(
                    self.get_type_constr_name(TyConstrIndex { ty, name }),
                ),
                _ => panic!("encountered a module or type Res while rendering"),
            },
            ast::Expr::Literal(literal) => self.lower_literal(*literal),
            ast::Expr::List(elems) => {
                let list = Expr::Builtin(Builtin::List);
                let elems: Box<_> = elems
                    .iter()
                    .map(|elem| self.lower_expr(elem.item().as_ref()))
                    .collect();

                call!(list; elems)
            }
            ast::Expr::Tuple(elems) => {
                let vector = Expr::Builtin(Builtin::Vector);
                let elems: Box<_> = elems
                    .iter()
                    .map(|elem| self.lower_expr(elem.item().as_ref()))
                    .collect();

                call!(vector; elems)
            }
            ast::Expr::Block {
                statements,
                return_expr,
            } => todo!(),
            ast::Expr::RecordConstr { name, fields, base } => {
                // TODO: we need to do the following:
                // 1. if base is present, use it to fill in missing fields
                // 2. otherwise just iterate over the fields directly
                // 3. each field is assigned its index in the vector by the order among Symbols

                let constr = match name.id() {
                    ast::BindingId::Global(Res::TyConstr { ty, name }) => {
                        TyConstrIndex { ty, name }
                    }
                    ast::BindingId::Global(Res::StructType(ty)) => {
                        let name = self.env.get_type(ty).name;
                        TyConstrIndex { ty, name }
                    }
                    _ => panic!("bad record constructor name"),
                };

                let discriminant = self.discriminant(constr);

                // TODO: we have two options depending on whether base is Some or not
                // 1. if base is Some, we need to evaluate it in a `let` binding and then use
                //    (vector-ref) to access its fields; otherwise
                // 2. if base is None then we just assign fields sequentially

                match base {
                    None => todo!(),
                    Some(_) => todo!(),
                }
            }
            ast::Expr::RecordField { item, field } => todo!(),
            ast::Expr::TupleField { item, field } => {
                let vector_ref = Expr::Builtin(Builtin::VectorRef);
                let item = self.lower_expr(item.item().as_ref());
                let field = Expr::Literal(Literal::UInt(field.item as u64));

                call!(vector_ref, item, field)
            }
            ast::Expr::Lambda { params, body } => {
                let body = self.lower_expr(body.item.as_ref());
                self.lower_params(params, body)
            }
            ast::Expr::Call { callee, args, .. } => {
                let callee = self.lower_expr(callee.item().as_ref());
                let args: Box<_> = args
                    .iter()
                    .map(|arg| self.lower_expr(arg.item().as_ref()))
                    .collect();

                call!(callee; args)
            }
            ast::Expr::Lazy { operator, lhs, rhs } => {
                let op = Expr::Builtin(match operator.item {
                    ast::LazyOperator::And => Builtin::And,
                    ast::LazyOperator::Or => Builtin::Or,
                });

                let lhs = self.lower_expr(lhs.item().as_ref());
                let rhs = self.lower_expr(rhs.item().as_ref());

                call!(op, lhs, rhs)
            }
            ast::Expr::Mutate {
                item, field, rhs, ..
            } => todo!(),
            ast::Expr::Match { scrutinee, arms } => {
                let scrutinee =
                    Box::new(self.lower_expr(scrutinee.item.as_ref()));

                let arms = arms
                    .iter()
                    .map(|arm| arm.item())
                    .map(|ast::MatchArm { pattern, body }| {
                        let pattern = self.lower_pattern(pattern.item());
                        let body = self.lower_expr(body.item.as_ref());

                        MatchArm { pattern, body }
                    })
                    .collect();

                Expr::Match { scrutinee, arms }
            }
        }
    }

    fn lower_literal(&self, literal: ast::LiteralExpr) -> Expr {
        match literal {
            ast::LiteralExpr::Unit => call!(Expr::Builtin(Builtin::Void)),
            ast::LiteralExpr::Bool(true) => Expr::Literal(Literal::True),
            ast::LiteralExpr::Bool(false) => Expr::Literal(Literal::False),
            ast::LiteralExpr::Char(c) => Expr::Literal(Literal::Char(c)),
            ast::LiteralExpr::String(s) => Expr::Literal(Literal::String(s)),
            ast::LiteralExpr::Int(i) => Expr::Literal(Literal::UInt(i)),
            ast::LiteralExpr::Float(f) => Expr::Literal(Literal::Float(f)),
            ast::LiteralExpr::Malformed(_) => panic!(
                "encountered a malformed literal expression during lowering"
            ),
        }
    }

    fn lower_pattern<V>(&mut self, pattern: &ast::Pattern<V>) -> Pattern {
        match pattern {
            ast::Pattern::Wildcard => Pattern::Wildcard,
            ast::Pattern::Literal(literal) => match literal {
                ast::LiteralExpr::Unit => Pattern::Wildcard,
                ast::LiteralExpr::Bool(true) => Pattern::Literal(Literal::True),
                ast::LiteralExpr::Bool(false) => {
                    Pattern::Literal(Literal::False)
                }
                ast::LiteralExpr::Char(c) => {
                    Pattern::Literal(Literal::Char(*c))
                }
                ast::LiteralExpr::String(s) => {
                    Pattern::Literal(Literal::String(*s))
                }
                ast::LiteralExpr::Int(i) => Pattern::Literal(Literal::UInt(*i)),
                ast::LiteralExpr::Float(f) => {
                    Pattern::Literal(Literal::Float(*f))
                }
                ast::LiteralExpr::Malformed(_) => panic!(
                    "encountered a malformed literal expression during lowering"
                ),
            },
            ast::Pattern::Var(var) => {
                let name = var.content.item;
                Pattern::Ident(name)
            }
            ast::Pattern::Tuple(pats) => Pattern::Vector(
                pats.iter().map(|pat| self.lower_pattern(pat)).collect(),
            ),
            ast::Pattern::List(pats) => Pattern::List(
                pats.iter().map(|pat| self.lower_pattern(pat)).collect(),
            ),
            ast::Pattern::Cons { head, tail } => {
                let head = Box::new(self.lower_pattern(head.item()));
                let tail = Box::new(self.lower_pattern(tail.item()));

                Pattern::Cons { head, tail }
            }
            ast::Pattern::UnitConstr { name } => {
                let shape = self.shape_of_named_type(name.id.ty);

                match shape {
                    Shape::Prim(_)
                    | Shape::MutBox
                    | Shape::Extern { .. }
                    | Shape::Fn { .. } => unreachable!(),
                    // the constr `1 -> List[T]` is Nil
                    Shape::List => Pattern::nil(),
                    // the constr `1 -> Option[T]` is None, rendered as `#f`.
                    Shape::Option => Pattern::Literal(Literal::False),
                    Shape::Struct { arity } => {
                        assert!(arity == 0);
                        Pattern::Wildcard
                    }
                    Shape::Variants(_) => Pattern::Vector(
                        self.discriminant(name.id)
                            .map(Pattern::Literal)
                            .into_iter()
                            .collect(),
                    ),
                }
            }
            ast::Pattern::TupleConstr { name, elems } => {
                let shape = self.shape_of_named_type(name.id.ty);
                let prefix = self.discriminant(name.id).map(Pattern::Literal);
                let fields = elems.iter().map(|elem| self.lower_pattern(elem));

                match shape {
                    Shape::Prim(_)
                    | Shape::MutBox
                    | Shape::Extern { .. }
                    | Shape::Fn { .. } => unreachable!(),
                    Shape::List => {
                        assert!(elems.len() == 2);
                        let mut fields = fields;
                        let head = Box::new(fields.next().unwrap());
                        let tail = Box::new(fields.next().unwrap());
                        Pattern::Cons { head, tail }
                    }
                    Shape::Option => {
                        assert!(elems.len() == 1);
                        let mut fields = fields;
                        let inner = Box::new(fields.next().unwrap());
                        Pattern::Box(inner)
                    }
                    Shape::Struct { arity } => {
                        assert_eq!(elems.len(), arity);
                        Pattern::Vector(fields.collect())
                    }
                    Shape::Variants(_) => Pattern::Vector(
                        prefix.into_iter().chain(fields).collect(),
                    ),
                }
            }
            ast::Pattern::RecordConstr { name, fields, rest } => {
                let shape = self.shape_of_named_type(name.id.ty);
                let prefix = self.discriminant(name.id).map(Pattern::Literal);
                let fields = fields
                    .iter()
                    .map(|field| {
                        let name = field.name;
                        let pattern = self.lower_pattern(field.pattern.item());

                        (name, pattern)
                    })
                    .collect::<HashMap<_, _>>();

                match shape {
                    Shape::Prim(_)
                    | Shape::List
                    | Shape::Option
                    | Shape::Extern { .. }
                    | Shape::Fn { .. } => unreachable!(),
                    Shape::MutBox => todo!(),
                    Shape::Struct { arity } => todo!(),
                    Shape::Variants(_) => todo!(),
                }
            }
        }
    }

    fn get_field_index(
        &mut self,
        constr: TyConstrIndex,
        field: Symbol,
    ) -> usize {
        todo!()
    }

    /// Returns the symbol corresponding to the given type constructor function definition,
    /// generating and memoizing its declaration if it has not already been generated.
    fn get_type_constr_name(&mut self, constr: TyConstrIndex) -> Symbol {
        match self.canonical_constr_names.get(&constr) {
            Some(name) => *name,
            None => {
                // TODO: we have to do several things here
                // 1. render the constructor into an expression
                // 2. bind it to a name and push it into self.type_constructor_definitions
                // 3. return the name as a symbol

                // render constructor into an expression
                let value = self.generate_constr_expr(constr);

                // get its canonical name
                let name = {
                    // fetch module path and type symbol
                    let module = self.env.get_type(constr.ty).module;
                    let module_path = self.env.module_path(module);
                    let ty_symbol = self.env.get_type(constr.ty).name;

                    // get rough blame
                    let file = self.env.get_module(module).file;
                    let span = self.get_constr(constr).ast.name.span();
                    let blame = Blame { file, span };

                    // sequence name components
                    let components = module_path
                        .into_iter()
                        .map(|id| self.env.get_module(id).name)
                        .chain(std::iter::once(ty_symbol));

                    // allocate buffer
                    let mut buf = String::new();

                    // write prefix elements
                    for component in components {
                        let s = self.env.interner.resolve(component).unwrap();
                        buf.push_str(s);
                        buf.push('/');
                    }

                    // write the final base name
                    let base_name =
                        self.env.interner.resolve(constr.name).unwrap();
                    buf.push_str(base_name);

                    // intern the canonical name and return
                    blame.with(self.env.interner.intern(&buf))
                };

                // make and cache definition
                self.type_constr_definitions.insert(
                    constr,
                    Def {
                        module: self.env.get_type(constr.ty).module,
                        name,
                        value,
                    },
                );

                // return symbol
                name.item
            }
        }
    }

    /// Returns an expression corresponding to the given constructor.
    fn generate_constr_expr(&mut self, constr: TyConstrIndex) -> Blamed<Expr> {
        /// The renderable constructor kinds.
        #[derive(Debug, Clone, Copy, PartialEq, Eq)]
        enum ConstrKind {
            Unit,
            Tuple,
        }

        let blame = {
            let module = self.env.get_type(constr.ty).module;
            let file = self.env.get_module(module).file;
            let span = self.get_constr(constr).span;

            Blame { file, span }
        };

        let shape = self.shape_of_named_type(constr.ty);
        let (arity, kind) = match &self.get_constr(constr).kind {
            ast::TyConstrKind::Unit(_) => (0, ConstrKind::Unit),
            ast::TyConstrKind::Tuple { elems, .. } => {
                (elems.len(), ConstrKind::Tuple)
            }
            ast::TyConstrKind::Record(_) => {
                panic!("tried to render a record constructor as a function")
            }
        };

        blame.with(match shape {
            Shape::Prim(_)
            | Shape::MutBox
            | Shape::Extern { .. }
            | Shape::Fn { .. } => unreachable!(),
            Shape::List => match kind {
                ConstrKind::Unit => call!(Expr::Builtin(Builtin::List)),
                ConstrKind::Tuple => Expr::Builtin(Builtin::Cons),
            },
            Shape::Option => match kind {
                ConstrKind::Unit => Expr::Literal(Literal::False),
                ConstrKind::Tuple => Expr::Builtin(Builtin::Box),
            },
            // HACK: no arity checking, just direct reference to `vector`
            Shape::Struct { arity: _ } => Expr::Builtin(Builtin::Vector),
            Shape::Variants(_) => {
                // get discriminant
                let discriminant = self.discriminant(constr).unwrap();

                // generate free parameter names
                let params = (0..arity)
                    .map(|n| {
                        let param = format!("arg{n}");
                        self.env.interner.intern(&param)
                    })
                    .collect::<Box<_>>();

                // sequence arguments
                let args = std::iter::once(Expr::Literal(discriminant))
                    .chain(params.iter().copied().map(Expr::Symbol));

                // generate (lambda [arg0 arg1 ...] (vector discriminant arg0 arg1 ...))
                Expr::Lambda {
                    args: params.clone(),
                    body: Box::new(
                        call!(Expr::Builtin(Builtin::Vector); args.collect::<Vec<_>>()),
                    ),
                }
            }
        })
    }

    fn get_canonical_name(&mut self, term: TermId) -> Symbol {
        match self.canonical_term_names.get(&term) {
            Some(name) => *name,
            None => {
                // get module prefix
                let module = self.env.get_term(term).module;
                let module_path = self.env.module_path(module);
                let (_root, module_prefix) = module_path.split_first().unwrap();

                // get the term's base name
                let base_symbol = self.env.get_term(term).name;
                let base_name = self.env.interner.resolve(base_symbol).unwrap();

                // resolve module names
                let prefix_components = module_prefix.iter().map(|&module| {
                    let mod_name = self.env.get_module(module).name;
                    self.env.interner.resolve(mod_name).unwrap()
                });

                // assemble name in memory
                let name = {
                    let mut name = String::new();

                    for elem in prefix_components {
                        name.push_str(elem);
                        name.push('/');
                    }

                    name.push_str(base_name);
                    name.into_boxed_str()
                };

                // intern the name, cache the symbol, and return
                let symbol = self.env.interner.intern(&name);
                self.canonical_term_names.insert(term, symbol);
                symbol
            }
        }
    }

    /// Extremely hacky helper method to get the argument to an `external.scheme` annotation.
    fn get_scheme_external(&self, attrs: &AttrSeq) -> Option<Symbol> {
        attrs.iter().find_map(|attr| {
            let lang = attr
                .name
                .as_ref()
                .ok()
                .and_then(|name| name.as_external_lang());

            if lang == Some(self.scheme_symbol) {
                let args = attr.args.as_ref();
                let (arg, tail) = args.split_first().unwrap();
                assert!(tail.is_empty());

                match arg.item() {
                    AttrArg::Name(_) => {
                        panic!("expected string argument for @external.scheme")
                    }
                    AttrArg::Literal(literal) => literal.as_string(),
                }
            } else {
                None
            }
        })
    }

    fn shape_of<V>(&mut self, ty: &ast::TyMatrix<V>) -> Shape {
        match ty {
            ast::TyMatrix::Prim(prim) => Shape::Prim(*prim),
            ast::TyMatrix::Var(_) => todo!(),
            ast::TyMatrix::Tuple(elems) => Shape::Struct { arity: elems.len() },
            ast::TyMatrix::Fn { domain, .. } => Shape::Fn {
                arity: domain.len(),
            },
            ast::TyMatrix::Named { name, args: _ } => {
                // NOTE: we could compute more efficient shapes in some cases if we took the
                // arguments into account, but it really isn't necessary for an MVP. instead, we
                // can generate shapes that work for any instance of the type.

                self.shape_of_named_type(*name)
            }
        }
    }

    fn shape_of_named_type(&mut self, name: TypeId) -> Shape {
        match self.named_type_shapes.get(&name) {
            Some(shape) => shape.clone(),
            None => {
                let shape = match &self.env.get_type(name).ast.kind {
                    ast::TypeKind::Alias { .. } => {
                        panic!(
                            "encountered unnormalized type alias while rendering"
                        )
                    }
                    ast::TypeKind::Extern => Shape::Extern { name },
                    ast::TypeKind::Adt { constrs, .. } => {
                        // first process all the constructors into their variant shapes
                        let variants: Box<[_]> = constrs
                            .keys()
                            .copied()
                            .map(|constr_name| ast::TyConstrIndex {
                                ty: name,
                                name: constr_name,
                            })
                            .map(|constr| self.variant_of_constr(constr))
                            .collect();

                        // now we look to find some particular shapes
                        match variants.as_ref() {
                            // named types cannot have zero constructors.
                            [] => panic!(
                                "encountered type with zero constructors"
                            ),
                            // single Ref constructor types are isomorphic to Ref.
                            [Variant::Ref] => Shape::MutBox,
                            // types with a single Cons constructor have an unbounded type, so we have to
                            // throw an error; ideally the user has already seen an error before we reach
                            // this point.
                            [Variant::Cons] => {
                                panic!(
                                    "tried to get the shape of an infinite type"
                                )
                            }
                            // general one-constructor types become structs.
                            [Variant::Plain { arity }] => {
                                Shape::Struct { arity: *arity }
                            }
                            // Cons + 1 types are isomorphic to List.
                            [Variant::Cons, Variant::Plain { arity: 0 }]
                            | [Variant::Plain { arity: 0 }, Variant::Cons] => {
                                Shape::List
                            }
                            // T + 1 types are isomorphic to Option.
                            [
                                Variant::Plain { arity: 1 },
                                Variant::Plain { arity: 0 },
                            ]
                            | [
                                Variant::Plain { arity: 0 },
                                Variant::Plain { arity: 1 },
                            ] => Shape::Option,
                            // otherwise just return the variants in a generic form.
                            _ => Shape::Variants(variants),
                        }
                    }
                };

                self.named_type_shapes.entry(name).or_insert(shape).clone()
            }
        }
    }

    /// Returns the discriminant associated with `constr` if it is not the only constructor of its
    /// type; that is, discriminants are only generated for types which require them.
    fn discriminant(&self, constr: TyConstrIndex) -> Option<Literal> {
        Some(Literal::Symbol(constr.name)).filter(|_| {
            self.env
                .get_type(constr.ty)
                .ast
                .constrs()
                .is_none_or(|constrs| constrs.len() != 1)
        })
    }

    fn variant_of_constr(&self, constr: TyConstrIndex) -> Variant {
        let def = self.get_constr(constr);

        match &def.kind {
            ast::TyConstrKind::Unit(_) => Variant::Plain { arity: 0 },
            ast::TyConstrKind::Record(fields) => match fields.len() {
                // check for the Ref variant shape
                1 => match &fields.values().next().unwrap().mutability {
                    Some(_) => Variant::Ref,
                    None => Variant::Plain { arity: 1 },
                },
                arity => Variant::Plain { arity },
            },
            ast::TyConstrKind::Tuple { elems, .. } => match elems.as_ref() {
                // check for the Cons variant shape
                [_, ty] => {
                    match self.constr_arg_is_recursive(constr.ty, &ty.matrix) {
                        true => Variant::Cons,
                        false => Variant::Plain { arity: 2 },
                    }
                }
                _ => Variant::Plain { arity: elems.len() },
            },
        }
    }

    /// Returns `true` iff `field_ty` is a recursive constructor argument of `ty`.
    ///
    /// For example, the second argument of `List.Cons` is such a recursive constructor argument,
    /// whereas its first argument is not. This is used to check for certain special type shapes
    /// that require special handling.
    fn constr_arg_is_recursive(
        &self,
        ty: TypeId,
        field_ty: &ast::TyMatrix<Uid>,
    ) -> bool {
        let params = &self.env.get_type(ty).ast.params;

        match field_ty {
            ast::TyMatrix::Named { name, args } if *name == ty => {
                // sanity check
                assert_eq!(params.len(), args.len());

                // check that every argument type matches every parameter type
                args.iter()
                    .zip(params)
                    .all(|(arg, param)| match arg.as_ref() {
                        ast::TyMatrix::Var(var) => *var == param.id,
                        _ => false,
                    })
            }
            _ => false,
        }
    }

    /// Returns an unused monotype ID.
    fn fresh_mono_ty_id(&mut self) -> MonoTyId {
        let id = self.next_mono_ty_id;
        self.next_mono_ty_id.increment();
        id
    }

    fn get_constr(
        &self,
        TyConstrIndex { ty, name }: TyConstrIndex,
    ) -> Spanned<&ast::TyConstr<Uid>> {
        self.env
            .get_type(ty)
            .ast
            .constrs()
            .and_then(|constrs| constrs.get(&name))
            .unwrap()
            .as_ref()
    }
}

type AttrSeq = [Spanned<
    Attr<Result<Spanned<AttrName>, Spanned<ast::NameContent>>, BoundResult>,
>];

fn collect_terms(env: &TypedEnv, module: ModId, terms: &mut Vec<TermId>) {
    let items = &env.get_module(module).items;

    for visp_item in items.values() {
        let (_, _, item) = visp_item.spread();

        match item {
            Res::Term(id) => terms.push(id),
            Res::Module(submodule) => collect_terms(env, submodule, terms),
            _ => continue,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        codegen::lower::Lowerer,
        cst::Parser,
        env::{
            import_res::ImportResEnv, resolve::resolve, typed::typecheck,
            unbound::UnboundEnv,
        },
        package as pkg,
    };
    use std::{path::PathBuf, str::FromStr};

    #[test]
    fn render_core() {
        // load package CSTs
        let path = PathBuf::from_str("../libs/core").unwrap();
        let package = pkg::Package::load_files(path).unwrap();
        let mut parser = Parser::new().unwrap();

        // lower CSTs to unbound_lowered::Ast
        let package = package
            .map_modules(|file| parser.parse(file))
            .transpose()
            .unwrap()
            .map_modules(crate::ast::unbound::Ast::try_from)
            .transpose()
            .unwrap()
            .map_modules(crate::ast::unbound_lowered::Ast::from);

        // build unbound env
        let mut env = UnboundEnv::new();
        let (_core_symbol, ingest_warnings, ingest_errors) =
            env.consume_package(package, Box::new([]));

        dbg!(ingest_warnings);
        dbg!(ingest_errors);

        // build import_res env
        let (env, errors) = ImportResEnv::from_unbound_env(env);
        dbg!(errors.len());

        let mut warnings = Vec::new();
        let mut errors = Vec::new();

        // build resolved env
        let env = resolve(env, &mut warnings, &mut errors);

        // lower to typed env
        let mut env = typecheck(env).unwrap();

        // lower core package
        let core_symbol = env.interner.intern_static("core");
        let mut lowerer = Lowerer::new(&mut env);
        let core_package = lowerer.lower_package(core_symbol);

        dbg![&core_package];
        panic!()
    }
}
