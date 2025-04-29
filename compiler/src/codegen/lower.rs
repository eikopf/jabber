//! Primary lowering implementation.

use std::{
    collections::{HashMap, HashSet},
    io::Write,
};

use crate::{
    ast::{
        attr::{Attr, AttrArg, AttrName},
        common::Vis,
        typed::{self as ast, TyConstrIndex},
    },
    codegen::{ToDoc, blame::Blame, scm::MatchArm},
    env::{
        ModId, Package, Res, Term, TermId, TypeId,
        resolve::BoundResult,
        typed::{TyVar, TypedEnv},
    },
    package::metadata::PackageKind,
    span::Spanned,
    symbol::{StringInterner, Symbol},
    unique::Uid,
};

use super::{
    blame::Blamed,
    repr::{Shape, Variant},
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
    pub kind: PackageKind,
    pub imports: Vec<Symbol>,
    pub exports: Vec<Symbol>,
    pub externals: Vec<Def<Symbol>>,
    pub constrs: Vec<Def<Blamed<Expr>>>,
    pub functions: Vec<Def<Blamed<Expr>>>,
    pub constants: Vec<Def<Blamed<Expr>>>,
}

impl LoweredPackage {
    pub fn new(name: Symbol, kind: PackageKind) -> Self {
        Self {
            name,
            kind,
            imports: Default::default(),
            exports: Default::default(),
            externals: Default::default(),
            constrs: Default::default(),
            functions: Default::default(),
            constants: Default::default(),
        }
    }

    pub fn write<W>(
        self,
        w: &mut W,
        interner: &mut StringInterner,
    ) -> std::io::Result<()>
    where
        W: Write,
    {
        writeln!(w, "#!r6rs")?;
        write!(w, "{}", self.to_doc(interner).pretty(80))
    }
}

#[derive(Debug)]
pub struct Lowerer<'a> {
    /// The typechecked environment.
    pub(crate) env: &'a mut TypedEnv,
    /// The canonical names for each term.
    canonical_term_names: HashMap<TermId, Symbol>,
    /// The canonical names for each type constructor.
    canonical_constr_names: HashMap<TyConstrIndex, Symbol>,
    /// The cached per-type shapes.
    named_type_shapes: HashMap<TypeId, Shape>,
    /// The type constructor definitions generated while lowering.
    type_constr_definitions: HashMap<TyConstrIndex, Def<Blamed<Expr>>>,
    /// The canonical orderings of the fields of record constructors.
    field_orders: HashMap<TyConstrIndex, Box<[Symbol]>>,
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
            field_orders: Default::default(),
            scheme_symbol,
        }
    }

    pub fn lower_package(
        &mut self,
        package: Symbol,
        kind: PackageKind,
    ) -> LoweredPackage {
        let Package {
            root_module,
            version: _,
            dependencies,
        } = self.env.get_package(package);

        // create an empty lowered package
        let mut lowered_package = LoweredPackage::new(package, kind);

        // add dependencies
        lowered_package.imports.extend_from_slice(dependencies);

        // accumulate the IDs for the terms in the package
        let terms = {
            let mut terms = HashSet::new();
            collect_terms(self.env, *root_module, &mut terms);

            // remove imported terms
            terms.retain(|&term| {
                let module = self.env.get_term(term).module;
                let owning_package = self.env.get_module(module).package;
                owning_package == package
            });

            terms
        };

        // lower the terms in any order, writing the results to lowered_package
        for term_id in terms {
            // HACK: evil unnecessary clone!!!
            let Term { module, ast, .. } = self.env.get_term(term_id).clone();
            let file = self.env.get_module(module).file;

            let blame = Blame {
                file,
                span: ast.span(),
            };

            // if the term is public in the package, export it
            if self.res_is_exported(Res::Term(term_id)) {
                let name = self.get_canonical_name(term_id);
                lowered_package.exports.push(name);
            }

            let term = ast.item();
            self.lower_term(term_id, &mut lowered_package, blame, module, term);
        }

        let constr_ids = self
            .type_constr_definitions
            .keys()
            .copied()
            .collect::<Vec<_>>();

        // run over the type constructors to find public exports
        for constr in constr_ids {
            if self.res_is_exported(Res::TyConstr {
                ty: constr.ty,
                name: constr.name,
            }) {
                let name = self.get_type_constr_name(constr);
                lowered_package.exports.push(name);
            }
        }

        // dump type constructor definitions into the package
        let constrs = self.type_constr_definitions.drain();
        lowered_package.constrs.extend(constrs.map(|(_, def)| def));

        // return the package
        lowered_package
    }

    fn res_is_exported(&self, res: Res) -> bool {
        match res {
            Res::Term(term_id) => {
                let term = self.env.get_term(term_id);
                let module = self.env.get_module(term.module);

                module.items.get(&term.name).is_some_and(Vis::is_visible)
                    && self.res_is_exported(Res::Module(term.module))
            }
            Res::Type(type_id) | Res::StructType(type_id) => {
                let type_ = self.env.get_type(type_id);
                let module = self.env.get_module(type_.module);

                module.items.get(&type_.name).is_some_and(Vis::is_visible)
                    && self.res_is_exported(Res::Module(type_.module))
            }
            Res::TyConstr { ty, name: _ } => {
                let type_ = self.env.get_type(ty);

                match &type_.ast.kind {
                    ast::TypeKind::Adt { opacity, .. } => {
                        opacity.is_none() && self.res_is_exported(Res::Type(ty))
                    }
                    _ => unreachable!(),
                }
            }
            Res::Module(mod_id) => {
                let mod_ = self.env.get_module(mod_id);

                // a module is exported if it is the root module, or if it is
                // public in its parent and its parent is exported
                match mod_.parent {
                    None => true,
                    Some(parent) => {
                        self.env
                            .get_module(parent)
                            .items
                            .get(&mod_.name)
                            .is_some_and(Vis::is_visible)
                            && self.res_is_exported(Res::Module(parent))
                    }
                }
            }
        }
    }

    pub fn lower_term(
        &mut self,
        id: TermId,
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
            let content = self.get_canonical_name(id);

            blame.with(content)
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
                let value = self.lower_expr(value.item().as_ref());

                let def = Def {
                    module,
                    name,
                    value: blame.with(value),
                };

                package.constants.push(def);
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
            .collect::<Box<_>>();

        let patterns = match patterns.len() {
            0 => vec![Pattern::Wildcard].into_boxed_slice(),
            _ => patterns,
        };

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
            } => {
                let body = Box::new(match return_expr.as_ref() {
                    Some(expr) => self.lower_expr(expr.item().as_ref()),
                    None => call!(Expr::Builtin(Builtin::Void)),
                });

                let bindings = statements
                    .iter()
                    .map(Spanned::item)
                    .map(|stmt| match stmt {
                        ast::Stmt::Expr(expr) => {
                            let rhs = self.lower_expr(expr.as_ref());
                            (Pattern::Wildcard, rhs)
                        }
                        ast::Stmt::Let { pattern, value } => {
                            let pattern = self.lower_pattern(pattern.item());
                            let rhs = self.lower_expr(value.item().as_ref());
                            (pattern, rhs)
                        }
                    })
                    .collect();

                Expr::MatchLetSeq { bindings, body }
            }
            ast::Expr::RecordConstr { name, fields, base } => {
                // get constr ID
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

                // collect some metadata
                let base_name = self.env.interner.intern_static("BASE*");
                let discriminant = self.discriminant(constr);
                let index_start = if discriminant.is_some() { 1 } else { 0 };
                let field_order = Box::from_iter(
                    self.get_field_ordering(constr).iter().copied(),
                );

                // determine the builtin constructor function for this type
                let builtin_constr =
                    Expr::Builtin(match self.shape_of_named_type(constr.ty) {
                        Shape::Prim(..)
                        | Shape::List
                        | Shape::Option
                        | Shape::Extern { .. }
                        | Shape::Fn { .. } => unreachable!(),
                        Shape::MutBox => Builtin::Box,
                        Shape::Struct { .. } | Shape::Variants(..) => {
                            Builtin::Vector
                        }
                    });

                // convert field list into a symbol -> expr map
                let fields = fields
                    .iter()
                    .map(|field| {
                        let name = field.field.item;
                        let value = field.value.item();
                        (name, value)
                    })
                    .collect::<HashMap<_, _>>();

                // lower each field, using `(vector-ref BASE* <index>)` if the
                // field does not occur in the field initializer list
                let field_exprs =
                    field_order.iter().copied().zip(index_start..).map(
                        |(name, index)| match fields.get(&name) {
                            Some(expr) => self.lower_expr(expr.as_ref()),
                            None => call!(
                                Expr::Builtin(Builtin::VectorRef),
                                Expr::Symbol(base_name),
                                Expr::Literal(Literal::UInt(index))
                            ),
                        },
                    );

                // prepend the discriminant (if any) to the list of expressions
                let exprs = discriminant
                    .map(Expr::Literal)
                    .into_iter()
                    .chain(field_exprs);

                // create the constructor expression
                let constr = call!(builtin_constr; Vec::from_iter(exprs));

                // if there is a base expr, wrap the constructor in a let form
                match base.as_ref() {
                    Some(base) => {
                        let base_expr = self.lower_expr(base.item().as_ref());
                        Expr::Let {
                            bindings: vec![(base_name, base_expr)].into(),
                            body: Box::new(constr),
                        }
                    }
                    None => constr,
                }
            }
            ast::Expr::RecordField { item, field } => {
                // NOTE: record field expressions can only occur when the
                // item is a struct record type

                let constr = match item.ty.matrix.as_ref() {
                    ast::TyMatrix::Named { name, .. } => {
                        let constr_name = self.env.get_type(*name).name;
                        TyConstrIndex {
                            ty: *name,
                            name: constr_name,
                        }
                    }
                    _ => unreachable!(),
                };

                let item = self.lower_expr(item.item().as_ref());

                match self.shape_of_named_type(constr.ty) {
                    Shape::MutBox => {
                        call!(Expr::Builtin(Builtin::Unbox), item)
                    }
                    Shape::Struct { .. } | Shape::Variants(..) => {
                        let index_start = match self.discriminant(constr) {
                            Some(_) => 1,
                            None => 0,
                        };

                        let raw_index = index_start
                            + self
                                .get_field_ordering(constr)
                                .iter()
                                .position(|f| f == field.item())
                                .unwrap();

                        let index =
                            Expr::Literal(Literal::UInt(raw_index as u64));
                        call!(Expr::Builtin(Builtin::VectorRef), item, index)
                    }
                    _ => unreachable!(),
                }
            }
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
            } => {
                // we need to get the Shape of `item`, where
                // - if the shape is MutBox then we use `set-box!`;
                // - otherwise we use `vector-set!`.

                let ty = &item.ty;
                let shape = self.shape_of(&ty.matrix);
                let item = self.lower_expr(item.item().as_ref());

                match shape {
                    Shape::Prim(_)
                    | Shape::List
                    | Shape::Option
                    | Shape::Extern { .. }
                    | Shape::Fn { .. } => unreachable!(),
                    Shape::MutBox => {
                        let rhs = self.lower_expr(rhs.item().as_ref());
                        call!(Expr::Builtin(Builtin::SetBox), item, rhs)
                    }
                    Shape::Struct { .. } | Shape::Variants(..) => {
                        let ty_name = match ty.matrix.as_ref() {
                            ast::TyMatrix::Named { name, args: _ } => *name,
                            _ => unreachable!(),
                        };

                        let constr = TyConstrIndex {
                            ty: ty_name,
                            name: field.item,
                        };

                        let field_order = self.get_field_ordering(constr);
                        let index = field_order
                            .iter()
                            .position(|name| name == field.item())
                            .map(|i| Expr::Literal(Literal::UInt(i as u64)))
                            .unwrap();

                        call!(Expr::Builtin(Builtin::VectorSet), item, index)
                    }
                }
            }
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
            ast::Pattern::RecordConstr { name, fields, .. } => {
                let shape = self.shape_of_named_type(name.id.ty);

                match shape {
                    Shape::Prim(_)
                    | Shape::List
                    | Shape::Option
                    | Shape::Extern { .. }
                    | Shape::Fn { .. } => unreachable!(),
                    Shape::MutBox => match fields.len() {
                        0 => Pattern::Box(Box::new(Pattern::Wildcard)),
                        1 => {
                            let field = fields[0].item();
                            let pattern = self.lower_pattern(&field.pattern);
                            Pattern::Box(Box::new(pattern))
                        }
                        _ => unreachable!(),
                    },
                    Shape::Struct { .. } | Shape::Variants(..) => {
                        let fields = fields
                            .iter()
                            .map(|field| {
                                let name = field.name;
                                let pattern =
                                    self.lower_pattern(field.pattern.item());

                                (name, pattern)
                            })
                            .collect::<HashMap<_, _>>();

                        let prefix =
                            self.discriminant(name.id).map(Pattern::Literal);
                        let field_order = self.get_field_ordering(name.id);

                        let field_pats = field_order.iter().copied().map(
                            |field| match fields.get(&field) {
                                // HACK: this clone should be avoided!!!
                                Some(pattern) => pattern.clone(),
                                None => Pattern::Wildcard,
                            },
                        );

                        let subpats = prefix.into_iter().chain(field_pats);
                        Pattern::Vector(subpats.collect())
                    }
                }
            }
        }
    }

    /// Returns the canonical ordering among the fields of the given `constr`.
    fn get_field_ordering(&mut self, constr: TyConstrIndex) -> &[Symbol] {
        #[allow(clippy::map_entry)]
        if !self.field_orders.contains_key(&constr) {
            match &self.get_constr(constr).kind {
                ast::TyConstrKind::Unit(_)
                | ast::TyConstrKind::Tuple { .. } => panic!(
                    "tried to compute the field ordering of a non-record constructor"
                ),
                ast::TyConstrKind::Record(fields) => {
                    let mut names: Vec<_> = fields.keys().copied().collect();
                    names.sort_unstable();
                    self.field_orders.insert(constr, names.into_boxed_slice());
                }
            }
        }

        self.field_orders.get(&constr).unwrap()
    }

    /// Returns the symbol corresponding to the given type constructor
    /// function definition, generating and memoizing its declaration if it has
    /// not already been generated.
    fn get_type_constr_name(&mut self, constr: TyConstrIndex) -> Symbol {
        match self.canonical_constr_names.get(&constr) {
            Some(name) => *name,
            None => {
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

                // get the term's base name
                let base_symbol = self.env.get_term(term).name;
                let base_name = self.env.interner.resolve(base_symbol).unwrap();

                // resolve module names
                let prefix_components = module_path.iter().map(|&module| {
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

fn collect_terms(env: &TypedEnv, module: ModId, terms: &mut HashSet<TermId>) {
    let items = &env.get_module(module).items;

    for visp_item in items.values() {
        let (_, _, item) = visp_item.spread();

        match item {
            Res::Term(id) => {
                terms.insert(id);
            }
            Res::Module(submodule) => collect_terms(env, submodule, terms),
            _ => continue,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        codegen::{ToDoc, lower::Lowerer},
        cst::Parser,
        env::{
            import_res::ImportResEnv, resolve::resolve, typed::typecheck,
            unbound::UnboundEnv,
        },
        package::{self as pkg, metadata::PackageKind},
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
        let core_package =
            lowerer.lower_package(core_symbol, PackageKind::Library);

        eprintln!("{}", core_package.to_doc(&mut env.interner).pretty(80));
        panic!()
    }
}
