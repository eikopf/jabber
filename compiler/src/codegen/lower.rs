//! Primary lowering implementation.

use std::collections::HashMap;

use crate::{
    ast::{
        attr::{Attr, AttrArg, AttrName},
        typed as ast,
    },
    codegen::blame::Blame,
    env::{
        FileId, ModId, Package, Res, Term, TermId,
        resolve::BoundResult,
        typed::{TyVar, TypedEnv},
    },
    span::{SpanSeq, Spanned},
    symbol::Symbol,
};

use super::{
    blame::Blamed,
    repr::{MonoTyId, Shape},
    scm::{Builtin, Expr, Literal},
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
    pub functions: Vec<Def<Blamed<Expr>>>,
    pub constants: Vec<Def<Blamed<Expr>>>,
}

impl LoweredPackage {
    pub fn new(name: Symbol, root_file: FileId) -> Self {
        Self {
            name,
            root_file,
            externals: Default::default(),
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
    canonical_names: HashMap<TermId, Symbol>,
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
            canonical_names: Default::default(),
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
            ty,
            kind,
        }: &ast::Term<TyVar>,
    ) {
        match kind {
            ast::TermKind::ExternFn { .. } => {
                let binding = self
                    .get_scheme_external(attrs)
                    .expect("missing scheme external for extern function");

                let def = Def {
                    module,
                    name: blame.with(name.content.item),
                    value: binding,
                };

                package.externals.push(def);
            }
            ast::TermKind::Fn { params, body, .. } => {
                let body = self.lower_expr(body.item().as_ref());

                todo!()
            }
            ast::TermKind::Const { value, .. } => todo!(),
        }
    }

    fn lower_expr(
        &mut self,
        ast::Typed { item, ty }: ast::Typed<&ast::Expr<TyVar>, TyVar>,
    ) -> Expr {
        match item {
            ast::Expr::Local(name) => Expr::Symbol(name.content.item),
            ast::Expr::Global(ast::Name { id, .. }) => match *id {
                Res::Term(term) => Expr::Symbol(self.get_canonical_name(term)),
                Res::TyConstr { ty, name } => {
                    // TODO: figure out how to render type constructors
                    todo!()
                }
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
            // TODO: these two expressions require a stable field -> index mapping
            ast::Expr::RecordConstr { name, fields, base } => todo!(),
            ast::Expr::RecordField { item, field } => todo!(),
            ast::Expr::TupleField { item, field } => {
                let vector_ref = Expr::Builtin(Builtin::VectorRef);
                let item = self.lower_expr(item.item().as_ref());
                let field = Expr::Literal(Literal::UInt(field.item as u64));

                call!(vector_ref, item, field)
            }
            ast::Expr::Lambda { params, body } => todo!(),
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
            ast::Expr::Match { scrutinee, arms } => todo!(),
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

    fn get_canonical_name(&mut self, term: TermId) -> Symbol {
        match self.canonical_names.get(&term) {
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
                self.canonical_names.insert(term, symbol);
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

    fn shape_of(&mut self, ty: ast::TyMatrix<TyVar>) -> Shape {
        todo!()
    }

    /// Returns an unused monotype ID.
    fn fresh_mono_ty_id(&mut self) -> MonoTyId {
        let id = self.next_mono_ty_id;
        self.next_mono_ty_id.increment();
        id
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
