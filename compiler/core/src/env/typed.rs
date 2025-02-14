//! Implementation for lowering into a typed environment and then checking
//! and inferring types within it.
//!
//! # Phases
//! Typechecking is broken into two phases,
//! 1. _lowering_, and;
//! 2. _checking_.
//!
//! ## Lowering
//! The entrypoint for lowering is the [`lower`] function, which takes a
//! [`ResEnv`] and returns a [`TypedEnv`]. More precisely, the resulting
//! [`TypedEnv`] is incomplete: every expression, constant, and function has
//! been assigned a type, but the overall program is not necessarily well-typed
//! or even completely well-formed.
//!
//! Aside from this main task—assigning types to expressions—the lowering phase
//! is also responsible for further desugaring of the syntax tree. Most of this
//! can be seen in the definition of [`ast::Expr`], in which block expressions
//! are desugared as [`ast::Expr::LetIn`] sequences and if-else expressions are
//! converted into match statements of a boolean-typed scrutinee.
//!
//! When type annotations occur, they are reified into [`ast::Ty`] values by an
//! appropriate method of [`TyReifier`]. This information is used to infer the
//! types of function and constant declarations, as well as of let-bindings and
//! lambda parameters.
//!
//! ## Checking
//! `TODO: write about typechecking impl`

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use super::{
    resolve::{BoundResult, ResEnv},
    Env, Res,
};

use crate::{
    ast::{
        bound::{self, Bound},
        common::ViSp,
        typed::{self as ast, Typed},
    },
    env::{Term, Type},
    span::{Span, SpanBox, SpanSeq, Spanned},
    symbol::Symbol,
    unique::Uid,
};

pub type TypedEnv = Env<
    Spanned<ast::Term<BoundResult>>,
    Spanned<ast::Type<BoundResult>>,
    HashMap<Symbol, ViSp<Res>>,
>;

pub fn lower(
    Env {
        files,
        packages,
        modules,
        terms: untyped_terms,
        types: untyped_types,
        interner,
    }: ResEnv,
) -> (TypedEnv, Vec<ast::TyError>) {
    let types = {
        let mut types = Vec::with_capacity(untyped_types.len());

        for Type { name, module, ast } in untyped_types {
            let ast = lower_type(ast);
            types.push(Type { name, module, ast });
        }

        types
    };

    let mut errors = Vec::new();

    let terms = {
        let mut terms = Vec::with_capacity(untyped_terms.len());

        for Term { name, module, ast } in untyped_terms {
            let ast = lower_term(ast, &mut errors);
            terms.push(Term { name, module, ast });
        }

        terms
    };

    // TODO: check for public items which do not have concrete types
    // (that is, they contain unbound type variables) and emit errors

    (
        Env {
            files,
            packages,
            modules,
            terms,
            types,
            interner,
        },
        errors,
    )
}

fn lower_type(
    Spanned { item, span }: Spanned<bound::Type<BoundResult>>,
) -> Spanned<ast::Type<BoundResult>> {
    let (attrs, name, params, kind) = match item {
        bound::Type::Alias(bound::TypeAlias {
            attrs,
            name,
            params,
            ty,
        }) => (attrs, name, params, ast::TypeKind::Alias { rhs: ty }),
        bound::Type::Adt(bound::Adt {
            attrs,
            name,
            opacity,
            params,
            constructors,
        }) => (
            attrs,
            name,
            params,
            ast::TypeKind::Adt {
                opacity,
                constructors,
            },
        ),
        bound::Type::Extern(bound::ExternType {
            attrs,
            name,
            params,
        }) => (attrs, name, params, ast::TypeKind::Extern),
    };

    span.with(ast::Type {
        attrs,
        name,
        params,
        kind,
    })
}

fn lower_term(
    Spanned { item, span }: Spanned<bound::Term<BoundResult>>,
    errors: &mut Vec<ast::TyError>,
) -> Spanned<ast::Term<BoundResult>> {
    let (attrs, name, ty, kind) = match item {
        bound::Term::Fn(bound::Fn {
            attrs,
            name,
            params,
            return_ty,
            body,
        }) => (
            attrs,
            name,
            TyReifier::reify_fn_ty_annotation(
                params.clone(),
                return_ty.clone(),
                errors,
            ),
            ast::TermKind::Fn {
                params: lower_params(params),
                body: lower_expr(*body, errors),
                return_ty,
            },
        ),
        bound::Term::ExternFn(bound::ExternFn {
            attrs,
            name,
            params,
            return_ty,
        }) => (
            attrs,
            name,
            TyReifier::reify_fn_ty_annotation(
                params.clone(),
                return_ty.clone(),
                errors,
            ),
            ast::TermKind::ExternFn {
                params: lower_params(params),
                return_ty,
            },
        ),
        bound::Term::Const(bound::Const {
            attrs,
            name,
            ty,
            value,
        }) => (
            attrs,
            name,
            TyReifier::reify_option_ty(ty.clone(), errors),
            ast::TermKind::Const {
                ty_ast: ty,
                value: lower_expr(value, errors),
            },
        ),
    };

    span.with(ast::Term {
        attrs,
        name,
        ty,
        kind,
    })
}

fn lower_params(
    params: SpanSeq<bound::Parameter<BoundResult>>,
) -> SpanSeq<ast::Parameter<BoundResult>> {
    let mut new_params = Vec::with_capacity(params.len());

    for Spanned { item, span } in params {
        let param = ast::Parameter {
            pattern: item.pattern,
            ty_ast: item.ty,
        };

        new_params.push(span.with(param));
    }

    new_params.into_boxed_slice()
}

fn lower_expr(
    Spanned { item, span }: Spanned<bound::Expr<BoundResult>>,
    errors: &mut Vec<ast::TyError>,
) -> Spanned<Typed<ast::Expr<BoundResult>, BoundResult>> {
    span.with(match item {
        bound::Expr::Name(name) => {
            let ty = Arc::new(ast::Ty::fresh_unbound());
            ty.with(ast::Expr::Name(name))
        }
        bound::Expr::Literal(literal_expr) => {
            let matrix = match &literal_expr {
                ast::LiteralExpr::Unit => {
                    ast::TyMatrix::Prim(ast::PrimTy::Unit)
                }
                ast::LiteralExpr::Bool(_) => {
                    ast::TyMatrix::Prim(ast::PrimTy::Bool)
                }
                ast::LiteralExpr::Char(_) => {
                    ast::TyMatrix::Prim(ast::PrimTy::Char)
                }
                ast::LiteralExpr::String(_) => {
                    ast::TyMatrix::Prim(ast::PrimTy::String)
                }
                ast::LiteralExpr::Int(_) => {
                    ast::TyMatrix::Prim(ast::PrimTy::Int)
                }
                ast::LiteralExpr::Float(_) => {
                    ast::TyMatrix::Prim(ast::PrimTy::Float)
                }
                ast::LiteralExpr::Malformed(_) => ast::TyMatrix::Poison,
            };

            let ty = Arc::new(ast::Ty {
                vars: Default::default(),
                poisoned: matches!(matrix, ast::TyMatrix::Poison),
                matrix,
            });

            ty.with(ast::Expr::Literal(literal_expr))
        }
        bound::Expr::List(untyped_elems) => {
            // NOTE: we could get a more precise type here by threading the
            // TypeId of core.list.List through as a parameter of lower_expr,
            // but it's less awkward to do this later during full typechecking

            let mut elems = Vec::with_capacity(untyped_elems.len());

            for elem in untyped_elems {
                let elem = lower_expr(elem, errors);
                elems.push(elem);
            }

            let ty = Arc::new(ast::Ty::fresh_unbound());
            ty.with(ast::Expr::List(elems.into_boxed_slice()))
        }
        bound::Expr::Tuple(untyped_elems) => {
            let mut elems = Vec::with_capacity(untyped_elems.len());

            for elem in untyped_elems {
                let elem = lower_expr(elem, errors);
                elems.push(elem);
            }

            let ty = Arc::new(ast::Ty::fresh_unbound_tuple(elems.len()));
            ty.with(ast::Expr::Tuple(elems.into_boxed_slice()))
        }
        bound::Expr::Block(block) => lower_block_rec(
            block.statements.as_ref(),
            block.return_expr,
            errors,
        ),
        bound::Expr::RecordConstr {
            name,
            fields: untyped_fields,
            base,
        } => {
            let mut fields = Vec::with_capacity(untyped_fields.len());

            for Spanned {
                item: bound::RecordExprField { field, value },
                span,
            } in untyped_fields
            {
                let value = lower_expr(value, errors);
                let field = ast::RecordExprField { field, value };
                fields.push(span.with(field));
            }

            let fields = fields.into_boxed_slice();
            let base = base.map(|base| lower_expr(*base, errors)).map(Box::new);
            let ty = Arc::new(ast::Ty::fresh_unbound());
            ty.with(ast::Expr::RecordConstr { name, fields, base })
        }
        bound::Expr::RecordField { item, field } => {
            let item = Box::new(lower_expr(*item, errors));
            let ty = Arc::new(ast::Ty::fresh_unbound());
            ty.with(ast::Expr::RecordField { item, field })
        }
        bound::Expr::TupleField { item, field } => {
            let item = Box::new(lower_expr(*item, errors));
            let ty = Arc::new(ast::Ty::fresh_unbound());
            ty.with(ast::Expr::TupleField { item, field })
        }
        bound::Expr::Lambda { params, body } => {
            let annotation =
                TyReifier::reify_fn_ty_annotation(params.clone(), None, errors);
            let params = lower_params(params);
            let body = Box::new(lower_expr(*body, errors));

            let ty = Arc::new(ast::Ty::fresh_unbound_fn(params.len()));
            ty.with(ast::Expr::Lambda {
                annotation,
                params,
                body,
            })
        }
        bound::Expr::Call { callee, args, kind } => {
            let callee = Box::new(lower_expr(*callee, errors));

            let args = {
                let mut typed_args = Vec::with_capacity(args.len());

                for arg in args {
                    let arg = lower_expr(arg, errors);
                    typed_args.push(arg);
                }

                typed_args.into_boxed_slice()
            };

            let ty = Arc::new(ast::Ty::fresh_unbound());
            ty.with(ast::Expr::Call { callee, args, kind })
        }
        bound::Expr::LazyAnd { operator, lhs, rhs } => {
            let operator = operator.with(ast::BuiltinOperator::LazyAnd);
            let lhs = Box::new(lower_expr(*lhs, errors));
            let rhs = Box::new(lower_expr(*rhs, errors));

            let ty = Arc::new(ast::Ty::prim(ast::PrimTy::Bool));
            ty.with(ast::Expr::Builtin { operator, lhs, rhs })
        }
        bound::Expr::LazyOr { operator, lhs, rhs } => {
            let operator = operator.with(ast::BuiltinOperator::LazyOr);
            let lhs = Box::new(lower_expr(*lhs, errors));
            let rhs = Box::new(lower_expr(*rhs, errors));

            let ty = Arc::new(ast::Ty::prim(ast::PrimTy::Bool));
            ty.with(ast::Expr::Builtin { operator, lhs, rhs })
        }
        bound::Expr::Mutate { operator, lhs, rhs } => {
            let operator = operator.with(ast::BuiltinOperator::Mutate);
            let lhs = Box::new(lower_expr(*lhs, errors));
            let rhs = Box::new(lower_expr(*rhs, errors));

            let ty = Arc::new(ast::Ty::prim(ast::PrimTy::Unit));
            ty.with(ast::Expr::Builtin { operator, lhs, rhs })
        }
        bound::Expr::Match {
            scrutinee,
            arms: untyped_arms,
        } => {
            let mut arms = Vec::with_capacity(untyped_arms.len());

            for Spanned {
                item: bound::MatchArm { pattern, body },
                span,
            } in untyped_arms
            {
                let body = lower_expr(body, errors);
                let arm = ast::MatchArm { pattern, body };
                arms.push(span.with(arm));
            }

            let scrutinee = Box::new(lower_expr(*scrutinee, errors));
            let arms = arms.into_boxed_slice();
            let ty = Arc::new(ast::Ty::fresh_unbound());
            ty.with(ast::Expr::Match { scrutinee, arms })
        }
        bound::Expr::IfElse {
            condition,
            consequence,
            alternative,
        } => {
            let consequence = consequence.span.with(ast::MatchArm {
                pattern: consequence
                    .span
                    .with(ast::Pattern::Literal(ast::LiteralExpr::Bool(true))),
                body: consequence.span.with(lower_block_rec(
                    consequence.statements.as_ref(),
                    consequence.return_expr.clone(),
                    errors,
                )),
            });

            let alternative_span = alternative
                .as_deref()
                .map(Spanned::span)
                .unwrap_or(Span::ZERO);

            let alternative = alternative_span.with(ast::MatchArm {
                pattern: alternative_span
                    .with(ast::Pattern::Literal(ast::LiteralExpr::Bool(false))),
                body: alternative_span.with(
                    alternative
                        .map(|b| {
                            lower_block_rec(
                                b.statements.as_ref(),
                                b.return_expr.clone(),
                                errors,
                            )
                        })
                        .unwrap_or_else(generate_unit_expr),
                ),
            });

            let scrutinee = Box::new(lower_expr(*condition, errors));
            let arms = std::iter::once(consequence)
                .chain(std::iter::once(alternative))
                .collect::<Box<[_]>>();

            let ty = Arc::new(ast::Ty::fresh_unbound());
            ty.with(ast::Expr::Match { scrutinee, arms })
        }
    })
}

fn generate_unit_expr() -> Typed<ast::Expr<BoundResult>, BoundResult> {
    let ty = Arc::new(ast::Ty::prim(ast::PrimTy::Unit));
    ty.with(ast::Expr::Literal(ast::LiteralExpr::Unit))
}

fn lower_block_rec(
    stmts: &[Spanned<bound::Stmt<BoundResult>>],
    body: Option<SpanBox<bound::Expr<BoundResult>>>,
    errors: &mut Vec<ast::TyError>,
) -> Typed<ast::Expr<BoundResult>, BoundResult> {
    match stmts {
        [] => match body {
            Some(expr) => lower_expr(*expr, errors).item,
            None => {
                let ty = Arc::new(ast::Ty::prim(ast::PrimTy::Unit));
                ty.with(ast::Expr::Literal(ast::LiteralExpr::Unit))
            }
        },
        [Spanned { item, span }, tail @ ..] => match item {
            bound::Stmt::Empty => lower_block_rec(tail, body, errors),
            bound::Stmt::Expr(expr) => {
                let lhs = None;
                let rhs = Box::new(lower_expr(span.with(expr.clone()), errors));
                let body = Box::new(lower_block_rec(tail, body, errors));

                let ty = body.ty.clone();
                ty.with(ast::Expr::LetIn { lhs, rhs, body })
            }
            bound::Stmt::Let { pattern, ty, value } => {
                let lhs = Some(ast::LetStmtLhs {
                    pattern: pattern.clone(),
                    ty_ast: ty.clone(),
                });
                let rhs = Box::new(lower_expr(value.clone(), errors));
                let body = Box::new(lower_block_rec(tail, body, errors));

                let ty = body.ty.clone();
                ty.with(ast::Expr::LetIn { lhs, rhs, body })
            }
        },
    }
}

/// A tree visitor for converting type ASTs into well-formed types.
#[derive(Debug, Clone, Default)]
struct TyReifier {
    vars: Vec<Uid>,
    errors: Vec<ast::TyError>,
    poisoned: bool,
}

impl TyReifier {
    fn reify_option_ty(
        ast: Option<Spanned<ast::TyAst<BoundResult>>>,
        errors: &mut Vec<ast::TyError>,
    ) -> ast::Ty {
        let mut reifier = TyReifier::default();
        let matrix = reifier.reify_option_matrix(ast);
        reifier.quantify_matrix(matrix, errors)
    }

    fn reify_fn_ty_annotation(
        parameters: SpanSeq<bound::Parameter<BoundResult>>,
        return_ty: Option<Spanned<ast::TyAst<BoundResult>>>,
        errors: &mut Vec<ast::TyError>,
    ) -> ast::Ty {
        let mut reifier = TyReifier::default();

        let domain: Box<[ast::TyMatrix]> = {
            let mut tys = Vec::with_capacity(parameters.len());

            for param in parameters {
                let ty = reifier.reify_option_matrix(param.item.ty);
                tys.push(ty);
            }

            tys.into_boxed_slice()
        };

        let codomain = Box::new(reifier.reify_option_matrix(return_ty));
        let matrix = ast::TyMatrix::Fn { domain, codomain };
        reifier.quantify_matrix(matrix, errors)
    }

    /// Consume self and an [`ast::TyMatrix`] to yield an [`ast::Ty`].
    fn quantify_matrix(
        mut self,
        matrix: ast::TyMatrix,
        errors: &mut Vec<ast::TyError>,
    ) -> ast::Ty {
        // move errors into the passed buffer
        errors.append(&mut self.errors);

        ast::Ty {
            vars: self.vars.into_iter().collect::<HashSet<_>>(),
            poisoned: self.poisoned,
            matrix,
        }
    }

    fn reify_option_matrix(
        &mut self,
        matrix: Option<Spanned<ast::TyAst<BoundResult>>>,
    ) -> ast::TyMatrix {
        match matrix {
            Some(ast) => self.reify_matrix(ast),
            None => self.fresh_var(),
        }
    }

    fn reify_matrix(
        &mut self,
        Spanned { span, item }: Spanned<ast::TyAst<BoundResult>>,
    ) -> ast::TyMatrix {
        match item {
            bound::Ty::Infer => self.fresh_var(),
            bound::Ty::Never => ast::TyMatrix::Prim(ast::PrimTy::Never),
            bound::Ty::Unit => ast::TyMatrix::Prim(ast::PrimTy::Unit),
            bound::Ty::Bool => ast::TyMatrix::Prim(ast::PrimTy::Bool),
            bound::Ty::Char => ast::TyMatrix::Prim(ast::PrimTy::Char),
            bound::Ty::String => ast::TyMatrix::Prim(ast::PrimTy::String),
            bound::Ty::Int => ast::TyMatrix::Prim(ast::PrimTy::Int),
            bound::Ty::Float => ast::TyMatrix::Prim(ast::PrimTy::Float),
            bound::Ty::Tuple(elem_asts) => {
                let elems = {
                    let mut elems = Vec::with_capacity(elem_asts.len());

                    for ast in elem_asts {
                        elems.push(self.reify_matrix(ast));
                    }

                    elems.into_boxed_slice()
                };

                ast::TyMatrix::Tuple(elems)
            }
            bound::Ty::Named {
                name: Err(name), ..
            } => {
                let error = ast::TyError::NoSuchName { name, span };
                self.errors.push(error);
                self.poisoned = true;
                ast::TyMatrix::Poison
            }
            bound::Ty::Named {
                name: Ok(name),
                args,
            } => {
                match name {
                    // error case: ∀T, U. T[U]
                    Bound::Local(name) if !args.is_empty() => {
                        let error = ast::TyError::TyVarWithArgs { name, span };
                        self.errors.push(error);
                        self.poisoned = true;
                        ast::TyMatrix::Poison
                    }
                    Bound::Local(name) => {
                        self.vars.push(name.id);
                        ast::TyMatrix::Var(name.id)
                    }
                    name => {
                        let args = {
                            let mut new_args = Vec::with_capacity(args.len());

                            for arg in args {
                                new_args.push(self.reify_matrix(arg));
                            }

                            new_args.into_boxed_slice()
                        };

                        let name = name
                            .as_res()
                            .unwrap()
                            .as_type()
                            .expect("definitely referenced by TypeId");

                        ast::TyMatrix::Adt { name, args }
                    }
                }
            }
            bound::Ty::Fn { domain, codomain } => {
                let domain = {
                    let mut dom = Vec::with_capacity(domain.len());

                    for ast in domain.item {
                        dom.push(self.reify_matrix(ast));
                    }

                    dom.into_boxed_slice()
                };

                let codomain = Box::new(self.reify_matrix(*codomain));

                ast::TyMatrix::Fn { domain, codomain }
            }
        }
    }

    fn fresh_var(&mut self) -> ast::TyMatrix {
        let uid = Uid::fresh();
        self.vars.push(uid);
        ast::TyMatrix::Var(uid)
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        cst::Parser,
        env::{
            import_res::ImportResEnv, resolve::resolve, unbound::UnboundEnv,
        },
        package as pkg,
    };
    use std::{path::PathBuf, str::FromStr};

    #[test]
    fn build_lowered_env_from_core() {
        // load package CSTs
        let path = PathBuf::from_str("../../libs/core").unwrap();
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
        let (mut env, ty_errors) = super::lower(env);

        // REF MODULE INSPECTION

        let ref_ = env.interner.intern_static("ref");
        let ref_mod_id = env.magic_core_submodule(ref_).unwrap();
        let ref_mod = env.get_module(ref_mod_id);

        for (sym, item) in ref_mod.items.clone() {
            let name = env.interner.resolve(sym).unwrap();
            let (_vis, _span, res) = item.spread();

            let res_value = env.get_res(res);

            eprintln!("{} ({:?})\n{:?}\n\n", name, res, res_value);
        }

        dbg![ty_errors.len()];
        panic!()
    }
}
