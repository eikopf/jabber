//! Concrete syntax trees parsed using Tree-sitter.

pub(crate) mod nodes {
    include!(concat!(env!("OUT_DIR"), "/nodes.rs"));
}

pub(crate) mod queries {
    include!(concat!(env!("OUT_DIR"), "/queries.rs"));
}

use crate::{
    ast::unbound as ast,
    file::File,
    span::{Span, SpanSeq, Spanned},
};

use nodes::{
    anon_unions::TypeExpr_FnTypeArgs, FnType, GenericType, Ident, Name, Path,
    PrimitiveType, SourceFile, TupleType, TypeExpr,
};

use thiserror::Error;
use type_sitter::{raw, IncorrectKind, Node, Tree};

pub struct Parser(type_sitter::Parser<SourceFile<'static>>);

#[derive(Debug, Clone, Copy, Error)]
#[error("Failed to parse {0}, probably because the parser timed out.")]
pub struct CstParseError<'a>(&'a std::path::Path);

impl Parser {
    pub fn new() -> Result<Self, raw::LanguageError> {
        type_sitter::Parser::new(&raw::Language::new(
            tree_sitter_jabber::LANGUAGE,
        ))
        .map(Self)
    }

    pub fn parse<'a>(
        &'a mut self,
        file: &'a File,
    ) -> Result<Cst, CstParseError<'a>> {
        self.0
            .parse(file.contents(), None)
            .map(|tree| Cst { tree, file })
            .map_err(|()| CstParseError(file.path()))
    }
}

pub struct Cst<'a> {
    tree: Tree<SourceFile<'static>>,
    file: &'a File,
}

pub enum ParseError {
    Error { parent_kind: &'static str },
    Missing { parent_kind: &'static str },
}

impl<'a> Cst<'a> {
    pub fn build_ast(self) -> Result<ast::Ast<'a>, ParseError> {
        // TODO: walk the raw tree for error/missing nodes and emit
        // appropriate ParseErrors if they exist

        let visitor = &self.visitor();
        let Cst { tree, file } = self;
        let root = tree.root_node().unwrap();
        let (shebang, module_comment, comments, decls) =
            visitor.visit_source_file(root).unwrap();

        Ok(ast::Ast::new(
            file,
            shebang,
            module_comment,
            comments,
            decls,
        ))
    }

    fn visitor(&self) -> CstVisitor<'a> {
        CstVisitor {
            source: self.file.contents(),
        }
    }
}

struct CstVisitor<'a> {
    source: &'a str,
}

type CstResult<'a, T> = Result<T, IncorrectKind<'a>>;

/// The owned components of an [`ast::Ast`]. The first element is taken
/// to be the `shebang` field, and the second is taken as the `module_comment`
/// field.
type AstComponents =
    (Option<Span>, Option<Span>, Box<[Span]>, SpanSeq<ast::Decl>);

impl<'a> CstVisitor<'a> {
    fn visit_source_file(
        &self,
        node: SourceFile<'a>,
    ) -> CstResult<'a, AstComponents> {
        todo!()
    }

    // TYPES

    fn visit_type(
        &self,
        node: TypeExpr<'a>,
    ) -> CstResult<'a, Spanned<ast::Ty>> {
        let span = node_span(node);

        match node {
            TypeExpr::Name(name) => self
                .visit_name(name)
                .map(ast::Ty::Name)
                .map(|node| span.with(node)),
            TypeExpr::FnType(fn_type) => self.visit_fn_type(fn_type),
            TypeExpr::GenericType(generic_type) => {
                self.visit_generic_type(generic_type)
            }
            TypeExpr::InferredType(_) => Ok(span.with(ast::Ty::Infer)),
            TypeExpr::ParenthesizedType(paren_type) => self
                .visit_type(paren_type.inner()?)
                .map(Box::new)
                .map(ast::Ty::Paren)
                .map(|ty| span.with(ty)),
            TypeExpr::PrimitiveType(primitive_type) => self
                .visit_prim_type(primitive_type)
                .map(ast::Ty::Prim)
                .map(|prim| span.with(prim)),
            TypeExpr::TupleType(tuple_type) => self
                .visit_tuple_type(tuple_type)
                .map(ast::Ty::Tuple)
                .map(|tup| span.with(tup)),
            TypeExpr::UnitType(_) => {
                Ok(ast::Ty::Prim(ast::PrimTy::Unit)).map(|ty| span.with(ty))
            }
        }
    }

    fn visit_prim_type(
        &self,
        node: PrimitiveType<'a>,
    ) -> CstResult<'a, ast::PrimTy> {
        let prim = match node.utf8_text(self.source.as_bytes()).unwrap() {
            "!" => ast::PrimTy::Never,
            // we don't include () here because it has a dedicated
            // node in the tree-sitter grammar, and so cannot appear
            "bool" => ast::PrimTy::Bool,
            "char" => ast::PrimTy::Char,
            "string" => ast::PrimTy::String,
            "int" => ast::PrimTy::Int,
            "float" => ast::PrimTy::Float,
            _ => unreachable!("There are no other primitive types."),
        };

        Ok(prim)
    }

    fn visit_tuple_type(
        &self,
        node: TupleType<'a>,
    ) -> CstResult<'a, SpanSeq<ast::Ty>> {
        let mut cursor = node.walk();
        let mut tys = Vec::new();

        for ty in node.type_exprs(&mut cursor) {
            let ty = self.visit_type(ty?)?;
            tys.push(ty);
        }

        Ok(tys.into_boxed_slice())
    }

    fn visit_fn_type(
        &self,
        node: FnType<'a>,
    ) -> CstResult<'a, Spanned<ast::Ty>> {
        let span = node_span(node);
        let codomain = self.visit_type(node.codomain()?).map(Box::new)?;

        let domain = match node.domain()? {
            TypeExpr_FnTypeArgs::TypeExpr(type_expr) => self
                .visit_type(type_expr)
                .map(|spanned| spanned.item)
                .map(ast::FnTyArgs::NoParens),
            TypeExpr_FnTypeArgs::FnTypeArgs(fn_type_args) => {
                let mut cursor = node.walk();
                let mut tys = Vec::new();

                for ty in fn_type_args.type_exprs(&mut cursor) {
                    let ty = self.visit_type(ty?)?;
                    tys.push(ty);
                }

                Ok(ast::FnTyArgs::Parens(tys.into_boxed_slice()))
            }
        }
        .map(|dom| node_span(node.domain()).with(dom))
        .map(Box::new)?;

        Ok(ast::Ty::Fn { domain, codomain }).map(|ty| span.with(ty))
    }

    fn visit_generic_type(
        &self,
        node: GenericType<'a>,
    ) -> CstResult<'a, Spanned<ast::Ty>> {
        let span = node_span(node);
        let name = self
            .visit_name(node.name()?)
            .map(|name| node_span(node.name()).with(name))?;

        let args = {
            let mut cursor = node.walk();
            let mut tys = Vec::new();

            for ty in node.arguments()?.type_exprs(&mut cursor) {
                let ty = self.visit_type(ty?)?;
                tys.push(ty);
            }

            tys.into_boxed_slice()
        };

        Ok(ast::Ty::Generic { name, args }).map(|ty| span.with(ty))
    }

    // NAMES

    fn visit_name(&self, node: Name<'a>) -> CstResult<'a, ast::Name> {
        match node {
            Name::Ident(_) => Ok(ast::Name::Ident),
            Name::Path(path) => self.visit_path(path).map(ast::Name::Path),
        }
    }

    fn visit_path(&self, node: Path<'a>) -> CstResult<'a, SpanSeq<ast::Ident>> {
        fn path_rec<'a>(
            visitor: &CstVisitor<'a>,
            node: Name<'a>,
            elems: &mut Vec<Spanned<ast::Ident>>,
        ) -> CstResult<'a, ()> {
            match node {
                Name::Ident(ident) => {
                    elems.push(visitor.visit_ident(ident));
                    Ok(())
                }
                Name::Path(path) => {
                    let root = path.root()?;
                    let name = path.name()?;
                    path_rec(visitor, root, elems)?;
                    elems.push(visitor.visit_ident(name));
                    Ok(())
                }
            }
        }

        let root = node.root()?;
        let name = node.name()?;

        let mut elems = Vec::new();
        path_rec(self, root, &mut elems)?;
        elems.push(self.visit_ident(name));
        Ok(elems.into_boxed_slice())
    }

    fn visit_ident(&self, node: Ident) -> Spanned<ast::Ident> {
        let span = node_span(node);
        span.with(ast::Ident)
    }
}

fn node_span<'a>(node: impl Node<'a>) -> Span {
    Span::try_from(node.range())
        .expect("Encountered byte index exceeding u32::MAX")
}

#[cfg(test)]
mod tests {
    use crate::{file::File, span::Spanned};

    use super::{ast, CstVisitor, Parser};

    #[test]
    fn cst_visitor_types() {
        let source = File::fake(
            r#"
            type Err = std.result.Result[!, _, (X, Y, Z) -> (F -> bool)]
            "#,
        );

        let mut parser = Parser::new().unwrap();
        let tree = parser.parse(&source).unwrap().tree;
        let visitor = CstVisitor {
            source: source.contents(),
        };

        let mut cursor = tree.walk();
        let mut decls = tree.root_node().unwrap().decls(&mut cursor);

        let type_node = decls
            .next()
            .unwrap()
            .unwrap()
            .as_type_decl()
            .unwrap()
            .r#type()
            .unwrap();

        let ty = visitor.visit_type(type_node).unwrap();
        dbg!(ty.clone());

        match ty.item {
            ast::Ty::Generic { name, args } => {
                assert_eq!(args.len(), 3);
                assert!(matches!(
                    args.first(),
                    Some(Spanned {
                        item: ast::Ty::Prim(ast::PrimTy::Never,),
                        ..
                    })
                ));

                match name.item {
                    ast::Name::Ident => panic!(),
                    ast::Name::Path(path) => {
                        assert_eq!(path.len(), 3);
                    }
                };
            }
            _ => panic!(),
        }
    }
}
