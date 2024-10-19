//! Concrete syntax trees parsed using Tree-sitter.

#[allow(clippy::all)]
#[allow(unused)]
pub(crate) mod nodes {
    include!(concat!(env!("OUT_DIR"), "/nodes.rs"));
}

#[allow(clippy::all)]
#[allow(unused)]
pub(crate) mod queries {
    include!(concat!(env!("OUT_DIR"), "/queries.rs"));
}

use crate::{
    ast::unbound as ast,
    file::File,
    span::{Span, SpanSeq, Spanned},
};

use nodes::{
    anon_unions::TypeExpr_FnTypeArgs, AccessSpec, Attribute, AttributeArgument,
    Attributes, Decl, DocComments, FnType, GenericParams, GenericType, Ident,
    LiteralExpr, Name, Path, PrimitiveType, SourceFile, TupleType, TypeDecl,
    TypeExpr,
};

use thiserror::Error;
use type_sitter::{
    raw, IncorrectKind, Node, QueryCursor, StreamingIterator, Tree,
};

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

/// The owned components of an `Ast`. The first element is taken to be the
/// `shebang` field, and the second is taken as the `module_comment` field.
type AstComponents =
    (Option<Span>, Option<Span>, Box<[Span]>, SpanSeq<ast::Decl>);

impl<'a> CstVisitor<'a> {
    fn visit_source_file(
        &self,
        node: SourceFile<'a>,
    ) -> CstResult<'a, AstComponents> {
        let shebang = node.shebang().transpose()?.map(node_span);
        let module_comment = node.module_comment().transpose()?.map(node_span);

        let comments: Box<[Span]> = {
            // query boilerplate
            let mut qcursor = QueryCursor::new();
            let mut comments = Vec::new();
            let mut matches = qcursor.matches(
                &queries::Comments,
                node,
                self.source.as_bytes(),
            );

            // matches is a StreamingIterator, so we have to manually
            // iterate over it
            while let Some(comment) = matches.get() {
                // get iterator over the individual line comments
                let mut comment_elems = comment.comments();
                // grab the span of the first line comment
                let Span { start, mut end } =
                    node_span(comment_elems.next().unwrap());
                // if we have more than one line comment, grab the last one
                // and set the end of the total span to its span.end
                if let Some(last_comment) = comment_elems.last() {
                    let Span { end: last_end, .. } = node_span(last_comment);
                    end = last_end
                }

                // assemble the complete span, add it to
                // the list, and advance the iterator
                let span = Span { start, end };
                comments.push(span);
                matches.advance();
            }

            comments.into_boxed_slice()
        };

        let decls = {
            let mut decls = Vec::new();
            let mut cursor = node.walk();

            for decl in node.decls(&mut cursor) {
                let decl = self.visit_decl(decl?)?;
                decls.push(decl);
            }

            decls.into_boxed_slice()
        };

        Ok((shebang, module_comment, comments, decls))
    }

    // DECLS
    fn visit_decl(&self, node: Decl<'a>) -> CstResult<'a, Spanned<ast::Decl>> {
        match node {
            Decl::ConstDecl(const_decl) => todo!(),
            Decl::EnumDecl(enum_decl) => todo!(),
            Decl::ExternFnDecl(extern_fn_decl) => todo!(),
            Decl::ExternTypeDecl(extern_type_decl) => todo!(),
            Decl::FnDecl(fn_decl) => todo!(),
            Decl::ModDecl(mod_decl) => todo!(),
            Decl::StructDecl(struct_decl) => todo!(),
            Decl::TypeDecl(type_decl) => self.visit_type_decl(type_decl),
            Decl::UseDecl(use_decl) => todo!(),
        }
    }

    fn visit_type_decl(
        &self,
        node: TypeDecl<'a>,
    ) -> CstResult<'a, Spanned<ast::Decl>> {
        // common decl components
        let doc_comment = self.visit_doc_comment_opt(node.docs().transpose()?);
        let attributes =
            self.visit_attributes_opt(node.attributes().transpose()?)?;
        let visibility =
            self.visit_access_spec_opt(node.visibility().transpose()?);

        // type decl components
        let name = self.visit_ident(node.name()?);
        let params =
            self.visit_generic_params_opt(node.params().transpose()?)?;
        let ty = self.visit_type(node.r#type()?)?;

        let span = node_span(node);
        Ok(span.with(ast::Decl {
            doc_comment,
            attributes,
            visibility,
            kind: ast::DeclKind::Type { name, params, ty },
        }))
    }

    fn visit_generic_params_opt(
        &self,
        node: Option<GenericParams<'a>>,
    ) -> CstResult<'a, SpanSeq<ast::Ident>> {
        let mut params = Vec::new();

        if let Some(node) = node {
            let mut cursor = node.walk();

            for param in node.idents(&mut cursor) {
                let param = self.visit_ident(param?);
                params.push(param);
            }
        }

        Ok(params.into_boxed_slice())
    }

    fn visit_doc_comment_opt(
        &self,
        node: Option<DocComments<'a>>,
    ) -> Option<Span> {
        node.map(node_span)
    }

    fn visit_access_spec_opt(
        &self,
        node: Option<AccessSpec<'a>>,
    ) -> ast::Visibility {
        match node {
            None => ast::Visibility::Priv,
            Some(access_spec) => ast::Visibility::Pub(node_span(access_spec)),
        }
    }

    // ATTRIBUTES
    fn visit_attributes_opt(
        &self,
        node: Option<Attributes<'a>>,
    ) -> CstResult<'a, SpanSeq<ast::Attr>> {
        let mut attrs = Vec::new();

        if let Some(node) = node {
            let mut cursor = node.walk();

            for attr in node.attributes(&mut cursor) {
                let attr = self.visit_attribute(attr?)?;
                attrs.push(attr);
            }
        }

        Ok(attrs.into_boxed_slice())
    }

    fn visit_attribute(
        &self,
        node: Attribute<'a>,
    ) -> CstResult<'a, Spanned<ast::Attr>> {
        let span = node_span(node);

        let name = {
            let span = node_span(node.name());
            let name = self.visit_name(node.name()?)?;
            span.with(name)
        };

        let args = {
            let mut args = Vec::new();

            if let Some(attr_args) = node.arguments().transpose()? {
                let mut cursor = node.walk();

                for arg in attr_args.attribute_arguments(&mut cursor) {
                    let arg = self.visit_attribute_argument(arg?)?;
                    args.push(arg);
                }
            }

            args.into_boxed_slice()
        };

        Ok(span.with(ast::Attr { name, args }))
    }

    fn visit_attribute_argument(
        &self,
        node: AttributeArgument<'a>,
    ) -> CstResult<'a, Spanned<ast::AttrArg>> {
        let span = node_span(node);

        match node {
            AttributeArgument::LiteralExpr(literal_expr) => self
                .visit_literal_expr(literal_expr)
                .map(ast::AttrArg::Literal)
                .map(|arg| span.with(arg)),
            AttributeArgument::Name(name) => self
                .visit_name(name)
                .map(ast::AttrArg::Name)
                .map(|name| span.with(name)),
        }
    }

    // EXPRESSIONS

    fn visit_literal_expr(
        &self,
        node: LiteralExpr<'a>,
    ) -> CstResult<'a, ast::LiteralExpr> {
        match node {
            LiteralExpr::BinLiteral(bin_literal) => todo!(),
            LiteralExpr::BoolLiteralFalse(bool_literal_false) => todo!(),
            LiteralExpr::BoolLiteralTrue(bool_literal_true) => todo!(),
            LiteralExpr::CharLiteral(char_literal) => todo!(),
            LiteralExpr::DecLiteral(dec_literal) => todo!(),
            LiteralExpr::FloatLiteral(float_literal) => todo!(),
            LiteralExpr::HexLiteral(hex_literal) => todo!(),
            LiteralExpr::OctLiteral(oct_literal) => todo!(),
            LiteralExpr::StringLiteral(string_literal) => todo!(),
            LiteralExpr::UnitLiteral(_) => Ok(ast::LiteralExpr::Unit),
        }
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
