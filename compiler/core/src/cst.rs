//! Concrete syntax trees parsed using Tree-sitter.

#[allow(clippy::all)]
#[allow(unused)]
#[allow(rustdoc::all)]
pub(crate) mod nodes {
    include!(concat!(env!("OUT_DIR"), "/nodes.rs"));
}

#[allow(clippy::all)]
#[allow(unused)]
#[allow(rustdoc::all)]
pub(crate) mod queries {
    include!(concat!(env!("OUT_DIR"), "/queries.rs"));
}

use crate::{
    ast::unbound as ast,
    file::File,
    span::{Span, SpanSeq, Spanned},
};

use nodes::{
    anon_unions::{
        EmptyStmt_ExprStmt_LetStmt as EsEsLs, Ident_Parameters,
        Ident_TupleField as ITf, Name_AliasItem_GlobItem_TreeItem as UseItem,
        RecordExprField_RecordUpdateBase as RefRub,
        RecordPatternField_RestPattern as RpfRp,
        RecordPayload_TuplePayload as RpTp, TypeExpr_FnTypeArgs as TeFta,
    },
    AccessSpec, Attribute, AttributeArgument, Attributes, BinaryOperator,
    Block, ConstDecl, Decl, DocComments, Expr, ExternFnDecl, ExternTypeDecl,
    FnDecl, FnType, GenericParams, GenericType, Ident, LiteralExpr, MatchArms,
    ModDecl, Name, Parameters, Path, Pattern, PrefixOperator, PrimitiveType,
    RecordExprField, RecordPatternField, RecordPayload, SourceFile,
    TuplePayload, TupleType, TypeAliasDecl, TypeConstructor, TypeDecl,
    TypeExpr, UseDecl,
};

use thiserror::Error;
use type_sitter::{
    raw, IncorrectKind, Node, QueryCursor, Range, StreamingIterator, Tree,
    TreeCursor,
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

#[derive(Debug, Clone, Copy, Error)]
pub enum ParseError {
    #[error("Parse error in {parent_kind} [{}..{}]", range.start_point, range.end_point)]
    Error {
        parent_kind: &'static str,
        range: Range,
    },
    #[error("Missing {kind} in {parent_kind} [{}..{}]", range.start_point, range.end_point)]
    Missing {
        parent_kind: &'static str,
        kind: &'static str,
        name: Option<&'static str>,
        range: Range,
    },
}

impl<'a> TryFrom<Cst<'a>> for ast::Ast {
    type Error = Box<[ParseError]>;

    fn try_from(value: Cst<'a>) -> Result<Self, Self::Error> {
        value.build_ast()
    }
}

impl<'a> Cst<'a> {
    fn build_ast(self) -> Result<ast::Ast, Box<[ParseError]>> {
        let errors = self.collect_errors();
        if !errors.is_empty() {
            return Err(errors);
        }

        // beyond this point, self.tree contains no errors

        let visitor = self.visitor();
        let Cst { tree, .. } = self;
        let root = tree.root_node().unwrap();
        let (shebang, module_comment, comments, decls) =
            visitor.visit_source_file(root).unwrap();

        Ok(ast::Ast::new(shebang, module_comment, comments, decls))
    }

    fn visitor(&self) -> CstVisitor<'a> {
        CstVisitor {
            source: self.file.contents(),
        }
    }

    fn collect_errors(&self) -> Box<[ParseError]> {
        fn collect_rec(errors: &mut Vec<ParseError>, cursor: &mut TreeCursor) {
            let node = cursor.node();

            if node.is_error() {
                let range = node.range();
                let parent_kind = node
                    .parent()
                    .map(|parent| parent.kind())
                    .unwrap_or("source_file");

                errors.push(ParseError::Error { range, parent_kind })
            } else if node.is_missing() {
                let range = node.range();
                let kind = node.kind();
                let name = cursor.field_name();
                let parent_kind = node
                    .parent()
                    .map(|parent| parent.kind())
                    .unwrap_or("source_file");

                errors.push(ParseError::Missing {
                    range,
                    name,
                    kind,
                    parent_kind,
                })
            }

            if cursor.goto_first_child() {
                loop {
                    collect_rec(errors, cursor);

                    if !cursor.goto_next_sibling() {
                        break;
                    }
                }

                cursor.goto_parent();
            }
        }

        let mut errors = Vec::new();
        let mut cursor = self.tree.walk();
        collect_rec(&mut errors, &mut cursor);
        errors.into_boxed_slice()
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
            while let Some(comment) = matches.next() {
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
            }

            comments.into_boxed_slice()
        };

        let decls = {
            let mut decls = Vec::new();
            let mut cursor = node.walk();

            for decl in node.declarations(&mut cursor) {
                let span = node_span(decl);
                let doc_comment =
                    self.visit_doc_comment_opt(decl?.docs().transpose()?);
                let attributes =
                    self.visit_attributes_opt(decl?.attributes().transpose()?)?;
                let visibility =
                    self.visit_access_spec_opt(decl?.visibility().transpose()?);
                let kind = self.visit_decl(decl?.body()?)?;

                decls.push(span.with(ast::Decl {
                    doc_comment,
                    attributes,
                    visibility,
                    kind,
                }));
            }

            decls.into_boxed_slice()
        };

        Ok((shebang, module_comment, comments, decls))
    }

    // DECLS
    fn visit_decl(
        &self,
        node: Decl<'a>,
    ) -> CstResult<'a, Spanned<ast::DeclKind>> {
        match node {
            Decl::UseDecl(use_decl) => self.visit_use_decl(use_decl),
            Decl::ModDecl(mod_decl) => self.visit_mod_decl(mod_decl),
            Decl::ConstDecl(const_decl) => self.visit_const_decl(const_decl),
            Decl::FnDecl(fn_decl) => self.visit_fn_decl(fn_decl),
            Decl::ExternFnDecl(extern_fn_decl) => {
                self.visit_extern_fn_decl(extern_fn_decl)
            }
            Decl::TypeDecl(type_decl) => self.visit_type_decl(type_decl),
            Decl::TypeAliasDecl(type_alias_decl) => {
                self.visit_type_alias_decl(type_alias_decl)
            }
            Decl::ExternTypeDecl(extern_type_decl) => {
                self.visit_extern_type_decl(extern_type_decl)
            }
        }
    }

    fn visit_use_decl(
        &self,
        node: UseDecl<'a>,
    ) -> CstResult<'a, Spanned<ast::DeclKind>> {
        let item = self.visit_use_item(node.item()?)?;

        let span = node_span(node);
        Ok(span.with(ast::DeclKind::Use { item }))
    }

    fn visit_mod_decl(
        &self,
        node: ModDecl<'a>,
    ) -> CstResult<'a, Spanned<ast::DeclKind>> {
        let name = self.visit_ident(node.name()?);

        let span = node_span(node);
        Ok(span.with(ast::DeclKind::Mod { name }))
    }

    fn visit_const_decl(
        &self,
        node: ConstDecl<'a>,
    ) -> CstResult<'a, Spanned<ast::DeclKind>> {
        let name = self.visit_ident(node.name()?);
        let ty = self.visit_type(node.r#type()?)?;
        let value = self.visit_expr(node.value()?)?;

        let span = node_span(node);
        Ok(span.with(ast::DeclKind::Const { name, ty, value }))
    }

    fn visit_fn_decl(
        &self,
        node: FnDecl<'a>,
    ) -> CstResult<'a, Spanned<ast::DeclKind>> {
        let name = self.visit_ident(node.name()?);
        let params = self.visit_parameters(node.parameters()?)?;
        let return_ty = node
            .return_type()
            .transpose()?
            .map(|ty| self.visit_type(ty))
            .transpose()?;

        let body = Box::new(if let Some(expr) = node.eq_body().transpose()? {
            let Spanned { item: expr, span } = self.visit_expr(expr)?;
            span.with(ast::FnBody::EqExpr(expr))
        } else if let Some(block) = node.block_body().transpose()? {
            let Spanned { item: block, span } = self.visit_block(block)?;
            span.with(ast::FnBody::Block(block))
        } else {
            unreachable!("The body of a fn_decl has no other forms")
        });

        let span = node_span(node);
        Ok(span.with(ast::DeclKind::Fn {
            name,
            params,
            return_ty,
            body,
        }))
    }

    fn visit_extern_fn_decl(
        &self,
        node: ExternFnDecl<'a>,
    ) -> CstResult<'a, Spanned<ast::DeclKind>> {
        let name = self.visit_ident(node.name()?);
        let params = self.visit_parameters(node.parameters()?)?;
        let return_ty = node
            .return_type()
            .transpose()?
            .map(|ty| self.visit_type(ty))
            .transpose()?;

        let span = node_span(node);
        Ok(span.with(ast::DeclKind::ExternFn {
            name,
            params,
            return_ty,
        }))
    }

    fn visit_type_alias_decl(
        &self,
        node: TypeAliasDecl<'a>,
    ) -> CstResult<'a, Spanned<ast::DeclKind>> {
        let name = self.visit_ident(node.name()?);
        let params =
            self.visit_generic_params_opt(node.params().transpose()?)?;
        let ty = self.visit_type(node.r#type()?)?;

        let span = node_span(node);
        Ok(span.with(ast::DeclKind::TypeAlias { name, params, ty }))
    }

    fn visit_type_decl(
        &self,
        node: TypeDecl<'a>,
    ) -> CstResult<'a, Spanned<ast::DeclKind>> {
        let name = self.visit_ident(node.name()?);
        let params =
            self.visit_generic_params_opt(node.params().transpose()?)?;

        let constructors = {
            let mut constructors = Vec::new();
            let mut cursor = node.walk();

            for constructor in
                node.constructors()?.type_constructors(&mut cursor)
            {
                let constructor = self.visit_type_constructor(constructor?)?;
                constructors.push(constructor);
            }

            constructors.into_boxed_slice()
        };

        let span = node_span(node);
        Ok(span.with(ast::DeclKind::Type {
            name,
            params,
            constructors,
        }))
    }

    fn visit_extern_type_decl(
        &self,
        node: ExternTypeDecl<'a>,
    ) -> CstResult<'a, Spanned<ast::DeclKind>> {
        let name = self.visit_ident(node.name()?);
        let params =
            self.visit_generic_params_opt(node.params().transpose()?)?;

        let span = node_span(node);
        Ok(span.with(ast::DeclKind::ExternType { name, params }))
    }

    fn visit_use_item(
        &self,
        node: UseItem<'a>,
    ) -> CstResult<'a, Spanned<ast::UseItem>> {
        let span = node_span(node);

        match node {
            UseItem::Name(name) => {
                let name = self.visit_name(name).map(Spanned::unwrap)?;
                Ok(ast::UseItem::Name(name))
            }
            UseItem::AliasItem(alias_item) => {
                let item = self.visit_name(alias_item.item()?)?;
                let alias = self.visit_ident(alias_item.alias()?);

                Ok(ast::UseItem::Alias { item, alias })
            }
            UseItem::GlobItem(glob_item) => {
                let root = glob_item
                    .root()
                    .transpose()?
                    .map(|name| self.visit_name(name))
                    .transpose()?;

                Ok(ast::UseItem::Glob { root })
            }
            UseItem::TreeItem(tree_item) => {
                let root = tree_item
                    .root()
                    .transpose()?
                    .map(|name| self.visit_name(name))
                    .transpose()?;

                let items = {
                    let mut items = Vec::new();
                    let mut cursor = tree_item.walk();

                    for item in tree_item.items()?.children(&mut cursor) {
                        let item = self.visit_use_item(item?)?;
                        items.push(item);
                    }

                    items.into_boxed_slice()
                };

                Ok(ast::UseItem::Tree { root, items })
            }
        }
        .map(|use_item| span.with(use_item))
    }

    fn visit_type_constructor(
        &self,
        node: TypeConstructor<'a>,
    ) -> CstResult<'a, Spanned<ast::TyConstr>> {
        let span = node_span(node);

        let doc_comment = self.visit_doc_comment_opt(node.docs().transpose()?);
        let attributes =
            self.visit_attributes_opt(node.attributes().transpose()?)?;
        let name = self.visit_ident(node.name()?);
        let payload = node
            .payload()
            .transpose()?
            .map(|payload| match payload {
                RpTp::RecordPayload(rec) => self.visit_record_payload(rec),
                RpTp::TuplePayload(tup) => self.visit_tuple_payload(tup),
            })
            .transpose()?;

        Ok(span.with(ast::TyConstr {
            doc_comment,
            attributes,
            name,
            payload,
        }))
    }

    fn visit_record_payload(
        &self,
        node: RecordPayload<'a>,
    ) -> CstResult<'a, Spanned<ast::TyConstrPayload>> {
        let mut fields = Vec::new();
        let mut cursor = node.walk();

        for field in node.record_fields(&mut cursor) {
            let doc_comment =
                self.visit_doc_comment_opt(field?.docs().transpose()?);
            let attributes =
                self.visit_attributes_opt(field?.attributes().transpose()?)?;

            let mutability = match field?.mutable().transpose()? {
                Some(node) => ast::Mutability::Mut(node_span(node)),
                None => ast::Mutability::Immut,
            };

            let name = self.visit_ident(field?.name()?);
            let ty = self.visit_type(field?.r#type()?)?;

            let span = node_span(field);
            fields.push(span.with(ast::RecordField {
                doc_comment,
                attributes,
                mutability,
                name,
                ty,
            }));
        }

        let fields = fields.into_boxed_slice();
        let span = node_span(node);
        Ok(span.with(ast::TyConstrPayload::Record(fields)))
    }

    fn visit_tuple_payload(
        &self,
        node: TuplePayload<'a>,
    ) -> CstResult<'a, Spanned<ast::TyConstrPayload>> {
        let mut elems = Vec::new();
        let mut cursor = node.walk();

        for ty in node.type_exprs(&mut cursor) {
            let ty = self.visit_type(ty?)?;
            elems.push(ty);
        }

        let elems = elems.into_boxed_slice();
        let span = node_span(node);
        Ok(span.with(ast::TyConstrPayload::Tuple(elems)))
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

    fn visit_parameters(
        &self,
        node: Parameters<'a>,
    ) -> CstResult<'a, Spanned<SpanSeq<ast::Parameter>>> {
        let span = node_span(node);
        let mut params = Vec::new();
        let mut cursor = node.walk();

        for param in node.parameters(&mut cursor) {
            let span = node_span(param);
            let pattern = self.visit_pattern(param?.pattern()?)?;
            let ty = param?
                .r#type()
                .transpose()?
                .map(|ty| self.visit_type(ty))
                .transpose()?;

            params.push(span.with(ast::Parameter { pattern, ty }))
        }

        Ok(span.with(params.into_boxed_slice()))
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
        let name = self.visit_name(node.name()?)?;
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
            AttributeArgument::LiteralExpr(literal_expr) => {
                Ok(ast::AttrArg::Literal(self.visit_literal_expr(literal_expr)))
                    .map(|arg| span.with(arg))
            }
            AttributeArgument::Name(name) => self
                .visit_name(name)
                .map(Spanned::unwrap)
                .map(ast::AttrArg::Name)
                .map(|name| span.with(name)),
        }
    }

    // EXPRESSIONS

    fn visit_expr(&self, node: Expr<'a>) -> CstResult<'a, Spanned<ast::Expr>> {
        let span = node_span(node);

        match node {
            Expr::Ident(_) => Ok(ast::Expr::Name(ast::Name::Ident)),
            Expr::Path(path) => self
                .visit_path(path)
                .map(Spanned::unwrap)
                .map(ast::Expr::Name),
            Expr::LiteralExpr(literal_expr) => {
                Ok(ast::Expr::Literal(self.visit_literal_expr(literal_expr)))
            }
            Expr::PrefixExpr(prefix_op) => {
                let operand =
                    self.visit_expr(prefix_op.operand()?).map(Box::new)?;
                let operator =
                    self.visit_prefix_operator(prefix_op.operator()?);

                Ok(ast::Expr::Prefix { operand, operator })
            }
            Expr::BinaryExpr(binary_op) => {
                let lhs = self.visit_expr(binary_op.lhs()?).map(Box::new)?;
                let rhs = self.visit_expr(binary_op.rhs()?).map(Box::new)?;
                let operator =
                    self.visit_binary_operator(binary_op.operator()?);

                Ok(ast::Expr::Binary { lhs, operator, rhs })
            }
            Expr::CallExpr(call_expr) => {
                let callee =
                    self.visit_expr(call_expr.callee()?).map(Box::new)?;

                let args = {
                    let mut args = Vec::new();
                    let mut cursor = call_expr.walk();

                    for arg in call_expr.arguments()?.exprs(&mut cursor) {
                        let arg = self.visit_expr(arg?)?;
                        args.push(arg);
                    }

                    args.into_boxed_slice()
                };

                Ok(ast::Expr::Call { callee, args })
            }
            Expr::FieldExpr(field_expr) => {
                let item = self.visit_expr(field_expr.item()?).map(Box::new)?;
                let field = {
                    let span = node_span(field_expr.field());

                    let field = match field_expr.field()? {
                        ITf::Ident(_) => ast::FieldExprField::Ident,
                        ITf::TupleField(_) => ast::FieldExprField::TupleIndex,
                    };

                    span.with(field)
                };

                Ok(ast::Expr::Field { item, field })
            }
            Expr::IfElseExpr(if_else_expr) => {
                let condition =
                    self.visit_expr(if_else_expr.condition()?).map(Box::new)?;

                let consequence = self
                    .visit_block(if_else_expr.consequence()?)
                    .map(Box::new)?;

                let alternative = if_else_expr
                    .alternative()
                    .transpose()?
                    .map(|else_clause| else_clause.body())
                    .transpose()?
                    .map(|block| self.visit_block(block))
                    .transpose()?
                    .map(Box::new);

                Ok(ast::Expr::IfElse {
                    condition,
                    consequence,
                    alternative,
                })
            }
            Expr::LambdaExpr(lambda_expr) => {
                let params = {
                    let span = node_span(lambda_expr.parameters());
                    span.with(match lambda_expr.parameters()? {
                        Ident_Parameters::Ident(_) => ast::LambdaParams::Ident,
                        Ident_Parameters::Parameters(parameters) => self
                            .visit_parameters(parameters)
                            .map(Spanned::unwrap)
                            .map(ast::LambdaParams::Parameters)?,
                    })
                };

                let body =
                    self.visit_expr(lambda_expr.body()?).map(Box::new)?;

                Ok(ast::Expr::Lambda { params, body })
            }
            Expr::MatchExpr(match_expr) => {
                let arms = self.visit_match_arms(match_expr.arms()?)?;
                let scrutinee =
                    self.visit_expr(match_expr.scrutinee()?).map(Box::new)?;

                Ok(ast::Expr::Match { scrutinee, arms })
            }
            Expr::RecordExpr(record_expr) => {
                let name = self.visit_name(record_expr.name()?)?;

                let mut fields = Vec::new();
                let mut base = None;

                if let Some(Ok(field_iter)) = record_expr.fields() {
                    let mut cursor = record_expr.walk();

                    for field in field_iter.children(&mut cursor) {
                        match field? {
                            RefRub::RecordExprField(field) => {
                                let field =
                                    self.visit_record_expr_field(field)?;
                                fields.push(field);
                            }
                            RefRub::RecordUpdateBase(update) => {
                                // this is fine because the record update
                                // base can only appear once
                                let expr = self.visit_expr(update.expr()?)?;
                                base = Some(Box::new(expr));
                            }
                        }
                    }
                }

                let fields = fields.into_boxed_slice();
                Ok(ast::Expr::Record { name, fields, base })
            }
            Expr::TupleExpr(tuple_expr) => {
                let mut exprs = Vec::new();
                let mut cursor = tuple_expr.walk();

                for expr in tuple_expr.exprs(&mut cursor) {
                    let expr = self.visit_expr(expr?)?;
                    exprs.push(expr);
                }

                Ok(ast::Expr::Tuple(exprs.into_boxed_slice()))
            }
            Expr::ListExpr(list_expr) => {
                let mut exprs = Vec::new();
                let mut cursor = list_expr.walk();

                for expr in list_expr.exprs(&mut cursor) {
                    let expr = self.visit_expr(expr?)?;
                    exprs.push(expr);
                }

                Ok(ast::Expr::List(exprs.into_boxed_slice()))
            }
            Expr::ParenthesizedExpr(paren_expr) => {
                let inner =
                    self.visit_expr(paren_expr.inner()?).map(Box::new)?;

                Ok(ast::Expr::Paren(inner))
            }
            Expr::Block(block) => self
                .visit_block(block)
                .map(|Spanned { item, .. }| ast::Expr::Block(Box::new(item))),
        }
        .map(|expr| span.with(expr))
    }

    fn visit_literal_expr(&self, node: LiteralExpr<'a>) -> ast::LiteralExpr {
        match node {
            LiteralExpr::BinLiteral(_) => ast::LiteralExpr::BinInt,
            LiteralExpr::BoolLiteralFalse(_) => ast::LiteralExpr::Bool(false),
            LiteralExpr::BoolLiteralTrue(_) => ast::LiteralExpr::Bool(true),
            LiteralExpr::CharLiteral(_) => ast::LiteralExpr::Char,
            LiteralExpr::DecLiteral(_) => ast::LiteralExpr::DecInt,
            LiteralExpr::FloatLiteral(_) => ast::LiteralExpr::Float,
            LiteralExpr::HexLiteral(_) => ast::LiteralExpr::HexInt,
            LiteralExpr::OctLiteral(_) => ast::LiteralExpr::OctInt,
            LiteralExpr::StringLiteral(_) => ast::LiteralExpr::String,
            LiteralExpr::UnitLiteral(_) => ast::LiteralExpr::Unit,
        }
    }

    fn visit_match_arms(
        &self,
        node: MatchArms<'a>,
    ) -> CstResult<'a, Spanned<SpanSeq<ast::MatchArm>>> {
        let span = node_span(node);
        let mut arms = Vec::new();

        let mut cursor = node.walk();
        for arm in node.match_arms(&mut cursor) {
            let span = node_span(arm);
            let pattern = self.visit_pattern(arm?.pattern()?)?;
            let body = self.visit_expr(arm?.body()?)?;

            let guard = arm?
                .guard()
                .transpose()?
                .map(|guard| guard.expr())
                .transpose()?
                .map(|expr| self.visit_expr(expr))
                .transpose()?;

            arms.push(span.with(ast::MatchArm {
                pattern,
                guard,
                body,
            }))
        }

        Ok(span.with(arms.into_boxed_slice()))
    }

    fn visit_record_expr_field(
        &self,
        node: RecordExprField<'a>,
    ) -> CstResult<'a, Spanned<ast::RecordExprField>> {
        let span = node_span(node);
        let field = self.visit_ident(node.name()?);
        let value = node
            .value()
            .transpose()?
            .map(|expr| self.visit_expr(expr))
            .transpose()?;

        Ok(span.with(ast::RecordExprField { field, value }))
    }

    fn visit_block(
        &self,
        node: Block<'a>,
    ) -> CstResult<'a, Spanned<ast::Block>> {
        let span = node_span(node);

        let statements = {
            let mut statements = Vec::new();
            let mut cursor = node.walk();

            for stmt in node.others(&mut cursor) {
                let span = node_span(stmt);
                let stmt = match stmt? {
                    EsEsLs::EmptyStmt(_) => ast::Stmt::Empty,
                    EsEsLs::ExprStmt(expr_stmt) => {
                        let expr = self.visit_expr(expr_stmt.expr()?)?;
                        ast::Stmt::Expr(expr)
                    }
                    EsEsLs::LetStmt(let_stmt) => {
                        let pattern =
                            self.visit_pattern(let_stmt.pattern()?)?;
                        let ty = let_stmt
                            .r#type()
                            .transpose()?
                            .map(|ty| self.visit_type(ty))
                            .transpose()?;
                        let value = self.visit_expr(let_stmt.value()?)?;

                        ast::Stmt::Let { pattern, ty, value }
                    }
                };

                statements.push(span.with(stmt));
            }

            statements.into_boxed_slice()
        };

        let return_expr = node
            .return_expr()
            .transpose()?
            .map(|expr| self.visit_expr(expr))
            .transpose()?;

        Ok(span.with(ast::Block {
            statements,
            return_expr,
        }))
    }

    fn visit_prefix_operator(
        &self,
        node: PrefixOperator<'a>,
    ) -> Spanned<ast::PrefixOp> {
        let span = node_span(node);

        span.with(match node.utf8_text(self.source.as_bytes()).unwrap() {
            "!" => ast::PrefixOp::Bang,
            "-" => ast::PrefixOp::Minus,
            "-." => ast::PrefixOp::MinusDot,
            "*" => ast::PrefixOp::Star,
            _ => unreachable!("There are no other prefix operators."),
        })
    }

    fn visit_binary_operator(
        &self,
        node: BinaryOperator<'a>,
    ) -> Spanned<ast::BinaryOp> {
        let span = node_span(node);

        span.with(match node.utf8_text(self.source.as_bytes()).unwrap() {
            "+" => ast::BinaryOp::Plus,
            "+." => ast::BinaryOp::PlusDot,
            "-" => ast::BinaryOp::Minus,
            "-." => ast::BinaryOp::MinusDot,
            "*" => ast::BinaryOp::Star,
            "*." => ast::BinaryOp::StarDot,
            "/" => ast::BinaryOp::Slash,
            "/." => ast::BinaryOp::SlashDot,
            "^" => ast::BinaryOp::Carat,
            "^." => ast::BinaryOp::CaratDot,
            "%" => ast::BinaryOp::Percent,
            "==" => ast::BinaryOp::EqEq,
            "!=" => ast::BinaryOp::BangEq,
            ">" => ast::BinaryOp::Gt,
            ">." => ast::BinaryOp::GtDot,
            "<" => ast::BinaryOp::Lt,
            "<." => ast::BinaryOp::LtDot,
            ">=" => ast::BinaryOp::Geq,
            ">=." => ast::BinaryOp::GeqDot,
            "<=" => ast::BinaryOp::Leq,
            "<=." => ast::BinaryOp::LeqDot,
            "|>" => ast::BinaryOp::RightPipe,
            "<|" => ast::BinaryOp::LeftPipe,
            "::" => ast::BinaryOp::Cons,
            "++" => ast::BinaryOp::PlusPlus,
            "||" => ast::BinaryOp::BarBar,
            "&&" => ast::BinaryOp::AmpAmp,
            "<-" => ast::BinaryOp::LeftArrow,
            ":=" => ast::BinaryOp::Walrus,
            _ => unreachable!("There are no other binary operators."),
        })
    }

    // PATTERNS

    fn visit_pattern(
        &self,
        node: Pattern<'a>,
    ) -> CstResult<'a, Spanned<ast::Pattern>> {
        let span = node_span(node);

        match node {
            Pattern::LiteralExpr(literal_expr) => {
                Ok(ast::Pattern::Literal(self.visit_literal_expr(literal_expr)))
            }
            Pattern::Name(name) => self
                .visit_name(name)
                .map(Spanned::unwrap)
                .map(ast::Pattern::Name),
            Pattern::ConsPattern(pat) => {
                let head = self.visit_pattern(pat.head()?).map(Box::new)?;
                let tail = self.visit_pattern(pat.tail()?).map(Box::new)?;

                Ok(ast::Pattern::Cons { head, tail })
            }
            Pattern::TupleConstructorPattern(constr_pat) => {
                let name = self.visit_name(constr_pat.name()?)?;

                let elems = {
                    let mut elems = Vec::new();
                    let mut cursor = constr_pat.walk();

                    for elem in constr_pat.payload()?.patterns(&mut cursor) {
                        let elem = self.visit_pattern(elem?)?;
                        elems.push(elem);
                    }

                    elems.into_boxed_slice()
                };

                Ok(ast::Pattern::TupleConstr { name, elems })
            }
            Pattern::ListPattern(list_pattern) => {
                let mut pats = Vec::new();
                let mut cursor = node.walk();

                for pat in list_pattern.patterns(&mut cursor) {
                    let pat = self.visit_pattern(pat?)?;
                    pats.push(pat);
                }

                Ok(ast::Pattern::List(pats.into_boxed_slice()))
            }
            Pattern::TuplePattern(tuple_pattern) => {
                let mut pats = Vec::new();
                let mut cursor = node.walk();

                for pat in tuple_pattern.patterns(&mut cursor) {
                    let pat = self.visit_pattern(pat?)?;
                    pats.push(pat);
                }

                Ok(ast::Pattern::Tuple(pats.into_boxed_slice()))
            }
            Pattern::ParenthesizedPattern(paren_pattern) => self
                .visit_pattern(paren_pattern.inner()?)
                .map(Box::new)
                .map(ast::Pattern::Paren),
            Pattern::RecordPattern(record_pattern) => {
                let name = self.visit_name(record_pattern.name()?)?;

                let mut fields = Vec::new();
                let mut rest = None;

                if let Some(Ok(field_iter)) = record_pattern.fields() {
                    let mut cursor = record_pattern.walk();

                    for field in field_iter.children(&mut cursor) {
                        match field? {
                            RpfRp::RecordPatternField(field) => {
                                let field =
                                    self.visit_record_pattern_field(field)?;

                                fields.push(field);
                            }
                            RpfRp::RestPattern(rest_pattern) => {
                                // this is fine because the rest_pattern can
                                // only appear at most once
                                let span = node_span(rest_pattern);
                                rest = Some(span);
                            }
                        }
                    }
                }

                let fields = fields.into_boxed_slice();
                Ok(ast::Pattern::Record { name, fields, rest })
            }
            Pattern::WildcardPattern(_) => Ok(ast::Pattern::Wildcard),
        }
        .map(|pattern| span.with(pattern))
    }

    fn visit_record_pattern_field(
        &self,
        node: RecordPatternField<'a>,
    ) -> CstResult<'a, Spanned<ast::RecordPatternField>> {
        let span = node_span(node);
        let field = self.visit_ident(node.field()?);
        let pattern = node
            .pattern()
            .transpose()?
            .map(|pat| self.visit_pattern(pat))
            .transpose()?;

        Ok(span.with(ast::RecordPatternField { field, pattern }))
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
                .map(Spanned::unwrap)
                .map(ast::Ty::Name),
            TypeExpr::FnType(fn_type) => {
                self.visit_fn_type(fn_type).map(Spanned::unwrap)
            }
            TypeExpr::GenericType(generic_type) => {
                self.visit_generic_type(generic_type).map(Spanned::unwrap)
            }
            TypeExpr::InferredType(_) => Ok(ast::Ty::Infer),
            TypeExpr::ParenthesizedType(paren_type) => self
                .visit_type(paren_type.inner()?)
                .map(Box::new)
                .map(ast::Ty::Paren),
            TypeExpr::PrimitiveType(primitive_type) => {
                self.visit_prim_type(primitive_type).map(ast::Ty::Prim)
            }
            TypeExpr::TupleType(tuple_type) => {
                self.visit_tuple_type(tuple_type).map(ast::Ty::Tuple)
            }
            TypeExpr::UnitType(_) => Ok(ast::Ty::Prim(ast::PrimTy::Unit)),
        }
        .map(|ty| span.with(ty))
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
            TeFta::TypeExpr(type_expr) => self
                .visit_type(type_expr)
                .map(|spanned| spanned.item)
                .map(ast::FnTyArgs::NoParens),
            TeFta::FnTypeArgs(fn_type_args) => {
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
        let name = self.visit_name(node.name()?)?;

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

    fn visit_name(&self, node: Name<'a>) -> CstResult<'a, Spanned<ast::Name>> {
        let span = node_span(node);
        match node {
            Name::Ident(_) => Ok(span.with(ast::Name::Ident)),
            Name::Path(path) => self.visit_path(path),
            Name::Self_(_) => Ok(span.with(ast::Name::Path(
                Some(span.with(ast::Qualifier::Self_)),
                [].into(),
            ))),
            Name::Super(_) => Ok(span.with(ast::Name::Path(
                Some(span.with(ast::Qualifier::Super)),
                [].into(),
            ))),
            Name::Package(_) => Ok(span.with(ast::Name::Path(
                Some(span.with(ast::Qualifier::Package)),
                [].into(),
            ))),
        }
    }

    fn visit_path(&self, node: Path<'a>) -> CstResult<'a, Spanned<ast::Name>> {
        fn path_rec<'a>(
            visitor: &CstVisitor<'a>,
            node: Name<'a>,
            elems: &mut Vec<Spanned<ast::Ident>>,
        ) -> CstResult<'a, Option<Spanned<ast::Qualifier>>> {
            match node {
                Name::Ident(ident) => {
                    elems.push(visitor.visit_ident(ident));
                    Ok(None)
                }
                Name::Path(path) => {
                    let root = path.root()?;
                    let name = path.name()?;
                    let qual = path_rec(visitor, root, elems)?;
                    elems.push(visitor.visit_ident(name));
                    Ok(qual)
                }
                Name::Self_(self_) => {
                    let span = node_span(self_);
                    Ok(Some(span.with(ast::Qualifier::Self_)))
                }
                Name::Super(super_) => {
                    let span = node_span(super_);
                    Ok(Some(span.with(ast::Qualifier::Super)))
                }
                Name::Package(package) => {
                    let span = node_span(package);
                    Ok(Some(span.with(ast::Qualifier::Package)))
                }
            }
        }

        let root = node.root()?;
        let name = node.name()?;

        let mut elems = Vec::new();
        let qual = path_rec(self, root, &mut elems)?;
        elems.push(self.visit_ident(name));

        let span = node_span(node);
        Ok(span.with(ast::Name::Path(qual, elems.into_boxed_slice())))
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
    use crate::file::File;

    use super::{ast, Parser};

    #[test]
    fn fake_ref_module() {
        let source = File::fake(
            r#"
            //! Mutable reference cells

            /// A mutable reference cell.
            @core.lang_item
            pub type Ref[T] = Ref { mutable contents : T }

            /// Constructs a new `Ref[T]` with the given `contents`.
            pub fn ref(contents: T) -> Ref[T] = Ref { contents }

            /// Returns the value stored in `ref`.
            ///
            /// This function is equivalent to the prefix `*` operator.
            @core.lang_item
            @core.operator.deref
            pub fn deref(ref: Ref[T]) -> T = ref.contents

            /// Replaces the contents of `ref` with the given `value`.
            ///
            /// This function is equivalent to the infix `:=` operator.
            @core.lang_item
            @core.operator.walrus
            pub fn update(ref: Ref[T], value: T) {
                ref.contents <- value;
            }
            "#,
        );

        let mut parser = Parser::new().unwrap();
        let cst = parser.parse(&source).unwrap();
        let ast = ast::Ast::try_from(cst).unwrap();

        assert!(ast.shebang().is_none());
        assert!(ast.module_comment().is_some());

        let decls = ast.decls();
        assert_eq!(decls.len(), 4);

        let ref_struct = decls.first().unwrap();
        assert!(ref_struct.item.doc_comment.is_some());
        assert_eq!(ref_struct.item.attributes.len(), 1);
        assert!(matches!(
            ref_struct.item.visibility,
            ast::Visibility::Pub(_)
        ));
    }

    #[test]
    fn fake_result_module() {
        let source = File::fake(
            r#"
    //! Results representing fallible computations

    /// A `Result` that may be `Ok` or an `Err`.
    @core.lang_item
    pub type Result[T, E] =
        | @core.lang_item
          /// Represents a successful computation.
          Ok(T)
        | @core.lang_item
          /// Represents a failed computation.
          Err(E)

    /// A `Result` which can only be `Ok`.
    pub type alias Always[T]    = Result[T, !]
    /// A `Result` which can only be `Err`.
    pub type alias AlwaysErr[E] = Result[!, E]

    pub fn map(res: Result[T, E], f: T -> U) = match res {
        Result.Ok(x)  => Result.Ok(f(x)),
        Result.Err(e) => Result.Err(e),
    }

    pub fn map_err(res: Result[T, E], f: E -> U) = match res {
        Result.Ok(x)  => Result.Ok(x),
        Result.Err(e) => Result.Err(f(e)),
    }

    pub fn unwrap(res: Result[T, E]) -> T = match res {
        Result.Ok(x) => x,
        _ => panic(),
    }
            "#,
        );

        let mut parser = Parser::new().unwrap();
        let cst = parser.parse(&source).unwrap();
        let ast = ast::Ast::try_from(cst).unwrap();

        assert!(ast.shebang().is_none());
        assert!(ast.module_comment().is_some());

        let decls = ast.decls();
        assert_eq!(decls.len(), 6);
    }
}
