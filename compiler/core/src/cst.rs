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
    span::{Span, SpanBox, SpanSeq, Spanned},
};

use nodes::{
    anon_unions::{
        EmptyStmt_ExprStmt_LetStmt as EsEsLs, Ident_Parameters,
        Ident_TupleField as ITf, RestPattern_StructPatternField as RpSpf,
        StructExprField_StructUpdateBase as SefSub,
        TypeExpr_FnTypeArgs as TeFta,
    },
    AccessSpec, Attribute, AttributeArgument, Attributes, BinaryOperator,
    Block, Decl, DocComments, Expr, FnType, GenericParams, GenericType, Ident,
    LiteralExpr, MatchArms, Name, Parameters, Path, Pattern, PrefixOperator,
    PrimitiveType, SourceFile, StructExprFields, TupleType, TypeDecl, TypeExpr,
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

#[derive(Debug, Clone, Copy, Error)]
pub enum ParseError {
    #[error("")]
    Error { parent_kind: &'static str },
    #[error("")]
    Missing { parent_kind: &'static str },
}

impl<'a> TryFrom<Cst<'a>> for ast::Ast<'a> {
    type Error = ParseError;

    fn try_from(value: Cst<'a>) -> Result<Self, Self::Error> {
        value.build_ast()
    }
}

impl<'a> Cst<'a> {
    fn build_ast(self) -> Result<ast::Ast<'a>, ParseError> {
        // TODO: walk the raw tree for error/missing nodes and emit
        // appropriate ParseErrors if they exist

        let visitor = self.visitor();
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
            AttributeArgument::LiteralExpr(literal_expr) => {
                Ok(ast::AttrArg::Literal(self.visit_literal_expr(literal_expr)))
                    .map(|arg| span.with(arg))
            }
            AttributeArgument::Name(name) => self
                .visit_name(name)
                .map(ast::AttrArg::Name)
                .map(|name| span.with(name)),
        }
    }

    // EXPRESSIONS

    fn visit_expr(&self, node: Expr<'a>) -> CstResult<'a, Spanned<ast::Expr>> {
        let span = node_span(node);

        match node {
            Expr::Ident(_) => Ok(span.with(ast::Expr::Name(ast::Name::Ident))),
            Expr::Path(path) => self
                .visit_path(path)
                .map(ast::Name::Path)
                .map(ast::Expr::Name)
                .map(|expr| span.with(expr)),
            Expr::LiteralExpr(literal_expr) => {
                Ok(ast::Expr::Literal(self.visit_literal_expr(literal_expr)))
                    .map(|expr| span.with(expr))
            }
            Expr::PrefixExpr(prefix_op) => {
                let operand =
                    self.visit_expr(prefix_op.operand()?).map(Box::new)?;
                let operator =
                    self.visit_prefix_operator(prefix_op.operator()?);

                Ok(span.with(ast::Expr::Prefix { operand, operator }))
            }
            Expr::BinaryExpr(binary_op) => {
                let lhs = self.visit_expr(binary_op.lhs()?).map(Box::new)?;
                let rhs = self.visit_expr(binary_op.rhs()?).map(Box::new)?;
                let operator =
                    self.visit_binary_operator(binary_op.operator()?);

                Ok(span.with(ast::Expr::Binary { lhs, operator, rhs }))
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

                Ok(span.with(ast::Expr::Call { callee, args }))
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

                Ok(span.with(ast::Expr::Field { item, field }))
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

                Ok(span.with(ast::Expr::IfElse {
                    condition,
                    consequence,
                    alternative,
                }))
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

                Ok(span.with(ast::Expr::Lambda { params, body }))
            }
            Expr::MatchExpr(match_expr) => {
                let arms = self.visit_match_arms(match_expr.arms()?)?;
                let scrutinee =
                    self.visit_expr(match_expr.scrutinee()?).map(Box::new)?;

                Ok(span.with(ast::Expr::Match { scrutinee, arms }))
            }
            Expr::StructExpr(struct_expr) => {
                let name = {
                    let span = node_span(struct_expr.name());
                    let name = self.visit_name(struct_expr.name()?)?;
                    span.with(name)
                };

                let (fields, base) = struct_expr
                    .fields()
                    .transpose()?
                    .map(|fields| self.visit_struct_expr_fields(fields))
                    .transpose()?
                    .unwrap_or_else(|| (Box::new([]), None));

                Ok(span.with(ast::Expr::Struct { name, fields, base }))
            }
            Expr::TupleExpr(tuple_expr) => {
                let mut exprs = Vec::new();
                let mut cursor = tuple_expr.walk();

                for expr in tuple_expr.exprs(&mut cursor) {
                    let expr = self.visit_expr(expr?)?;
                    exprs.push(expr);
                }

                Ok(span.with(ast::Expr::Tuple(exprs.into_boxed_slice())))
            }
            Expr::ListExpr(list_expr) => {
                let mut exprs = Vec::new();
                let mut cursor = list_expr.walk();

                for expr in list_expr.exprs(&mut cursor) {
                    let expr = self.visit_expr(expr?)?;
                    exprs.push(expr);
                }

                Ok(span.with(ast::Expr::List(exprs.into_boxed_slice())))
            }
            Expr::ParenthesizedExpr(paren_expr) => {
                let inner =
                    self.visit_expr(paren_expr.inner()?).map(Box::new)?;

                Ok(span.with(ast::Expr::Paren(inner)))
            }
            Expr::Block(block) => self
                .visit_block(block)
                .map(|Spanned { item, .. }| ast::Expr::Block(Box::new(item)))
                .map(|expr| span.with(expr)),
        }
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

    fn visit_struct_expr_fields(
        &self,
        node: StructExprFields<'a>,
    ) -> CstResult<
        'a,
        (SpanSeq<ast::StructExprField>, Option<SpanBox<ast::Expr>>),
    > {
        let mut fields = Vec::new();
        let mut base = None;

        let mut cursor = node.walk();
        for field in node.children(&mut cursor) {
            match field? {
                SefSub::StructUpdateBase(struct_update_base) => {
                    // this is fine because the "..base" field can only
                    // appear once
                    let expr = self.visit_expr(struct_update_base.expr()?)?;
                    base = Some(Box::new(expr));
                }
                SefSub::StructExprField(struct_expr_field) => {
                    let span = node_span(struct_expr_field);
                    let name = self.visit_ident(struct_expr_field.name()?);
                    let value = struct_expr_field
                        .value()
                        .transpose()?
                        .map(|expr| self.visit_expr(expr))
                        .transpose()?;

                    fields
                        .push(span.with(ast::StructExprField { name, value }));
                }
            }
        }

        Ok((fields.into_boxed_slice(), base))
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
                    .map(|pat| span.with(pat))
            }
            Pattern::Name(name) => self
                .visit_name(name)
                .map(ast::Pattern::Name)
                .map(|pat| span.with(pat)),
            Pattern::ConsPattern(cons_pattern) => {
                let span = node_span(cons_pattern);
                let head =
                    self.visit_pattern(cons_pattern.head()?).map(Box::new)?;
                let tail =
                    self.visit_pattern(cons_pattern.tail()?).map(Box::new)?;

                Ok(span.with(ast::Pattern::Cons { head, tail }))
            }
            Pattern::EnumPattern(enum_pattern) => {
                let name = {
                    let span = node_span(enum_pattern.name());
                    let name = self.visit_name(enum_pattern.name()?)?;
                    span.with(name)
                };

                let elems = {
                    let mut elems = Vec::new();
                    let mut cursor = node.walk();

                    for pat in enum_pattern.payload()?.patterns(&mut cursor) {
                        let pat = self.visit_pattern(pat?)?;
                        elems.push(pat);
                    }

                    elems.into_boxed_slice()
                };

                Ok(span.with(ast::Pattern::Enum { name, elems }))
            }
            Pattern::ListPattern(list_pattern) => {
                let mut pats = Vec::new();
                let mut cursor = node.walk();

                for pat in list_pattern.patterns(&mut cursor) {
                    let pat = self.visit_pattern(pat?)?;
                    pats.push(pat);
                }

                Ok(span.with(ast::Pattern::List(pats.into_boxed_slice())))
            }
            Pattern::TuplePattern(tuple_pattern) => {
                let mut pats = Vec::new();
                let mut cursor = node.walk();

                for pat in tuple_pattern.patterns(&mut cursor) {
                    let pat = self.visit_pattern(pat?)?;
                    pats.push(pat);
                }

                Ok(span.with(ast::Pattern::Tuple(pats.into_boxed_slice())))
            }
            Pattern::ParenthesizedPattern(paren_pattern) => self
                .visit_pattern(paren_pattern.inner()?)
                .map(Box::new)
                .map(ast::Pattern::Paren)
                .map(|pat| span.with(pat)),
            Pattern::StructPattern(struct_pattern) => {
                let name = {
                    let span = node_span(struct_pattern.name());
                    let name = self.visit_name(struct_pattern.name()?)?;
                    span.with(name)
                };

                // yes, this is hideous.
                let (fields, rest) = {
                    let mut fields = Vec::new();
                    let mut rest = None;

                    if let Some(pat_fields) =
                        struct_pattern.fields().transpose()?
                    {
                        let mut cursor = node.walk();

                        for field in pat_fields.children(&mut cursor) {
                            match field? {
                                RpSpf::RestPattern(rest_pattern) => {
                                    // this is fine, since the rest_pattern
                                    // can only appear once
                                    rest = Some(node_span(rest_pattern))
                                }
                                RpSpf::StructPatternField(sp_field) => {
                                    let span = node_span(sp_field);
                                    let field =
                                        self.visit_ident(sp_field.field()?);
                                    let pattern = sp_field
                                        .pattern()
                                        .transpose()?
                                        .map(|pat| self.visit_pattern(pat))
                                        .transpose()?;

                                    fields.push(span.with(
                                        ast::StructPatternField {
                                            field,
                                            pattern,
                                        },
                                    ))
                                }
                            }
                        }
                    }

                    (fields.into_boxed_slice(), rest)
                };

                Ok(span.with(ast::Pattern::Struct { name, fields, rest }))
            }
            Pattern::WildcardPattern(_) => {
                Ok(ast::Pattern::Wildcard).map(|pat| span.with(pat))
            }
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
    use crate::file::File;

    use super::{ast, Parser};

    #[test]
    fn type_decl_full_file() {
        let source = File::fake(
            r#"
            #! a shebang line

            // random comment

            //! module comment

            // second random comment
            // including this second line

            /// some documentation for Always
            @an.attribute(true, 0xFAFD, "hello, world")
            pub type Always[T] = std.Result[T, !]

            // third random comment
            "#,
        );

        let mut parser = Parser::new().unwrap();
        let cst = parser.parse(&source).unwrap();
        let ast = ast::Ast::try_from(cst).unwrap();

        assert!(ast.shebang().is_some());
        assert!(ast.module_comment().is_some());
        assert_eq!(ast.comments().len(), 3);
        assert_eq!(ast.decls().len(), 1);

        let type_decl = ast.decls().first().unwrap();
        assert!(matches!(type_decl.item.kind, ast::DeclKind::Type { .. }));
        assert!(type_decl.item.doc_comment.is_some());
        assert_eq!(type_decl.item.attributes.len(), 1);

        let attr = type_decl.item.attributes.first().unwrap().item();
        match attr.name.item() {
            ast::Name::Ident => panic!(),
            ast::Name::Path(path) => assert_eq!(path.len(), 2),
        }
    }
}
