use lalrpop_util::lalrpop_mod;

mod ast;

lalrpop_mod!(pub calculator);
lalrpop_mod!(pub prototype);

fn main() {
    println!("Hello, world!");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ident() {
        assert!(prototype::IdentParser::new().parse("PascalCase").is_ok());
        assert!(prototype::IdentParser::new().parse("snake_case").is_ok());
        assert!(prototype::IdentParser::new().parse("__private").is_ok());

        // the wildcard pattern isn't an identifier, and multiple
        // consecutive underscores are also disallowed
        assert!(prototype::IdentParser::new().parse("_").is_err());
        assert!(prototype::IdentParser::new().parse("___").is_err());
    }

    #[test]
    fn name() {
        assert!(prototype::NameParser::new().parse("Item").is_ok());
        assert!(prototype::NameParser::new()
            .parse("qualified.Item")
            .is_ok());
        assert!(prototype::NameParser::new()
            .parse("mangled.Symbol.")
            .is_err());
    }

    #[test]
    fn prim_nums() {
        // floats
        assert!(prototype::PrimFloatParser::new().parse("f32").is_ok());
        assert!(prototype::PrimFloatParser::new().parse("f64").is_ok());

        // unsigned integers
        assert!(prototype::PrimIntParser::new().parse("u8").is_ok());
        assert!(prototype::PrimIntParser::new().parse("u16").is_ok());
        assert!(prototype::PrimIntParser::new().parse("u32").is_ok());
        assert!(prototype::PrimIntParser::new().parse("u64").is_ok());

        // signed integers
        assert!(prototype::PrimIntParser::new().parse("i8").is_ok());
        assert!(prototype::PrimIntParser::new().parse("i16").is_ok());
        assert!(prototype::PrimIntParser::new().parse("i32").is_ok());
        assert!(prototype::PrimIntParser::new().parse("i64").is_ok());
    }

    #[test]
    fn prim_types() {
        assert!(prototype::PrimTyParser::new().parse("!").is_ok());
        assert!(prototype::PrimTyParser::new().parse("()").is_ok());
        assert!(prototype::PrimTyParser::new().parse("bool").is_ok());
        assert!(prototype::PrimTyParser::new().parse("char").is_ok());
        assert!(prototype::PrimTyParser::new().parse("string").is_ok());

        // numeric primitive types
        assert!(prototype::PrimTyParser::new().parse("i16").is_ok());
        assert!(prototype::PrimTyParser::new().parse("u8").is_ok());
        assert!(prototype::PrimTyParser::new().parse("u32").is_ok());
        assert!(prototype::PrimTyParser::new().parse("f64").is_ok());
    }

    #[test]
    fn generic_params() {
        // empty lists aren't allowed
        assert!(prototype::GenericParamsParser::new().parse("[]").is_err());
        assert!(prototype::GenericParamsParser::new().parse("[|]").is_err());

        assert!(prototype::GenericParamsParser::new()
            .parse("[A, B]")
            .is_ok());

        // trailing commas aren't allowed
        assert!(prototype::GenericParamsParser::new()
            .parse("[A, B, ]")
            .is_err());

        assert!(prototype::GenericParamsParser::new()
            .parse("[A, B | C, D]")
            .is_ok());

        assert!(prototype::GenericParamsParser::new()
            .parse("[A[F], B, C | D[G, H], E]")
            .is_ok());
    }

    #[test]
    fn types() {
        // primitive types
        assert!(prototype::TyParser::new()
            .parse("()")
            .is_ok_and(|ty| matches!(ty, ast::Ty::Prim(ast::PrimTy::Unit))));

        assert!(prototype::TyParser::new()
            .parse("!")
            .is_ok_and(|ty| matches!(ty, ast::Ty::Prim(ast::PrimTy::Bottom))));

        assert!(prototype::TyParser::new()
            .parse("string")
            .is_ok_and(|ty| matches!(ty, ast::Ty::Prim(ast::PrimTy::String))));

        // named types
        assert!(prototype::TyParser::new()
            .parse("T[A, B[C[D]]]")
            .is_ok_and(|ty| matches!(ty, ast::Ty::Name(_, _))));

        // function types
        assert!(prototype::TyParser::new()
            .parse("A -> B")
            .is_ok_and(|ty| matches!(ty, ast::Ty::Func(_, _))));

        // condition checks if -> is right-associative
        assert!(prototype::TyParser::new()
            .parse("A -> B -> C")
            .is_ok_and(|ty| matches!(ty, 
                ast::Ty::Func(_, right) if matches!(*right, 
                    ast::Ty::Func(_, _)))));

        // condition checks if -> is right-associative
        assert!(prototype::TyParser::new()
            .parse("(A -> B) -> C")
            .is_ok_and(|ty| matches!(ty, 
                ast::Ty::Func(left, _) if matches!(*left, 
                    ast::Ty::Func(_, _)))));

        assert!(prototype::TyParser::new()
            .parse("(A, B, C, D)")
            .is_ok_and(|ty| matches!(ty, ast::Ty::Tuple(_))));
    }


    #[test]
    fn num_literal_digits() {
       assert!(prototype::NumLiteralDigitsParser::new()
           .parse("123")
           .is_ok_and(|digits| matches!(digits, ast::NumLiteralDigits::Int(123u64)))); 

       assert!(prototype::NumLiteralDigitsParser::new()
           .parse("123.")
           .is_ok_and(|digits| matches!(digits, ast::NumLiteralDigits::IntDot(123u64)))); 

       assert!(prototype::NumLiteralDigitsParser::new()
           .parse(".123")
           .is_ok_and(|digits| matches!(digits, ast::NumLiteralDigits::Frac(123u64)))); 

       assert!(prototype::NumLiteralDigitsParser::new()
           .parse("123.456")
           .is_ok_and(|digits| matches!(digits, ast::NumLiteralDigits::Real { int: 123u64, frac: 456u64 }))); 
    }

    #[test]
    fn num_literals() {
        // passing examples
        let examples = vec![
           (".0f32", ast::NumLiteral { 
               digits: ast::NumLiteralDigits::Frac(0u64), 
               suffix: Some(ast::PrimNum::Float(ast::PrimFloat::F32)),
           }),

           (".367u8", ast::NumLiteral { 
               digits: ast::NumLiteralDigits::Frac(367u64), 
               suffix: Some(ast::PrimNum::Int(ast::PrimInt::U8)),
           }),

           ("123.367i64", ast::NumLiteral { 
               digits: ast::NumLiteralDigits::Real { int: 123u64, frac: 367u64 }, 
               suffix: Some(ast::PrimNum::Int(ast::PrimInt::I64)),
           }),
       ]; 

       let parser = prototype::NumLiteralParser::new();

       for (src, lit) in examples {
           assert_eq!(parser.parse(src), Ok(lit));
       };
    }

    #[test]
    fn patterns() {
        // testing a large composite pattern (ignoring the fact that this wouldn't type check)
        assert!(prototype::PatternParser::new()
            .parse("[a :: b :: c, _, (), \"foo\"]")
            .is_ok_and(|pat| matches!(
                    pat,
                    // the pattern is a list
                    ast::Pattern::List(elems)
                    // with four elements
                    if elems.len() == 4
                    // the first element is a cons pattern whose rhs is also a cons pattern
                    && matches!(&elems[0], ast::Pattern::Cons(_, rhs) if matches!(**rhs, ast::Pattern::Cons(_, _))) 
                    // the second element is a wildcard pattern
                    && matches!(elems[1], ast::Pattern::Wildcard)
                    // the third element is a literal unit
                    && matches!(elems[2], ast::Pattern::Literal(ast::AtomicLiteral::Unit))
                    // the fourth element is a literal string whose value is "foo"
                    && matches!(&elems[3], ast::Pattern::Literal(ast::AtomicLiteral::String(foo)) if **foo == *"foo"))));
    }
}
