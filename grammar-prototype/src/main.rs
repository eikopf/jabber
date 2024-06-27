use lalrpop_util::lalrpop_mod;

mod ast;

lalrpop_mod!(pub calculator);

fn main() {
    println!("Hello, world!");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn calculator_test() {
        assert!(calculator::TermParser::new().parse("22").is_ok());
        assert!(calculator::TermParser::new().parse("((22))").is_ok());
    }
}
