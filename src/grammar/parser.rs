use pest::Parser;
use pest_derive::Parser;

#[derive(Parser)]
#[grammar = "grammar.pest"]
struct RawParser;

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_parse() {
        dbg!(RawParser::parse(Rule::nat_literal, "2345").unwrap());
        // dbg!(RawParser::parse(Rule::fun_args, "a: Nat").unwrap());
        dbg!(RawParser::parse(
            Rule::program,
            "def foo(a: Nat, b: Nat) = 5 * 2 + 3 * 4 + let x = 5 * 2 in x + y * let y = 5 in x * y"
        )
        .unwrap());
    }
}
