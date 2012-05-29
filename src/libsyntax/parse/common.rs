import std::map::{hashmap};
import ast_util::spanned;
import parser::parser;
import lexer::lexer;

type seq_sep = {
    sep: option<token::token>,
    trailing_opt: bool   // is trailing separator optional?
};

fn seq_sep(t: token::token) -> seq_sep {
    ret {sep: option::some(t), trailing_opt: false};
}
fn seq_sep_opt(t: token::token) -> seq_sep {
    ret {sep: option::some(t), trailing_opt: true};
}
fn seq_sep_none() -> seq_sep {
    ret {sep: option::none, trailing_opt: false};
}


fn token_to_str<L: lexer>(reader: L, token: token::token) -> str {
    token::to_str(*reader.interner(), token)
}


// This should be done with traits, once traits work
/*impl parser_common<L: lexer> for parser<L> {


}*/
type parser_common = int;
