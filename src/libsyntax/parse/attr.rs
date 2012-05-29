import either::{either, left, right};
import ast_util::spanned;
import common::{parser_common, seq_sep};

export attr_or_ext;
export parser_attr;

// A type to distingush between the parsing of item attributes or syntax
// extensions, which both begin with token.POUND
type attr_or_ext = option<either<[ast::attribute], @ast::expr>>;


type parser_attr = int;
/*impl parser_attr<L: lexer> for parser<L> {

}*/

//
// Local Variables:
// mode: rust
// fill-column: 78;
// indent-tabs-mode: nil
// c-basic-offset: 4
// buffer-file-coding-system: utf-8-unix
// End:
//
