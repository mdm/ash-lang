mod regex;

enum TokenClass {
    Identifier,
    StringLiteral,
    IntegerLiteral,
    FloatLiteral,
    Operator,
    Separator,
    EndOfInput,
}

struct DottedItem {
    token_class: TokenClass,
    dot: usize,
}

struct TransitionTable {
    base: Vec<usize>, // TODO: do we need HasshMaps here if we want to support arbitrary Unicode chars?
    next: Vec<usize>,
    check: Vec<usize>,
    default: Vec<usize>,
}

struct Lexer {
    states: Vec<DottedItem>,
    transitions: TransitionTable,
}
