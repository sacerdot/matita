let debug_lexer_default = false

let count_default = 0

let debug_lexer = ref debug_lexer_default

let count = ref count_default

let clear () =
   debug_lexer := debug_lexer_default;
   count := count_default
