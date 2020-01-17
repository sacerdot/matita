let output_dir_default = ""

let baseuri_default = ""

let debug_lexer_default = false

let debug_pass_default = false

let pass_default = false

let output_dir = ref output_dir_default

let baseuri = ref baseuri_default

let debug_lexer = ref debug_lexer_default

let d0 = ref debug_pass_default

let d1 = ref debug_pass_default

let d2 = ref debug_pass_default

let e1 = ref debug_pass_default

let e2 = ref debug_pass_default

let p0 = ref pass_default

let p1 = ref pass_default

let p2 = ref pass_default

let clear () =
   output_dir := output_dir_default;
   baseuri := baseuri_default;
   debug_lexer := debug_lexer_default;
   d0 := debug_pass_default; d1 := debug_pass_default; d2 := debug_pass_default; 
   e1 := debug_pass_default; e2 := debug_pass_default;
   p0 := pass_default; p1 := pass_default; p2 := pass_default
