module A = Arg
module P = Printf

module O = Options 
module L = Lexer

let help   = "Usage: mac [ -LX ]* [ <file> ]*"
let help_L = " Activate lexer debugging"
let help_Q = " Read data from standard input"
let help_V = " Show version information"
let help_X = " Reset options and counters"

let active = ref false

let process_channel ich =
   let lexbuf = Lexing.from_channel ich in
   L.token lexbuf; active := true

let output_version () =
   P.printf "mac 0.1.0 M - November 2012\n"

let process_stdin () =
   process_channel stdin

let process_file fname =
   let ich = open_in fname in
   process_channel ich; close_in ich

let output_count () =
   if !active then P.printf "%u\n" !O.count

let main () =
   A.parse [
      "-L", A.Set O.debug_lexer, help_L;
      "-Q", Arg.Unit process_stdin, help_Q; 
      "-V", Arg.Unit output_version, help_V; 
      "-X", A.Unit O.clear, help_X;
   ] process_file help;
   output_count ()

let _ = main ()
