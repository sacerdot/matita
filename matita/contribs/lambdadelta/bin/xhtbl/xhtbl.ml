module A = Arg
module F = Filename
module L = List

module O  = Options 
module TP = TextParser
module TL = TextLexer
module TU = TextUnparser
module P1 = Pass1
module P2 = Pass2
module P3 = Pass3
module M  = Matrix
module XU = XmlUnparser

let help    = "Usage: xhtbl [ -LX | -O <dir> | -d0 | -d1 | -d2 | -e1 | -e2 | -p0 | -p1 | -p2 | <file> ]*"
let help_L  = " Output lexer tokens"
let help_O  = "<dir>  Set this output directory"
let help_X  = " Clear all options"
let help_b  = "<uri>  Set this base uri for relative links"
let help_d0 = " Output table contents after phase zero (parsing)"
let help_d1 = " Output table contents after phase one (sizing)"
let help_d2 = " Output table contents after phase two (filling)"
let help_e1 = " Disabled"
let help_e2 = " Output debug information during phase two (filling)"
let help_p0 = " Process until phase zero (parsing)"
let help_p1 = " Process until phase one (sizing)"
let help_p2 = " Process until phase two (filling)"

let hook = "xhtbl"

let includes, tables = ref [], ref []

let process_directive och bname (name, table, css, uri, ext) =
   tables := name :: !tables;
   if !O.d0 then TU.debug table;
   if not !O.p0 then begin
      let size = P1.process table in
      if !O.d1 then TU.debug table;
      if not !O.p1 then begin
         let matrix = M.make size in
         let _ = P2.process table matrix in
         if !O.d2 then TU.debug table;
         if not !O.p2 then P3.process css uri ext matrix;
	 let name = if name = "" then bname else name in
         XU.output och name matrix
      end
   end

let process_file fname =
   let bname = F.chop_extension (F.basename fname) in
   let ich = open_in fname in
   let lexbuf = Lexing.from_channel ich in
   let ns, ds = TP.script TL.token lexbuf in
   close_in ich; includes := bname :: !includes;
   let ns = ("", "http://www.w3.org/1999/xhtml") :: ns in
   let och = XU.open_out bname ns in 
   L.iter (process_directive och bname) ds;
   XU.close_out och

let main () =
   A.parse [
      "-L", A.Set O.debug_lexer, help_L;
      "-O", A.String ((:=) O.output_dir), help_O; 
      "-X", A.Unit O.clear, help_X;
      "-b", A.String ((:=) O.baseuri), help_b;
      "-d0", A.Set O.d0, help_d0;  
      "-d1", A.Set O.d1, help_d1;  
      "-d2", A.Set O.d2, help_d2;  
      "-e1", A.Set O.e1, help_e1;  
      "-e2", A.Set O.e2, help_e2;  
      "-p0", A.Set O.p0, help_p0;  
      "-p1", A.Set O.p1, help_p1;  
      "-p2", A.Set O.p2, help_p2;  
   ] process_file help;
   XU.write_hook hook !includes !tables 

let _ = main ()
