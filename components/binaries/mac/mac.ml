(*
    ||M||  This file is part of HELM, an Hypertextual, Electronic        
    ||A||  Library of Mathematics, developed at the Computer Science     
    ||T||  Department, University of Bologna, Italy.                     
    ||I||                                                                
    ||T||  HELM is free software; you can redistribute it and/or         
    ||A||  modify it under the terms of the GNU General Public License   
    \   /  version 2 or (at your option) any later version.      
     \ /   This software is distributed as is, NO WARRANTY.     
      V_______________________________________________________________ *)

module A = Arg
module P = Printf

module O = Options 
module L = Lexer

let help   = "Usage: mac [ -LXQV | -p <int> ]* [ <file> ]*"
let help_L = " Activate lexer debugging"
let help_Q = " Read data from standard input"
let help_V = " Show version information"
let help_X = " Reset options and counters"
let help_p = "<int> Assume <int> characters per page (default: 5120)"

let active = ref false

let process_channel ich =
   let lexbuf = Lexing.from_channel ich in
   L.token lexbuf; active := true

let output_version () =
   P.printf "mac 0.1.1 M - July 2013\n"

let process_stdin () =
   process_channel stdin

let process_file fname =
   let ich = open_in fname in
   process_channel ich; close_in ich

let set_page i =
   if i > 0 then O.page := i

let output_count () =
   if !active then
      let pages = !O.count / !O.page in
      let pages = if !O.count mod !O.page = 0 then pages else succ pages in
      P.printf "%u %u\n" !O.count pages

let main () =
   A.parse [
      "-L", A.Set O.debug_lexer, help_L;
      "-Q", Arg.Unit process_stdin, help_Q; 
      "-V", Arg.Unit output_version, help_V; 
      "-X", A.Unit O.clear, help_X;
   ] process_file help;
   output_count ()

let _ = main ()
