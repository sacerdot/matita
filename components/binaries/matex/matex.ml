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
module F = Filename

module U = NUri
module R = Helm_registry
module L = Librarian

module X = Ground
module G = Options
module E = Engine
module O = TeXOutput
module K = Kernel

let help_O = "<dir> Set this output directory"
let help_X = " Clear configuration and options"
let help_a = " Log alpha-unconverted identifiers (default: no)"
let help_g = " Global alpha-conversion (default: no)"
let help_l = "<file> Output the list of generated files in this file"
let help_m = " Log missing notational macros (default: no)"
let help_p = " Omit types (default: no)"
let help_t = " Test term transformations (default: no)"

let help   = ""

(* internal functions *******************************************************)

let alpha_decode = R.triple R.string R.string R.string

let macro_decode = R.triple R.string R.string R.int

let init registry =
   R.load_from registry; 
   if !G.no_init then begin
      K.init ();
      G.no_init := false;
   end;
   G.alpha_type := R.get_list alpha_decode "matex.alpha.type";
   G.alpha_sort := R.get_list alpha_decode "matex.alpha.sort";
   G.macro_gref := R.get_list macro_decode "matex.notation.const"

let is_registry s =
   F.check_suffix s ".conf.xml"

let no_init () =
   failwith "MaTeX: main: registry not initialized" 

let malformed s =
   failwith ("MaTeX: main: malformed argument: " ^ s)

let set_list fname =
   let file = F.concat !G.out_dir fname in
   G.close_list (); G.list_och := Some (open_out file)

let process s =
   if is_registry s then init s
   else if !G.no_init then no_init ()
   else if L.is_uri s then E.process (U.uri_of_string s)
   else malformed s

let main =
begin try
   A.parse [
      "-O", A.String ((:=) G.out_dir), help_O;
      "-X", A.Unit G.clear, help_X;
      "-a", A.Set G.log_alpha, help_a;
      "-g", A.Set G.global_alpha, help_g;
      "-l", A.String set_list, help_l;
      "-m", A.Set G.log_missing, help_m;
      "-p", A.Set G.no_types, help_p;
      "-t", A.Set G.test, help_t;
   ] process help
with
   | X.Error s -> X.log s
end;
G.close_list ()
