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
module B = NCicLibrary
module C = NCicTypeChecker
module H = HLog

module G = Options
module E = Engine
module O = TeXOutput

let help_O = "<dir> Set this output directory"
let help_X = " Clear configuration and options"

let help   = ""

(* internal functions *******************************************************)

let trusted _ = true

let no_log _ _ = ()

let init registry =
   R.load_from registry; 
   if !G.no_init then begin
      B.init (); 
      C.set_trust trusted;
      H.set_log_callback no_log;
      G.no_init := false;
   end

let is_registry s =
   F.check_suffix s ".conf.xml"

let no_init () =
   failwith "MaTeX: registry not initialized" 

let malformed s =
   failwith ("MaTeX: malformed argument: " ^ s)

let process s =
   if is_registry s then init s
   else if !G.no_init then no_init ()
   else if L.is_uri s then E.process (U.uri_of_string s)
   else malformed s

let main =
   A.parse [
      "-O", A.String ((:=) G.out_dir), help_O;
      "-X", A.Unit G.clear, help_X;
   ] process help
