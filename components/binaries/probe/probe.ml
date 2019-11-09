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

module R = Helm_registry
module L = Librarian
module B = NCicLibrary
module C = NCicTypeChecker
module H = HLog

module O = Options
module M = MatitaList
module D = MatitaRemove
module S = NCicScan
module E = Engine

let trusted _ = true

let no_log _ _ = ()

let init registry =
   R.load_from registry;
   if !O.no_init then begin
      B.init ();
      C.set_trust trusted;
      H.set_log_callback no_log;
      O.no_init := false;
   end

let scan_uri devel str =
   M.from_string (R.get "matita.basedir") devel str;
   S.scan ()

let scan_from devel =
   let devel, uri = E.get_uri devel in
   scan_uri devel uri

let set_g () = O.exclude := `Generated :: !O.exclude

let set_i () = O.exclude := `Implied :: !O.exclude

let set_p () = O.exclude := `Provided :: !O.exclude

let out_f () = O.iter_xflavours E.out_int

let out_oc () = E.out_int !O.net

let out_on () = E.out_length !O.objs

let out_os () = E.out_uris !O.objs

let out_sc () = E.out_int !O.chars

let out_sn () = E.out_length !O.srcs

let out_ss () = E.out_uris !O.srcs

let out_b file = O.out_deps file

let process s =
   if L.is_uri s then scan_uri "" s
   else if E.is_registry s then init s
   else scan_from s

let clear () =
   D.objects (); O.clear ()

let _ =
   let help = "Usage: probe [ -LX | <configuration file> | -gip | <HELM (base)uri> | -f | -oc | -on | -os | -sc | -sn | -ss  ]*" in
   let help_L  = " Activate lexer debugging" in
   let help_X  = " Clear configuration, options and counters" in
   let help_b  = "<file>  Print backward object dependences in this file" in
   let help_f  = " Print the number of objects grouped by flavour" in
   let help_g  = " Exclude generated objects" in
   let help_i  = " Exclude implied objects" in
   let help_oc = " Print the total intrinsic complexity (objects)" in
   let help_on = " Print the number of objects" in
   let help_os = " Print the list of objects" in
   let help_p  = " Exclude provided objects" in
   let help_sc = " Print the total extrinsic complexity (sources)" in
   let help_sn = " Print the number of sources" in
   let help_ss = " Print the list of sources" in
   A.parse [
      "-L" , A.Set O.debug_lexer, help_L;
      "-X" , A.Unit clear , help_X;
      "-b" , A.String out_b , help_b;
      "-f" , A.Unit out_f , help_f;
      "-g" , A.Unit set_g , help_g;
      "-i" , A.Unit set_i , help_i;
      "-oc", A.Unit out_oc, help_oc;
      "-on", A.Unit out_on, help_on;
      "-os", A.Unit out_os, help_os;
      "-p" , A.Unit set_p , help_p;
      "-sc", A.Unit out_sc, help_sc;
      "-sn", A.Unit out_sn, help_sn;
      "-ss", A.Unit out_ss, help_ss;
   ] process help;
   D.objects ()
