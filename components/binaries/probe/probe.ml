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

let set_p () = O.exclude := `Provided :: !O.exclude

let out_i () = E.out_int !O.net

let out_on () = E.out_length !O.objs

let out_os () = E.out_uris !O.objs

let out_sn () = E.out_length !O.srcs 

let out_ss () = E.out_uris !O.srcs

let process s =
   if L.is_uri s then scan_uri "" s
   else if E.is_registry s then init s
   else scan_from s

let clear () = 
   D.objects (); O.clear ()

let _ =
   let help = "Usage: probe [ -X | <configuration file> | -gp | HELM (base)uri | -i | -on | os | -sn | -ss  ]*" in
   let help_X  = " Clear configuration, options and counters" in
   let help_g  = " Exclude generated objects" in
   let help_i  = " Print the total intrinsic size" in
   let help_p  = " Exclude provided objects" in
   let help_on = " Print the number of objects" in
   let help_os = " Print the list of objects" in
   let help_sn = " Print the number of sources" in
   let help_ss = " Print the list of sources" in
   A.parse [
      "-X" , A.Unit clear, help_X;
      "-g" , A.Unit set_g, help_g;
      "-i" , A.Unit out_i, help_i;
      "-on", A.Unit out_on, help_on;
      "-os", A.Unit out_os, help_os;
      "-p" , A.Unit set_p, help_p;      
      "-sn", A.Unit out_sn, help_sn;
      "-ss", A.Unit out_ss, help_ss;
   ] process help;
   D.objects ()
