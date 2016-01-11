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

module F = Filename

module R = Helm_registry
module P = NCicPp

(* internal *****************************************************************)

let default_no_init = true

let default_out_dir = F.current_dir_name

let default_proc_id = "H"

let default_test = false

let default_no_types = false

(* interface ****************************************************************)

let status = new P.status

let no_init = ref default_no_init

let out_dir = ref default_out_dir   (* directory of generated files *)

let proc_id = ref default_proc_id   (* identifer of anticipations *)

let test = ref default_test         (* test anticipation *)

let no_types = ref default_no_types (* omit types *)

let clear () =
   R.clear ();
   no_init := default_no_init;
   out_dir := default_out_dir;
   proc_id := default_proc_id;
   test := default_test;
   no_types := default_no_types
