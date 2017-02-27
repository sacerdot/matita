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

let default_check = false

let default_no_types = false

let default_no_proofs = false

let default_global_alpha = false

let default_log_alpha = false

let default_log_missing = false

let default_list_och = None

let default_alpha = []

let default_macro = []

let default_sigs = []

(* interface ****************************************************************)

let dno_id = "_"                            (* identifier for not-occurring premises *)

let nan = -1                                (* not a number *)

let status = new P.status

let no_init = ref default_no_init

let out_dir = ref default_out_dir           (* directory of generated files *)

let proc_id = ref default_proc_id           (* identifer for anticipations *)

let check = ref default_check               (* check transformations *)

let no_types = ref default_no_types         (* omit types *)

let no_proofs = ref default_no_proofs       (* omit proofs *)

let global_alpha = ref default_global_alpha (* log alpha-unconverted identifiers *)

let log_alpha = ref default_log_alpha       (* log alpha-unconverted identifiers *)

let log_missing = ref default_log_missing   (* log missing notational macros *)

let list_och = ref default_list_och         (* output stream for list file *)

let alpha_type = ref default_alpha          (* data for type-based alpha-conversion *)

let alpha_sort = ref default_alpha          (* data for sort-based alpha-conversion *)

let alpha_gref = ref default_alpha          (* data for constant renaming *)

let macro_gref = ref default_macro          (* data for eta-conversion and constant rendering *)

let sigs_gref = ref default_sigs            (* data for sigma-type rendering *)

let is_global_id s =
   !global_alpha && s <> dno_id

let close_list () = match !list_och with
   | None     -> ()
   | Some och -> close_out och

let clear () =
   R.clear (); close_list ();
   no_init := default_no_init;
   out_dir := default_out_dir;
   proc_id := default_proc_id;
   check := default_check;
   no_types := default_no_types;
   no_proofs := default_no_proofs;
   global_alpha := default_global_alpha;
   log_alpha := default_log_alpha;
   log_missing := default_log_missing;
   list_och := default_list_och;
   alpha_type := default_alpha;
   alpha_sort := default_alpha;
   alpha_gref := default_alpha;
   macro_gref := default_macro;
   sigs_gref := default_sigs
