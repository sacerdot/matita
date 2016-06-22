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

val dno_id: string

val nan: int

val status: NCicPp.status

val no_init: bool ref

val out_dir: string ref

val proc_id: string ref

val check: bool ref 

val no_types: bool ref 

val no_proofs: bool ref 

val global_alpha: bool ref

val log_alpha: bool ref

val log_missing: bool ref

val list_och: out_channel option ref 

val alpha_type: (string * string * string) list ref

val alpha_sort: (string * string * string) list ref

val alpha_gref: (string * string) list ref

val macro_gref: (string * string * int * int) list ref

val clear: unit -> unit

val close_list: unit -> unit

val is_global_id: string -> bool
