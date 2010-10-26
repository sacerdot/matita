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

(* $Id$ *)

val set_head_beta_reduce: (upto:int -> NCic.term -> NCic.term) -> unit
val set_get_obj: (NUri.uri -> NCic.obj) -> unit

val r2s: bool -> NReference.reference -> string

val string_of_flavour: NCic.def_flavour -> string

val ppterm: 
  context:NCic.context -> 
  subst:NCic.substitution -> 
  metasenv:NCic.metasenv ->
  ?margin:int ->
  ?inside_fix:bool ->
   NCic.term -> string

val ppcontext:
  ?sep:string ->
  subst:NCic.substitution -> 
  metasenv:NCic.metasenv ->
  NCic.context -> string 

val ppmetasenv:
  subst:NCic.substitution -> NCic.metasenv -> string

val ppsubst:
 metasenv:NCic.metasenv -> ?use_subst:bool -> NCic.substitution -> string

val ppobj: NCic.obj -> string

(* variants that use a formatter 
module Format : sig
  val ppterm: 
    formatter:Format.formatter ->
    context:NCic.context -> 
    subst:NCic.substitution -> 
    metasenv:NCic.metasenv ->
    ?margin:int ->
    ?inside_fix:bool ->
     NCic.term -> unit
  
  val ppcontext:
    ?sep:string ->
    formatter:Format.formatter ->
    subst:NCic.substitution -> 
    metasenv:NCic.metasenv ->
    NCic.context -> unit 
  
  val ppmetasenv:
    formatter:Format.formatter ->
    subst:NCic.substitution -> NCic.metasenv -> unit
  
  val ppsubst: 
    formatter:Format.formatter ->
    metasenv:NCic.metasenv -> NCic.substitution -> unit
  
  val ppobj: 
    formatter:Format.formatter -> NCic.obj -> unit
end
*)
