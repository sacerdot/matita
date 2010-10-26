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

(* $Id: nCic.ml 9058 2008-10-13 17:42:30Z tassi $ *)

exception Error of string lazy_t * exn option
val fail: ?exn:exn -> string lazy_t -> 'a

class type g_pstatus =
 object
  inherit NEstatus.g_status
  method obj: NCic.obj
 end

class pstatus :
 NCic.obj ->
  object ('self)
   inherit NEstatus.status
   method obj: NCic.obj
   method set_obj: NCic.obj -> 'self
   method set_pstatus: #g_pstatus -> 'self
  end

type tactic_term = NotationPt.term Disambiguate.disambiguator_input
type tactic_pattern = GrafiteAst.npattern Disambiguate.disambiguator_input

type cic_term 
val ctx_of : cic_term -> NCic.context
val term_of_cic_term : 
 #pstatus as 'status -> cic_term -> NCic.context -> 'status * NCic.term

val mk_cic_term : NCic.context -> NCic.term -> cic_term
val disambiguate:
 #pstatus as 'status -> NCic.context -> tactic_term -> cic_term option ->
  'status * cic_term (* * cic_term XXX *)

val analyse_indty: 
 #pstatus as 'status -> cic_term -> 
  'status * (NReference.reference * int * NCic.term list * NCic.term list)

val ppterm: #pstatus -> cic_term -> string
val ppcontext: #pstatus -> NCic.context -> string
val whd: 
 #pstatus as 'status -> ?delta:int -> NCic.context -> cic_term -> 
  'status * cic_term 
val normalize: 
 #pstatus as 'status -> ?delta:int -> NCic.context -> cic_term ->
  'status * cic_term 
val typeof: 
 #pstatus as 'status -> NCic.context -> cic_term -> 'status * cic_term
val unify: 
 #pstatus as 'status -> NCic.context -> cic_term -> cic_term -> 'status
val refine: 
 #pstatus as 'status -> NCic.context -> cic_term -> cic_term option -> 
  'status * cic_term * cic_term (* status, term, type *)
val apply_subst:
 #pstatus as 'status -> NCic.context -> cic_term -> 'status * cic_term
val apply_subst_context :
  #pstatus -> fix_projections:bool -> NCic.context -> NCic.context
val fix_sorts: #pstatus as 'status -> cic_term -> 'status * cic_term
val saturate :
 #pstatus as 'status -> ?delta:int -> cic_term -> 'status * cic_term * cic_term list
val metas_of_term : #pstatus as 'status -> cic_term -> int list

val get_goalty: #pstatus -> int -> cic_term
val get_subst: #pstatus -> NCic.substitution
val mk_meta: 
 #pstatus as 'status -> ?attrs:NCic.meta_attrs -> NCic.context ->
   [ `Decl of cic_term | `Def of cic_term ] -> NCicUntrusted.meta_kind ->
     'status * cic_term
val instantiate: #pstatus as 'status -> int -> cic_term -> 'status
val instantiate_with_ast: #pstatus as 'status -> int -> tactic_term -> 'status

val select_term:
 #pstatus as 'status -> 
  found: ('status -> cic_term -> 'status * cic_term) ->
  postprocess: ('status -> cic_term -> 'status * cic_term) ->
  cic_term -> tactic_term option * NCic.term ->
    'status * cic_term

val mk_in_scope: #pstatus as 'status -> cic_term -> 'status * cic_term
val mk_out_scope:
 int -> (#pstatus as 'status) -> cic_term -> 'status * cic_term

class type ['stack] g_status =
 object
  inherit g_pstatus
  method stack: 'stack
 end

class ['stack] status :
 NCic.obj -> 'stack ->
  object ('self)
   inherit pstatus
   method stack: 'stack
   method set_stack: 'stack -> 'self
   method set_status: 'stack #g_status -> 'self
  end

class type lowtac_status = [unit] status

type 'status lowtactic = #lowtac_status as 'status -> int -> 'status

class type tac_status = [Continuationals.Stack.t] status

val pp_tac_status: #tac_status -> unit

type 'status tactic = #tac_status as 'status -> 'status

(* indexing facilities over cic_term based on inverse De Bruijn indexes *)

module NCicInverseRelIndexable : Discrimination_tree.Indexable
with type input = cic_term and type constant_name = NUri.uri 

module Ncic_termSet : Set.S with type elt = cic_term

module InvRelDiscriminationTree : Discrimination_tree.DiscriminationTree 
with type constant_name = NCicInverseRelIndexable.constant_name
and type input = NCicInverseRelIndexable.input
and type data = Ncic_termSet.elt and type dataset = Ncic_termSet.t

val debug : bool ref

(* end *)