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

val set_reference_of_oxuri: (UriManager.uri -> NReference.reference) -> unit

val disambiguate_term :
  context:NCic.context ->
  metasenv:NCic.metasenv -> 
  subst:NCic.substitution ->
  expty:NCic.term option ->
  mk_implicit: (bool -> 'alias) ->
  description_of_alias:('alias -> string) ->
  fix_instance:(DisambiguateTypes.domain_item -> 'alias list -> 'alias list) ->
  mk_choice:('alias -> NCic.term DisambiguateTypes.codomain_item) ->
  aliases:'alias DisambiguateTypes.Environment.t ->
  universe:'alias list DisambiguateTypes.Environment.t option ->
  rdb:#NRstatus.status ->
  lookup_in_library:(
    DisambiguateTypes.interactive_user_uri_choice_type ->
    DisambiguateTypes.input_or_locate_uri_type ->
    DisambiguateTypes.Environment.key ->
    'alias list) ->
  CicNotationPt.term Disambiguate.disambiguator_input ->
  ((DisambiguateTypes.domain_item * 'alias) list *
   NCic.metasenv *                  
   NCic.substitution *
   NCic.term) list * 
  bool
  
val disambiguate_obj :
  mk_implicit:(bool -> 'alias) ->
  description_of_alias:('alias -> string) ->
  fix_instance:(DisambiguateTypes.domain_item -> 'alias list -> 'alias list) ->
  mk_choice:('alias -> NCic.term DisambiguateTypes.codomain_item) ->
  aliases:'alias DisambiguateTypes.Environment.t ->
  universe:'alias list DisambiguateTypes.Environment.t option ->
  rdb:#NRstatus.status ->
  lookup_in_library:(
    DisambiguateTypes.interactive_user_uri_choice_type ->
    DisambiguateTypes.input_or_locate_uri_type ->
    DisambiguateTypes.Environment.key ->
     'alias list) ->
  uri:NUri.uri ->
  string * int * CicNotationPt.term CicNotationPt.obj ->
  ((DisambiguateTypes.Environment.key * 'alias) list * NCic.metasenv *
   NCic.substitution * NCic.obj)
  list * bool

val disambiguate_path: CicNotationPt.term -> NCic.term

