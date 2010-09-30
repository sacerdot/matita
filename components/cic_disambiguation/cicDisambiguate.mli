(*
 *
Copyright (C) 1999-2006, HELM Team.

This file is part of HELM, an Hypertextual, Electronic
Library of Mathematics, developed at the Computer Science
Department, University of Bologna, Italy.

HELM is free software; you can redistribute it and/or
modify it under the terms of the GNU General Public License
as published by the Free Software Foundation; either version 2
of the License, or (at your option) any later version.

HELM is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program; if not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA
02110-1301 USA.

For details, see the HELM web site: http://helm.cs.unibo.it/
*)

val interpretate_path :
  context:Cic.name list -> CicNotationPt.term -> Cic.term

val disambiguate_term :
  context:Cic.context ->
  metasenv:Cic.metasenv -> 
  subst:Cic.substitution ->
  expty:Cic.term option ->
  ?initial_ugraph:CicUniv.universe_graph -> 
  mk_implicit:(bool -> 'alias) ->
  description_of_alias:('alias -> string) ->
  fix_instance:(DisambiguateTypes.domain_item -> 'alias list -> 'alias list) ->
  mk_choice:('alias -> Cic.term DisambiguateTypes.codomain_item) ->
  aliases:'alias DisambiguateTypes.Environment.t ->
  universe:'alias list DisambiguateTypes.Environment.t option ->
  lookup_in_library:(
    DisambiguateTypes.interactive_user_uri_choice_type ->
    DisambiguateTypes.input_or_locate_uri_type ->
    DisambiguateTypes.Environment.key ->
    'alias list) ->
  CicNotationPt.term Disambiguate.disambiguator_input ->
  ((DisambiguateTypes.domain_item * 'alias) list *
   Cic.metasenv *                  
   Cic.substitution *
   Cic.term*
   CicUniv.universe_graph) list * 
  bool

val disambiguate_obj :
  mk_implicit:(bool -> 'alias) ->
  description_of_alias:('alias -> string) ->
  fix_instance:(DisambiguateTypes.domain_item -> 'alias list -> 'alias list) ->
  mk_choice:('alias -> Cic.term DisambiguateTypes.codomain_item) ->
  aliases:'alias DisambiguateTypes.Environment.t ->
  universe:'alias list DisambiguateTypes.Environment.t option ->
  lookup_in_library:(
    DisambiguateTypes.interactive_user_uri_choice_type ->
    DisambiguateTypes.input_or_locate_uri_type ->
    DisambiguateTypes.Environment.key ->
    'alias list) ->
  uri:UriManager.uri option ->     (* required only for inductive types *)
  CicNotationPt.term CicNotationPt.obj Disambiguate.disambiguator_input ->
  ((DisambiguateTypes.domain_item * 'alias) list *
   Cic.metasenv *   
   Cic.substitution *
   Cic.obj *
   CicUniv.universe_graph) list * 
  bool
