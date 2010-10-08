(* Copyright (C) 2005, HELM Team.
 * 
 * This file is part of HELM, an Hypertextual, Electronic
 * Library of Mathematics, developed at the Computer Science
 * Department, University of Bologna, Italy.
 * 
 * HELM is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 * 
 * HELM is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with HELM; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston,
 * MA  02111-1307, USA.
 * 
 * For details, see the HELM World-Wide-Web page,
 * http://helm.cs.unibo.it/
 *)


  (** {2 Persistant state handling} *)

type interpretation_id

val add_interpretation:
  string ->                                       (* id / description *)
  string * CicNotationPt.argument_pattern list -> (* symbol, level 2 pattern *)
  CicNotationPt.cic_appl_pattern ->               (* level 3 pattern *)
    interpretation_id

  (** @raise Interpretation_not_found *)
val lookup_interpretations:
  ?sorted:bool -> string -> (* symbol *)
    (string * CicNotationPt.argument_pattern list *
      CicNotationPt.cic_appl_pattern) list

exception Interpretation_not_found

  (** @raise Interpretation_not_found *)
val remove_interpretation: interpretation_id -> unit

  (** {3 Interpretations toggling} *)

val get_all_interpretations: unit -> (interpretation_id * string) list
val get_active_interpretations: unit -> interpretation_id list
val set_active_interpretations: interpretation_id list -> unit

  (** {2 content -> cic} *)

  (** @param env environment from argument_pattern to cic terms
   * @param pat cic_appl_pattern *)
val instantiate_appl_pattern:
  mk_appl:('term list -> 'term) -> 
  mk_implicit:(bool -> 'term) ->
  term_of_uri : (UriManager.uri -> 'term) ->
  term_of_nref : (NReference.reference -> 'term) ->
  (string * 'term) list -> CicNotationPt.cic_appl_pattern ->
    'term

val push: unit -> unit
val pop: unit -> unit

(* for Matita NG *)
val find_level2_patterns32:
 int ->
  string * string *
   CicNotationPt.argument_pattern list * CicNotationPt.cic_appl_pattern

val add_load_patterns32: 
 ((bool * CicNotationPt.cic_appl_pattern * int) list -> unit) -> unit
val init: unit -> unit
