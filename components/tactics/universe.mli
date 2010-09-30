(* Copyright (C) 2002, HELM Team.
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
 * http://cs.unibo.it/helm/.
 *)

type universe

val empty : universe


val iter : 
  universe ->
  (UriManager.uri Discrimination_tree.path -> Cic.term list -> unit) ->
  unit

(* retrieves the list of term that hopefully unify *)
val get_candidates: universe -> Cic.term -> Cic.term list

(* index [univ] [key] [term] *)
val index: universe -> Cic.term -> Cic.term -> universe

(* collapse non-indexable terms, removing coercions an unfolding the head
 * constant if any *)
val keys: Cic.context -> Cic.term -> Cic.term list

(* collapse non-indexable terms, not removing coercions *)
val key: Cic.term -> Cic.term 

val in_universe: universe -> Cic.term -> Cic.term option

(* indexes the term and its unfolded both without coercions *)
val index_term_and_unfolded_term: 
  universe -> Cic.context -> Cic.term -> Cic.term -> universe

(* indexex the term without coercions, with coercions and unfolded without
 * coercions *)
val index_local_term: 
  universe -> Cic.context -> Cic.term -> Cic.term -> universe

(* pairs are (term,ty) *)
val index_list: 
    universe -> Cic.context -> (Cic.term*Cic.term) list -> universe
val remove:
  universe -> Cic.context -> Cic.term -> Cic.term -> universe
val remove_uri:
  universe -> UriManager.uri -> universe
