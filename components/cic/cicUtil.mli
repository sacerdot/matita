(* Copyright (C) 2004, HELM Team.
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

exception Meta_not_found of int
exception Subst_not_found of int

val lookup_meta: int -> Cic.metasenv -> Cic.conjecture
val lookup_subst: int -> Cic.substitution -> Cic.context * Cic.term * Cic.term
val exists_meta: int -> Cic.metasenv -> bool
val clean_up_local_context :
  Cic.substitution -> Cic.metasenv -> int -> (Cic.term option) list 
  -> (Cic.term option) list

val is_closed : Cic.term -> bool
val is_meta_closed : Cic.term -> bool
val metas_of_term : Cic.term -> (int * Cic.term option list) list
(* as before but with no duplicates. may avoind some stack overflows *)
val metas_of_term_set : Cic.term -> (int * Cic.term option list) list

  (** @raise Failure "not enough prods" *)
val strip_prods: int -> Cic.term -> Cic.term

(** conversions between terms which are fully representable as uris (Var, Const,
 * Mutind, and MutConstruct) and corresponding tree representations *)
val term_of_uri: UriManager.uri -> Cic.term (** @raise UriManager.IllFormedUri *)
val uri_of_term: Cic.term -> UriManager.uri (** @raise Invalid_argument "uri_of_term" *)

val id_of_annterm: Cic.annterm -> Cic.id

(** {2 Cic selectors} *)

val params_of_obj: Cic.obj -> UriManager.uri list
val attributes_of_obj: Cic.obj -> Cic.attribute list
val projections_of_record: Cic.obj -> UriManager.uri -> UriManager.uri list
val is_generated: Cic.obj -> bool

(** mk_rels [howmany] [from] 
 * creates a list of [howmany] rels starting from [from] in decreasing order *)
val mk_rels : int -> int -> Cic.term list

(** {2 Uri hash consing} *)
val rehash_term: Cic.term -> Cic.term
val rehash_obj: Cic.obj -> Cic.obj

val alpha_equivalence: Cic.term -> Cic.term -> bool

(* FG: Consistency Check. Detects:
 * applications without arguments, folded applications, non-positive rels
 *)
val is_sober: Cic.context -> Cic.term -> bool

val pp_term:
   (string -> unit) -> Cic.metasenv -> Cic.context -> Cic.term -> unit
val pp_obj:
   (string -> unit) -> Cic.obj -> unit
