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


(* identity_relocation_list_for_metavariable i canonical_context         *)
(* returns the identity relocation list, which is the list               *)
(* [Rel 1 ; ... ; Rel n] where n = List.length [canonical_context]       *)
val identity_relocation_list_for_metavariable :
  ?start: int -> 'a option list -> Cic.term option list

(* Returns the first meta whose number is above the *)
(* number of the higher meta.                       *)
val new_meta : Cic.metasenv -> Cic.substitution -> int

(** [mk_implicit metasenv context]
 * add a fresh metavariable to the given metasenv, using given context
 * @return the new metasenv and the index of the added conjecture *)
val mk_implicit: Cic.metasenv -> Cic.substitution -> Cic.context -> Cic.metasenv * int

(** as above, but the fresh metavariable represents a type *)
val mk_implicit_type: Cic.metasenv -> Cic.substitution -> Cic.context -> Cic.metasenv * int

(** as above, but the fresh metavariable represents a sort *)
val mk_implicit_sort: Cic.metasenv -> Cic.substitution -> Cic.metasenv * int

(** [mk_implicit metasenv context] create n fresh metavariables *)
val n_fresh_metas:  
  Cic.metasenv -> Cic.substitution -> Cic.context -> int -> Cic.metasenv * Cic.term list

(** [fresh_subst metasenv context uris] takes in input a list of uri and
creates a fresh explicit substitution *)
val fresh_subst:  
  Cic.metasenv -> 
    Cic.substitution ->
      Cic.context -> 
        UriManager.uri list -> 
          Cic.metasenv * (Cic.term Cic.explicit_named_substitution)

