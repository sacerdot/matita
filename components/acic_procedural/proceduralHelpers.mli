(* Copyright (C) 2003-2005, HELM Team.
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

val mk_fresh_name:
   bool -> Cic.context -> Cic.name -> Cic.name

val list_fold_right_cps:
   ('b -> 'c) -> (('b -> 'c) -> 'a -> 'b -> 'c) -> 'a list -> 'b -> 'c

val list_fold_left_cps:
   ('b -> 'c) -> (('b -> 'c) -> 'b -> 'a -> 'c) -> 'b -> 'a list -> 'c

val list_map_cps:
   ('b list -> 'c) -> (('b -> 'c) -> 'a -> 'c) -> 'a list -> 'c

val identity:
   'a -> 'a

val compose:
   ('a -> 'b) -> ('c -> 'a) -> 'c -> 'b

val fst3:
   'a * 'b * 'c -> 'a 

val refine:
   Cic.context -> Cic.term -> Cic.term

val get_type:
   string -> Cic.context -> Cic.term -> Cic.term

val is_prop:
   Cic.context -> Cic.term -> bool

val is_proof:
   Cic.context -> Cic.term -> bool

val is_sort:
   Cic.term -> bool

val is_unsafe:
   int -> Cic.context * Cic.term -> bool

val is_not_atomic:
   Cic.term -> bool

val is_atomic:
   Cic.term -> bool

val get_ind_type:
   UriManager.uri -> int -> int * Cic.inductiveType

val get_ind_names:
   UriManager.uri -> int -> string list

val get_default_eliminator:
  Cic.context -> UriManager.uri -> int -> Cic.term -> Cic.term

val get_ind_parameters:
   Cic.context -> Cic.term -> Cic.term list * int

val cic: 
   Cic.annterm -> Cic.term

val occurs:
   Cic.context -> what:Cic.term -> where:Cic.term -> bool

val name_of_uri:
   UriManager.uri -> int option -> int option -> string

val cic_bc:
   Cic.context -> Cic.term -> Cic.term

val acic_bc:
   Cic.context -> Cic.annterm -> Cic.annterm

val is_acic_proof:
   (Cic.id, Cic2acic.sort_kind) Hashtbl.t -> Cic.context -> Cic.annterm ->
   bool

val alpha:
   ?flatten:bool -> Cic.context -> Cic.term -> Cic.term -> bool
