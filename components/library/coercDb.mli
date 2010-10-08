(* Copyright (C) 2000, HELM Team.
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


type coerc_carr = private 
  | Uri of UriManager.uri (* const, mutind, mutconstr *)
  | Sort of Cic.sort (* Prop, Set, Type *) 
  | Fun of int
  | Dead
;;
  
val eq_carr: ?exact:bool -> coerc_carr -> coerc_carr -> bool
val string_of_carr: coerc_carr -> string

(* takes a term in whnf ~delta:false and a desired ariety *)
val coerc_carr_of_term: Cic.term -> int -> coerc_carr 

type coerc_db
val empty_coerc_db : coerc_db
val dump: unit -> coerc_db
val restore: coerc_db -> unit

val to_list:
  coerc_db -> 
    (coerc_carr * coerc_carr * (UriManager.uri * int * int) list) list

(* src carr, tgt carr, uri, saturations, coerced position 
 * invariant:
 *   if the constant pointed by uri has n argments
 *   n = coerced position + saturations + FunClass arity
 *)

type saturations = int
type coerced_pos = int
type coercion_entry = 
  coerc_carr * coerc_carr * UriManager.uri * saturations * coerced_pos
val add_coercion: coercion_entry -> unit
val remove_coercion: (coercion_entry -> bool) -> unit

val find_coercion: 
  (coerc_carr * coerc_carr -> bool) -> (UriManager.uri * int) list 
    
val is_a_coercion: Cic.term -> coercion_entry option

val prefer: UriManager.uri -> unit
