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

(* $Id$ *)

(* This module implements the Query interface to the Coercion Graph *)

type coercion_search_result = 
     (* metasenv, last coercion argument, fully saturated coercion *)
     (* to apply the coercion it is sufficient to unify the last coercion
        argument (that is a Meta) with the term to be coerced *)
  | SomeCoercion of (Cic.metasenv * Cic.term * Cic.term) list
  | SomeCoercionToTgt of (Cic.metasenv * Cic.term * Cic.term) list
  | NoCoercion
  | NotHandled

val look_for_coercion :
  Cic.metasenv -> Cic.substitution -> Cic.context ->
   Cic.term -> Cic.term -> coercion_search_result

val source_of: Cic.term -> Cic.term

val generate_dot_file: Format.formatter -> unit

(* given the Appl contents returns the argument of the head coercion *)
val coerced_arg: Cic.term list -> (Cic.term * int) option

(* returns: (carr,menv,(saturated coercion,last arg)option,idem) list *)
val meets : 
  Cic.metasenv -> Cic.substitution -> Cic.context ->
  bool * CoercDb.coerc_carr -> bool * CoercDb.coerc_carr -> 
    (CoercDb.coerc_carr * Cic.metasenv * 
      (Cic.term * Cic.term) option * (Cic.term * Cic.term) option) list
  
