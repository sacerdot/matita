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

(* These are the only exceptions that will be raised *)
exception TypeCheckerFailure of string Lazy.t
exception AssertFailure of string Lazy.t

(* this function is exported to be used also by the refiner;
   the callback function (defaul value: ignore) is invoked on each
   processed subterm; its first argument is the undebrujined term (the
   input); its second argument the corresponding debrujined term (the
   output). The callback is used to relocalize the error messages *)
val debrujin_constructor :
 ?cb:(Cic.term -> Cic.term -> unit) ->
 ?check_exp_named_subst: bool ->
  UriManager.uri -> int -> Cic.context -> Cic.term -> Cic.term

  (* defaults to true *)
val typecheck : 
  ?trust:bool -> UriManager.uri -> Cic.obj * CicUniv.universe_graph

(* FUNCTIONS USED ONLY IN THE TOPLEVEL *)

(* type_of_aux' metasenv context term *)
val type_of_aux':
  ?subst:Cic.substitution -> Cic.metasenv -> Cic.context -> 
  Cic.term -> CicUniv.universe_graph -> 
  Cic.term * CicUniv.universe_graph

(* typechecks the obj and puts it in the environment
 * empty universes are filed with the given uri, thus you should
 * get the object again after calling this *)
val typecheck_obj : UriManager.uri -> Cic.obj -> unit

(* check_allowed_sort_elimination uri i s1 s2
   This function is used outside the kernel to determine in advance whether
   a MutCase will be allowed or not.
   [uri,i] is the type of the term to match
   [s1] is the sort of the term to eliminate (i.e. the head of the arity
        of the inductive type [uri,i])
   [s2] is the sort of the goal (i.e. the head of the type of the outtype
        of the MutCase) *)
val check_allowed_sort_elimination:
 UriManager.uri -> int -> Cic.sort -> Cic.sort -> bool

(* does_not_occur ~subst context n nn t
   checks if the semi-open interval of Rels (n,nn] occurs in t *)
val does_not_occur:
 ?subst:Cic.substitution -> Cic.context -> int -> int -> Cic.term -> bool
