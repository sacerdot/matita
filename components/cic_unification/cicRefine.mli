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

exception RefineFailure of string Lazy.t;;
exception Uncertain of string Lazy.t;;
exception AssertFailure of string Lazy.t;;

(* type_of_aux' metasenv context term graph                *)
(* refines [term] and returns the refined form of [term],  *)
(* its type, the new metasenv and universe graph.          *)
val type_of_aux':
 ?localization_tbl:Stdpp.location Cic.CicHash.t ->
  Cic.metasenv -> Cic.context -> Cic.term -> CicUniv.universe_graph ->
   Cic.term * Cic.term * Cic.metasenv * CicUniv.universe_graph

 (* this is the correct one and should be used by tactics to fold subst *)
val type_of:
  Cic.metasenv -> Cic.substitution -> 
  Cic.context -> Cic.term -> CicUniv.universe_graph ->
   Cic.term * Cic.term * Cic.metasenv * Cic.substitution *CicUniv.universe_graph

(* typecheck metasenv uri obj graph                     *)
(* refines [obj] and returns the refined form of [obj], *)
(* the new metasenv and universe graph.                 *)
(* the [uri] is required only for inductive definitions *)
val typecheck : 
 localization_tbl:Stdpp.location Cic.CicHash.t ->
  Cic.metasenv -> UriManager.uri option -> Cic.obj ->
   Cic.obj * Cic.metasenv * CicUniv.universe_graph

val insert_coercions: bool ref (* initially true *)
val pack_coercions : bool ref

val pack_coercion_obj: Cic.obj -> Cic.obj

val pack_coercion_metasenv: Cic.metasenv -> Cic.metasenv
