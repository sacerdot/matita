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

(****************************************************************************)
(*                                                                          *)
(*                              PROJECT HELM                                *)
(*                                                                          *)
(*               Claudio Sacerdoti Coen <sacerdot@cs.unibo.it>              *)
(*                                24/01/2000                                *)
(*                                                                          *)
(* This module implements a trival cache system (an hash-table) for cic     *)
(*                          ^^^^^^                                          *)
(* objects. Uses the getter (getter.ml) and the parser (cicParser.ml)       *)
(*                                                                          *)
(****************************************************************************)

exception CircularDependency of string Lazy.t;;
exception Object_not_found of UriManager.uri;;

(* as the get cooked, but if not present the object is only fetched,
 * not unfreezed and committed 
 *)
val get_obj : 
  CicUniv.universe_graph -> UriManager.uri ->   
    Cic.obj * CicUniv.universe_graph

type type_checked_obj =
 | CheckedObj of (Cic.obj * CicUniv.universe_graph)    
 | UncheckedObj of Cic.obj * (CicUniv.universe_graph * CicUniv.universe list) option

val is_type_checked : 
  ?trust:bool -> CicUniv.universe_graph -> UriManager.uri ->  
    type_checked_obj

(* set_type_checking_info uri                                         *)
(* must be called once the type-checking of uri is finished           *)
(* The object whose uri is uri is unfreezed and won't be type-checked *)
(* again in the future (is_type_checked will return true)             *)
(*                                                                    *)
(* WARNING: THIS FUNCTION MUST BE CALLED ONLY BY CicTypeChecker       *)
val set_type_checking_info : UriManager.uri -> 
  (Cic.obj * CicUniv.universe_graph * CicUniv.universe list) -> unit

(* this function is called by CicTypeChecker.typecheck_obj to add to the *)
(* environment a new well typed object that is not yet in the library    *)
(* WARNING: THIS FUNCTION MUST BE CALLED ONLY BY CicTypeChecker *)
val add_type_checked_obj : 
  UriManager.uri -> 
  (Cic.obj * CicUniv.universe_graph * CicUniv.universe list) -> unit

  (** remove a type checked object
  * @raise Object_not_found when given term is not in the environment
  * @raise Failure when remove_term is invoked while type checking *)
val remove_obj: UriManager.uri -> unit

(* get_cooked_obj ~trust uri                                        *)
(* returns the object if it is already type-checked or if it can be *)
(* trusted (if [trust] = true and the trusting function accepts it) *)
(* Otherwise it raises Not_found                                    *)
val get_cooked_obj : 
  ?trust:bool -> CicUniv.universe_graph -> UriManager.uri ->
    Cic.obj * CicUniv.universe_graph

(* get_cooked_obj_with_univlist ~trust uri                          *)
(* returns the object if it is already type-checked or if it can be *)
(* trusted (if [trust] = true and the trusting function accepts it) *)
(* Otherwise it raises Not_found                                    *)
val get_cooked_obj_with_univlist : 
  ?trust:bool -> CicUniv.universe_graph -> UriManager.uri ->
    Cic.obj * CicUniv.universe_graph * CicUniv.universe list

(* FUNCTIONS USED ONLY IN THE TOPLEVEL/PROOF-ENGINE *)

(* (de)serialization *)
val dump_to_channel : ?callback:(string -> unit) -> out_channel -> unit
val restore_from_channel : ?callback:(string -> unit) -> in_channel -> unit
val empty : unit -> unit

(** Set trust function. Per default this function is set to (fun _ -> true) *)
val set_trust: (UriManager.uri -> bool) -> unit

  (** @return true for objects currently cooked/frozend/unchecked, false
  * otherwise (i.e. objects already parsed from XML) *)
val in_cache : UriManager.uri -> bool

(* to debug the matitac batch compiler *)
val list_obj: unit -> (UriManager.uri * Cic.obj * CicUniv.universe_graph) list
val list_uri: unit -> UriManager.uri list

  (** @return true for objects available in the library *)
val in_library: UriManager.uri -> bool

  (** total parsing time, only to benchmark the parser *)
val total_parsing_time: float ref

val invalidate: unit -> unit

(* EOF *)
