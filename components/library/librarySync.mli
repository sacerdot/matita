(* Copyright (C) 2004-2005, HELM Team.
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

exception AlreadyDefined of UriManager.uri

type coercion_decl = 
  UriManager.uri -> int (* arity *) ->
   int (* saturations *) -> string (* baseuri *) ->
    UriManager.uri list (* lemmas (new objs) *)

(* the add_single_obj fun passed to the callback can raise AlreadyDefined *)
val add_object_declaration_hook :
  (add_obj:(UriManager.uri -> Cic.obj -> UriManager.uri list) -> 
   add_coercion:coercion_decl ->
    UriManager.uri -> Cic.obj -> UriManager.uri list) -> unit

(* adds an object to the library together with all auxiliary lemmas on it *)
(* (e.g. elimination principles, projections, etc.)                       *)
(* it returns the list of the uris of the auxiliary lemmas generated      *)
val add_obj: 
  UriManager.uri -> Cic.obj -> pack_coercion_obj:(Cic.obj -> Cic.obj) -> 
    UriManager.uri list

(* removes an object (does not remove its associated lemmas) *)
val remove_obj: UriManager.uri -> unit

(* Informs the library that [uri] is a coercion.                         *)
(* This can generate some composite coercions that, if [add_composites]  *)
(* is true are added to the library.                                     *)
(* The list of added objects is returned.                                *)
val add_coercion: 
  add_composites:bool -> pack_coercion_obj:(Cic.obj -> Cic.obj) -> coercion_decl

(* these just push/pop the coercions database, since the library is not
 * pushable/poppable *)
val push: unit -> unit
val pop: unit -> unit
