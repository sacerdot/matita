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

val add_coercion:
  pack_coercion_obj:(Cic.obj -> Cic.obj) ->
  add_composites:bool -> GrafiteTypes.status ->
  UriManager.uri -> int -> int ->
  string (* baseuri *) ->
    GrafiteTypes.status * UriManager.uri list

val prefer_coercion: 
  GrafiteTypes.status -> UriManager.uri -> GrafiteTypes.status 

val time_travel: 
  present:GrafiteTypes.status -> ?past:GrafiteTypes.status -> unit -> unit

  (* also resets the imperative part of the status 
   * init: the baseuri of the current script *)
val init: LexiconEngine.status -> string -> GrafiteTypes.status

(*
  (* just an empty status, does not reset imperative 
   * part, use push/pop for that *)
val initial_status: string -> GrafiteTypes.status
*)

  (* preserve _only_ imperative parts of the status *)
val push: unit -> unit
val pop: unit -> unit
