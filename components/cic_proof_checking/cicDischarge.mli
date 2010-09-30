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

(* NOTE. Discharged variables are not well formed. *)
(*       For internal recursive use only.          *) 

(* discharges the explicit variables of the given object (with sharing)     *)
(* the first argument is a map for relacating the names of the objects      *)
(* the second argument is a map for relocating the uris of the dependencdes *)
val discharge_object:
   (string -> string) -> (UriManager.uri -> UriManager.uri) -> 
   Cic.obj -> Cic.obj

(* applies the previous function to the object at the given uri *)
(* returns true if the object does not need discharging         *)
val discharge_uri:
   (string -> string) -> (UriManager.uri -> UriManager.uri) ->
   UriManager.uri -> Cic.obj * bool

(* if activated prints the received object before and after discharging *)
val debug: bool ref
