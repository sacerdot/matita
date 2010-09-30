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

exception IllFormedUri of string;;

type uri

val eq : uri -> uri -> bool
val compare : uri -> uri -> int

val uri_of_string : string -> uri

val string_of_uri : uri -> string  (* complete uri *)
val name_of_uri   : uri -> string  (* name only (without extension)*)
val nameext_of_uri   : uri -> string  (* name only (with extension)*)
val buri_of_uri   : uri -> string  (* base uri only, without trailing '/' *)

(* given an uri, returns the uri of the corresponding cic file, *)
(* i.e. removes the [.types][.ann] suffix                       *)
val cicuri_of_uri : uri -> uri

val strip_xpointer: uri -> uri      (* remove trailing #xpointer..., if any *)

(* given an uri, returns the uri of the corresponding annotation file, *)
(* i.e. adds the .ann suffix if not already present                    *)
val annuri_of_uri : uri -> uri

val uri_is_annuri : uri -> bool
val uri_is_var : uri -> bool
val uri_is_con : uri -> bool
val uri_is_ind : uri -> bool

(* given an uri of a constant, it gives back the uri of its body             *)
(* it gives back None if the uri refers to a Variable or MutualInductiveType *)
val bodyuri_of_uri : uri -> uri option

val ind_uri_split : uri -> uri * int option * int option

(* given an uri, it gives back the uri of its inner types             *)
val innertypesuri_of_uri : uri -> uri
(* given an uri, it gives back the uri of its univgraph             *)
val univgraphuri_of_uri : uri -> uri

(* builder for MutInd and MutConstruct URIs
 * [uri] -> [typeno] -> [consno option]
 *)
val uri_of_uriref :  uri -> int -> int option -> uri

module UriSet: Set.S with type elt = uri
(*module UriPairSet: Set.S with type elt = uri * uri*)

module UriHashtbl : Hashtbl.S with type key = uri

