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

(* $Id$ *)

open Printf
open GrafiteTypes

  (** user hit the cancel button *)
exception Cancel

type abouts =
  [ `Blank
  | `Current_proof
  | `Us
  | `Coercions
  | `CoercionsFull
  | `TeX
  | `Grammar
  | `Hints
  ]
  
type mathViewer_entry =
  [ `About of abouts  (* current proof *)
  | `Check of string  (* term *)
  | `Cic of Cic.term * Cic.metasenv
  | `NCic of NCic.term * NCic.context * NCic.metasenv * NCic.substitution
  | `Dir of string  (* "directory" in cic uris namespace *)
  | `HBugs of [ `Tutors ] (* list of available HBugs tutors *)
  | `Metadata of [ `Deps of [`Fwd | `Back] * UriManager.uri ]
  | `Uri of UriManager.uri (* cic object uri *)
  | `NRef of NReference.reference (* cic object uri *)
  | `Whelp of string * UriManager.uri list (* query and results *)
  | `Univs of UriManager.uri
  ]

let string_of_entry = function
  | `About `Blank -> "about:blank"
  | `About `Current_proof -> "about:proof"
  | `About `Us -> "about:us"
  | `About `Coercions -> "about:coercions?tred=true"
  | `About `CoercionsFull -> "about:coercions"
  | `About `TeX -> "about:tex"
  | `About `Grammar -> "about:grammar"
  | `About `Hints -> "about:hints"
  | `Check _ -> "check:"
  | `Cic (_, _) -> "term:"
  | `NCic (_, _, _, _) -> "nterm:"
  | `Dir uri -> uri
  | `HBugs `Tutors -> "hbugs:/tutors/"
  | `Metadata meta ->
      "metadata:/" ^
      (match meta with
      | `Deps (dir, uri) ->
          "deps/" ^
          let suri =
            let suri = UriManager.string_of_uri uri in
            let len = String.length suri in
            String.sub suri 4 (len - 4) in (* strip "cic:" prefix *)
          (match dir with | `Fwd -> "forward" | `Back -> "backward") ^ suri)
  | `Uri uri -> UriManager.string_of_uri uri
  | `NRef nref -> NReference.string_of_reference nref
  | `Whelp (query, _) -> query
  | `Univs uri -> "univs:" ^ UriManager.string_of_uri uri

let entry_of_string = function
  | "about:blank" -> `About `Blank
  | "about:proof" -> `About `Current_proof
  | "about:us"    -> `About `Us
  | "about:hints"    -> `About `Hints
  | "about:coercions?tred=true"    -> `About `Coercions
  | "about:coercions"    -> `About `CoercionsFull
  | "about:tex"    -> `About `TeX
  | "about:grammar"    -> `About `Grammar
  | _ ->  (* only about entries supported ATM *)
      raise (Invalid_argument "entry_of_string")

class type mathViewer =
  object
    (** @param reuse if set reused last opened cic browser otherwise 
     *  opens a new one. default is false
     *)
    method show_entry: ?reuse:bool -> mathViewer_entry -> unit
    method show_uri_list:
      ?reuse:bool -> entry:mathViewer_entry -> UriManager.uri list -> unit
    method screenshot: 
      GrafiteTypes.status -> NCic.metasenv -> NCic.metasenv ->
        NCic.substitution -> string -> unit
  end
