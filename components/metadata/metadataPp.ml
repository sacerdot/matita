(* Copyright (C) 2004, HELM Team.
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

open MetadataTypes

let pp_relation r = 
  match r with
  | Eq i -> sprintf "= %d" i
  | Ge i -> sprintf ">= %d" i
  | Gt i -> sprintf "> %d" i
  | Le i -> sprintf "<= %d" i
  | Lt i -> sprintf "< %d" i

let pp_position = function
  | `MainConclusion (Some d) -> sprintf "MainConclusion(%s)" (pp_relation d)
  | `MainConclusion None -> sprintf "MainConclusion"
  | `MainHypothesis (Some d) -> sprintf "MainHypothesis(%s)" (pp_relation d)
  | `MainHypothesis None -> "MainHypothesis"
  | `InConclusion -> "InConclusion"
  | `InHypothesis -> "InHypothesis"
  | `InBody -> "InBody"

let pp_position_tag = function
  | `MainConclusion _ -> mainconcl_pos
  | `MainHypothesis _ -> mainhyp_pos
  | `InConclusion -> inconcl_pos
  | `InHypothesis -> inhyp_pos
  | `InBody -> inbody_pos

let columns_of_position pos =
  match pos with
  | `MainConclusion (Some (Eq d)) -> `String mainconcl_pos, `Int d
  | `MainConclusion None -> `String mainconcl_pos, `Null
  | `MainHypothesis (Some (Eq d)) -> `String mainhyp_pos, `Int d
  | `MainHypothesis None -> `String mainhyp_pos, `Null
  | `InConclusion -> `String inconcl_pos, `Null
  | `InHypothesis -> `String inhyp_pos, `Null
  | `InBody -> `String inbody_pos, `Null
  | _ -> assert false 

(*
let metadata_ns = "http://www.cs.unibo.it/helm/schemas/schema-helm"
let uri_of_pos pos = String.concat "#" [metadata_ns; pp_position pos]
*)

type t = [ `Int of int | `String of string | `Null ]

let columns_of_metadata_aux ~about metadata =
  let sort s = `String (CicPp.ppsort s) in
  let source = `String (UriManager.string_of_uri about) in
  let occurrence u = `String (UriManager.string_of_uri u) in
  List.fold_left
    (fun (sort_cols, rel_cols, obj_cols) metadata ->
      match metadata with
      | `Sort (s, p) ->
          let (p, d) = columns_of_position (p :> position) in
          [source; p; d; sort s] :: sort_cols, rel_cols, obj_cols
      | `Rel p ->
          let (p, d) = columns_of_position (p :> position) in
          sort_cols, [source; p; d] :: rel_cols, obj_cols
      | `Obj (o, p) ->
          let (p, d) = columns_of_position p in
          sort_cols, rel_cols,
          [source; occurrence o; p; d] :: obj_cols)
    ([], [], []) metadata

let columns_of_metadata metadata =
  List.fold_left
    (fun (sort_cols, rel_cols, obj_cols) (uri, _, metadata) ->
      let (s, r, o) = columns_of_metadata_aux ~about:uri metadata in
      (List.append sort_cols s, List.append rel_cols r, List.append obj_cols o))
    ([], [], []) metadata

let pp_constr =
  function
    | `Sort (sort, p) -> 
	sprintf "Sort %s; [%s]" 
	  (CicPp.ppsort sort) (String.concat ";" (List.map pp_position p))
    | `Rel p -> sprintf "Rel [%s]" (String.concat ";" (List.map pp_position p))
    | `Obj (uri, p) -> sprintf "Obj %s; [%s]" 
	(UriManager.string_of_uri uri) (String.concat ";" (List.map pp_position p))
 
(*
let pp_columns ?(sep = "\n") (sort_cols, rel_cols, obj_cols) =
  String.concat sep
    ([ "Sort" ] @ List.map Dbi.sdebug (sort_cols :> Dbi.sql_t list list) @
    [ "Rel" ] @ List.map Dbi.sdebug (rel_cols :> Dbi.sql_t list list) @
    [ "Obj" ] @ List.map Dbi.sdebug (obj_cols :> Dbi.sql_t list list))
*)


