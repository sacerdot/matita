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

let is_main_pos = function
  | `MainConclusion _
  | `MainHypothesis _ -> true
  | _ -> false

let main_pos (pos: position): main_position =
  match pos with
  | `MainConclusion depth -> `MainConclusion depth
  | `MainHypothesis depth -> `MainHypothesis depth
  | _ -> assert false

let next_pos = function
  | `MainConclusion _ -> `InConclusion
  | `MainHypothesis _ -> `InHypothesis
  | pos -> pos

let string_of_uri = UriManager.string_of_uri

module OrderedMetadata =
  struct
    type t = MetadataTypes.metadata
    let compare m1 m2 = (* ignore universes in Cic.Type sort *)
      match (m1, m2) with
      | `Sort (Cic.Type _, pos1), `Sort (Cic.Type _, pos2) ->
          Pervasives.compare pos1 pos2
      | _ -> Pervasives.compare m1 m2
  end

module MetadataSet = Set.Make (OrderedMetadata)
module UriManagerSet = UriManager.UriSet

module S = MetadataSet

let unopt = function Some x -> x | None -> assert false

let incr_depth = function
  | `MainConclusion (Some (Eq depth)) -> `MainConclusion (Some (Eq (depth + 1)))
  | `MainHypothesis (Some (Eq depth)) -> `MainHypothesis (Some (Eq (depth + 1)))
  | _ -> assert false

let var_has_body uri =
  match CicEnvironment.get_obj CicUniv.oblivion_ugraph uri with
  | Cic.Variable (_, Some body, _, _, _), _ -> true
  | _ -> false

let compute_term pos term =
  let rec aux (pos: position) set = function
    | Cic.Var (uri, subst) when var_has_body uri ->
        (* handles variables with body as constants *)
        aux pos set (Cic.Const (uri, subst))
    | Cic.Rel _
    | Cic.Var _ ->
        if is_main_pos pos then
          S.add (`Rel (main_pos pos)) set
        else
          set
    | Cic.Meta (_, local_context) ->
        List.fold_left
          (fun set context ->
            match context with
            | None -> set
            | Some term -> aux (next_pos pos) set term)
          set
          local_context
    | Cic.Sort sort ->
        if is_main_pos pos then
          S.add (`Sort (sort, main_pos pos)) set
        else
          set
    | Cic.Implicit _ -> assert false
    | Cic.Cast (term, ty) ->
        (* TODO consider also ty? *)
        aux pos set term
    | Cic.Prod (_, source, target) ->
        (match pos with
        | `MainConclusion _ ->
            let set = aux (`MainHypothesis (Some (Eq 0))) set source in
            aux (incr_depth pos) set target
        | `MainHypothesis _ ->
            let set = aux `InHypothesis set source in
            aux (incr_depth pos) set target
        | `InConclusion
        | `InHypothesis
        | `InBody ->
            let set = aux pos set source in
            aux pos set target)
    | Cic.Lambda (_, source, target) ->
        (*assert (not (is_main_pos pos));*)
        let set = aux (next_pos pos) set source in
        aux (next_pos pos) set target
    | Cic.LetIn (_, term, _, target) ->
        if is_main_pos pos then
          aux pos set (CicSubstitution.subst term target)
        else
          let set = aux pos set term in
          aux pos set target
    | Cic.Appl [] -> assert false
    | Cic.Appl (hd :: tl) ->
        let set = aux pos set hd in
        List.fold_left
          (fun set term -> aux (next_pos pos) set term)
          set tl
    | Cic.Const (uri, subst) ->
        let set = S.add (`Obj (uri, pos)) set in
        List.fold_left
          (fun set (_, term) -> aux (next_pos pos) set term)
          set subst
    | Cic.MutInd (uri, typeno, subst) ->
        let uri = UriManager.uri_of_uriref uri typeno None in
        let set = S.add (`Obj (uri, pos)) set in
        List.fold_left (fun set (_, term) -> aux (next_pos pos) set term)
          set subst
    | Cic.MutConstruct (uri, typeno, consno, subst) ->
        let uri = UriManager.uri_of_uriref uri typeno (Some consno) in
        let set = S.add (`Obj (uri, pos)) set in
        List.fold_left (fun set (_, term) -> aux (next_pos pos) set term)
          set subst
    | Cic.MutCase (uri, _, outtype, term, pats) ->
        let pos = next_pos pos in
        let set = aux pos set term in
        let set = aux pos set outtype in
        List.fold_left (fun set term -> aux pos set term) set pats
    | Cic.Fix (_, funs) ->
        let pos = next_pos pos in
        List.fold_left
          (fun set (_, _, ty, body) ->
            let set = aux pos set ty in
            aux pos set body)
          set funs
    | Cic.CoFix (_, funs) ->
        let pos = next_pos pos in
        List.fold_left
          (fun set (_, ty, body) ->
            let set = aux pos set ty in
            aux pos set body)
          set funs
  in
  aux pos S.empty term

module OrderedInt =
struct
  type t = int
  let compare = Pervasives.compare
end

module IntSet = Set.Make (OrderedInt)

let compute_metas term =
  let rec aux in_hyp ((concl_metas, hyp_metas) as acc) cic =
    match cic with
    | Cic.Rel _
    | Cic.Sort _
    | Cic.Var _ -> acc
    | Cic.Meta (no, local_context) ->
        let acc =
          if in_hyp then
            (concl_metas, IntSet.add no hyp_metas)
          else
            (IntSet.add no concl_metas, hyp_metas)
        in
        List.fold_left
          (fun set context ->
            match context with
            | None -> set
            | Some term -> aux in_hyp set term)
          acc
          local_context
    | Cic.Implicit _ -> assert false
    | Cic.Cast (term, ty) ->
        (* TODO consider also ty? *)
        aux in_hyp acc term
    | Cic.Prod (_, source, target) ->
        if in_hyp then
          let acc = aux in_hyp acc source in
          aux in_hyp acc target
        else
          let acc = aux true acc source in
          aux in_hyp acc target
    | Cic.Lambda (_, source, target) ->
        let acc = aux in_hyp acc source in
        aux in_hyp acc target
    | Cic.LetIn (_, term, _, target) ->
        aux in_hyp acc (CicSubstitution.subst term target)
    | Cic.Appl [] -> assert false
    | Cic.Appl (hd :: tl) ->
        let acc = aux in_hyp acc hd in
        List.fold_left (fun acc term -> aux in_hyp acc term) acc tl
    | Cic.Const (_, subst)
    | Cic.MutInd (_, _, subst)
    | Cic.MutConstruct (_, _, _, subst) ->
        List.fold_left (fun acc (_, term) -> aux in_hyp acc term) acc subst
    | Cic.MutCase (uri, _, outtype, term, pats) ->
        let acc = aux in_hyp acc term in
        let acc = aux in_hyp acc outtype in
        List.fold_left (fun acc term -> aux in_hyp acc term) acc pats
    | Cic.Fix (_, funs) ->
        List.fold_left
          (fun acc (_, _, ty, body) ->
            let acc = aux in_hyp acc ty in
            aux in_hyp acc body)
          acc funs
    | Cic.CoFix (_, funs) ->
        List.fold_left
          (fun acc (_, ty, body) ->
            let acc = aux in_hyp acc ty in
            aux in_hyp acc body)
          acc funs
  in
  aux false (IntSet.empty, IntSet.empty) term

  (** type of inductiveType *)
let compute_type pos uri typeno (name, _, ty, constructors) =
  let consno = ref 0 in
  let type_metadata =
    (UriManager.uri_of_uriref uri typeno None, name, (compute_term pos ty))
  in
  let constructors_metadata =
    List.map
      (fun (name, term) ->
        incr consno;
        let uri = UriManager.uri_of_uriref uri typeno (Some !consno) in
        (uri, name, (compute_term pos term)))
      constructors
  in
  type_metadata :: constructors_metadata

let compute_ind pos ~uri ~types =
  let idx = ref ~-1 in
  List.map (fun ty -> incr idx; compute_type pos uri !idx ty) types

let compute (pos:position) ~body ~ty = 
  let type_metadata = compute_term pos ty in
  let body_metadata =
    match body with
    | None -> S.empty
    | Some body -> compute_term `InBody body
  in
  let uris =
    S.fold
      (fun metadata uris ->
        match metadata with
        | `Obj (uri, _) -> UriManagerSet.add uri uris
        | _ -> uris)
      type_metadata UriManagerSet.empty
  in
  S.union
    (S.filter
      (function
        | `Obj (uri, _) when UriManagerSet.mem uri uris -> false
        | _ -> true)
      body_metadata)
    type_metadata

let depth_offset params =
  let non p x = not (p x) in
  List.length (List.filter (non var_has_body) params)

let rec compute_var pos uri =
  let o, _ = CicEnvironment.get_obj CicUniv.oblivion_ugraph uri in
  match o with
    | Cic.Variable (_, Some _, _, _, _) -> S.empty
    | Cic.Variable (_, None, ty, params, _) ->
	let var_metadata = 
          List.fold_left
            (fun metadata uri ->
              S.union metadata (compute_var (next_pos pos) uri))
            S.empty
            params
        in
	(match pos with
	   | `MainHypothesis (Some (Eq 0)) -> 
	       let pos = `MainHypothesis (Some (Eq (depth_offset params))) in
               let ty_metadata = compute_term pos ty in
               S.union ty_metadata var_metadata
	   | `InHypothesis ->
               let ty_metadata = compute_term pos ty in
               S.union ty_metadata var_metadata
	   | _ -> assert false)
    | _ -> assert false 

let compute_obj uri =
  let o, _ = CicEnvironment.get_obj CicUniv.oblivion_ugraph uri in
  match o with
  | Cic.Variable (_, body, ty, params, _)
  | Cic.Constant (_, body, ty, params, _) -> 
      let pos = `MainConclusion (Some (Eq (depth_offset params))) in
      let metadata = compute pos ~body ~ty in
      let var_metadata = 
        List.fold_left
          (fun metadata uri ->
            S.union metadata (compute_var (`MainHypothesis (Some (Eq 0))) uri))
          S.empty
          params
      in
      [ uri, 
        UriManager.name_of_uri uri,
        S.union metadata var_metadata ]
  | Cic.InductiveDefinition (types, params, _, _) ->
      let pos = `MainConclusion(Some (Eq (depth_offset params))) in
      let metadata = compute_ind pos ~uri ~types in
      let var_metadata = 
        List.fold_left
          (fun metadata uri ->
            S.union metadata (compute_var (`MainHypothesis (Some (Eq 0))) uri))
          S.empty params
      in
      List.fold_left
        (fun acc m -> 
          (List.map (fun (uri,name,md) -> (uri,name,S.union md var_metadata)) m)
          @ acc)
        [] metadata
  | Cic.CurrentProof _ -> assert false    

let compute_obj uri = 
  List.map (fun (u, n, md) -> (u, n, S.elements md)) (compute_obj uri)
  
let compute ~body ~ty =
  S.elements (compute (`MainConclusion (Some (Eq 0))) ~body ~ty)

