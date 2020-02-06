(*
    ||M||  This file is part of HELM, an Hypertextual, Electronic
    ||A||  Library of Mathematics, developed at the Computer Science
    ||T||  Department, University of Bologna, Italy.
    ||I||
    ||T||  HELM is free software; you can redistribute it and/or
    ||A||  modify it under the terms of the GNU General Public License
    \   /  version 2 or (at your option) any later version.
     \ /   This software is distributed as is, NO WARRANTY.
      V_______________________________________________________________ *)

module ET = RolesTypes

let raise_error e =
  raise (ET.Error e)

let list_union error compare l1 l2 =
  let rec aux l1 l2 = match l1 with
  | []       -> l2
  | hd1::tl1 -> match l2 with
  | []       -> l1
  | hd2::tl2 ->
    let b = compare (snd hd1) (snd hd2) in
    if b > 0 then hd2 :: aux l1 tl2
    else if b < 0 then hd1 :: aux tl1 l2
    else raise_error (error (snd hd1))
  in
  aux l1 l2

let list_compare compare l1 l2 =
  let rec aux l1 l2 = match l1 with
  | []       ->
    if l2 = [] then 0 else -1
  | hd1::tl1 -> match l2 with
  | []       -> 1
  | hd2::tl2 ->
    let b = compare hd1 hd2 in
    if b = 0 then aux tl1 tl2 else b
  in
  aux l1 l2

let rec list_nth n = function
  | []         -> raise_error ET.ENoEntry
  | (_,hd)::tl -> if n = 0 then hd else list_nth (pred n) tl

let rec list_toggle n = function
  | []         -> raise_error ET.ENoEntry
  | (b,hd)::tl -> if n = 0 then (not b,hd)::tl else (b,hd)::list_toggle (pred n) tl

let rec list_toggle_all = function
  | []         -> []
  | (b,hd)::tl -> (not b,hd)::list_toggle_all tl

let rec list_split = function
  | []                -> [], []
  | (b,a) as hd :: tl ->
    let fs,ts = list_split tl in
    if fst hd then fs,((false,a)::ts)
    else (hd::fs),ts

let rec list_select r = function
  | []         -> r
  | (b,hd)::tl ->
    begin match b, r with
    | false, _      -> list_select r tl
    | true , None   -> list_select (Some hd) tl
    | true , Some _ -> raise_error (ET.EWrongSelect)
    end

let rec list_exists compare = function
  | []        -> false
  | (_,a)::tl ->
    let b = compare a in
    if b <= 0 then b = 0 else
    list_exists compare tl

let rec list_count s c = function
  | []         -> s, c
  | (b, _)::tl -> list_count (s + if b then 1 else 0) (succ c) tl

let string_of_version v =
  String.concat "." (List.map string_of_int v)

let version_of_string s =
  List.map int_of_string (String.split_on_char '.' s)

let compare_versions v1 v2 =
  list_compare compare v1 v2

let string_of_name n =
  String.concat "_" n

let name_of_string s =
  String.split_on_char '_' s

let compare_names n1 n2 =
  list_compare compare n1 n2

let names_union ns1 ns2 =
  let error n = ET.ENameClash n in
  list_union error compare_names ns1 ns2

let string_of_obj (v,n) =
  Printf.sprintf "%s/%s" (string_of_version v) (string_of_name n)

let obj_of_string s =
  match String.split_on_char '/' s with
  | [sv;sn] -> version_of_string sv, name_of_string sn
  | _       -> failwith "obj_of_string"

let compare_objs (v1,n1) (v2,n2) =
  let b = compare_versions v1 v2 in
  if b = 0 then compare_names n1 n2 else b

let objs_union os1 os2 =
  let error o = ET.EObjClash o in
  list_union error compare_objs os1 os2

let rec rev_objs_of_names v os = function
  | []        -> os
  | (b,n)::tl -> rev_objs_of_names v ((b,(v,n))::os) tl

let obj_of_role r =
  let n = match r.ET.n with
    | []        -> []
    | (_,n):: _ -> n
  in
  r.ET.v, n

let string_of_role r =
  string_of_obj (obj_of_role r)

let compare_roles r1 r2 =
  compare_objs (obj_of_role r1) (obj_of_role r2)

let roles_union rs1 rs2 =
  let error r = ET.ERoleClash r in
  list_union error compare_roles rs1 rs2

let exists_role_deleted v r =
  let o = v, [] in
  let compare r = compare_objs o (obj_of_role r) in
  list_exists compare r

let rec get_tops v = function
  | []        -> [], []
  | (_,r)::tl ->
    let ds, ts = get_tops v tl in
    if compare_versions v r.ET.v = 0 then begin
      if r.ET.n = [] then objs_union r.ET.o ds, ts else
      let tops = rev_objs_of_names v [] r.ET.n in
      ds, objs_union (List.rev tops) ts
    end else
      ds, ts

let rec match_names oi ni os ns =
  match os, ns with
  | _         , []        -> None
  | []        , _         -> None
  | (_,o)::otl,(_,n)::ntl ->
    let b = compare_names (snd o) n in
    if b > 0 then match_names oi (succ ni) os ntl else
    if b < 0 then match_names (succ oi) ni otl ns else
    Some (oi, ni)

let new_status = {
  ET.r = []; ET.s = []; ET.t = []; ET.w = [];
}

let string_of_pointer = string_of_version

let pointer_of_string = version_of_string

let list_visit before each visit after string_of p l =
  let ptr p = string_of_pointer (List.rev p) in
  let rec aux i = function
    | []         -> ()
    | (b, x)::tl ->
      each (ptr (i::p)) b (string_of x);
      visit (i::p) x;
      aux (succ i) tl
  in
  let s, c = list_count 0 0 l in
  let count = Printf.sprintf "%u/%u" s c in
  before (ptr p) count;
  aux 0 l;
  after ()

let string_of_error = function
  | ET.EWrongExt x         ->
    Printf.sprintf "unknown input file type %S" x
  | ET.EStage v            ->
    Printf.sprintf "current stage %S" (string_of_version v)
  | ET.ENoStage            ->
    Printf.sprintf "current stage not defined"
  | ET.EWaiting            ->
    Printf.sprintf "current stage not finished"
  | ET.ENameClash n        ->
    Printf.sprintf "name clash %S" (string_of_name n)
  | ET.EObjClash o         ->
    Printf.sprintf "object clash %S" (string_of_obj o)
  | ET.ERoleClash r        ->
    Printf.sprintf "role clash %S" (string_of_role r)
  | ET.ENoEntry            ->
    Printf.sprintf "entry not found"
  | ET.EWrongSelect        ->
    Printf.sprintf "selected role is not unique"
  | ET.EWrongVersion       ->
    Printf.sprintf "selected role is not in the current stage"
  | ET.ETops               ->
    Printf.sprintf "top objects already computed"
  | ET.EWrongRequest (r,a) ->
    Printf.sprintf "unknown request \"%s=%s\"" r a
