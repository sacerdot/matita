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

let string_of_version v =
  String.concat "." (List.map string_of_int v)

let version_of_string s =
  List.map int_of_string (String.split_on_char '.' s)

let string_of_name n =
  String.concat "_" n

let name_of_string s =
  String.split_on_char '_' s

let compare_names n1 n2 =
  list_compare compare n1 n2

let string_of_obj (v,n) =
  Printf.sprintf "%s/%s" (string_of_version v) (string_of_name n) 

let obj_of_string s =
  match String.split_on_char '/' s with
  | [sv;sn] -> version_of_string sv, name_of_string sn 
  | _       -> failwith "obj_of_string"

let new_status = {
  ET.r = []; ET.s = []; ET.t = []; ET.w = [];
}

let pointer_of_string = version_of_string

let string_of_error = function
  | ET.EExt x       ->
    Printf.sprintf "unknown input file type %S" x
  | ET.EStage v     ->
    Printf.sprintf "current stage %S" (string_of_version v)
  | ET.ENoStage     ->
    Printf.sprintf "current stage not defined"
  | ET.ENews        ->
    Printf.sprintf "current stage not finished"
  | ET.ENameClash n ->
    Printf.sprintf "name clash %S" (string_of_name n)
  | ET.ENoEntry     ->
    Printf.sprintf "entry not found"
