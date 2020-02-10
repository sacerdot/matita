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
    let b = compare hd1 hd2 in
    if b > 0 then hd2 :: aux l1 tl2
    else if b < 0 then hd1 :: aux tl1 l2
    else raise_error (error hd1)
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

let rec list_apply prop map n = function
  | []       -> false
  | hd :: tl ->
    if prop n hd then begin map hd; true end
    else list_apply prop map (succ n) tl

let list_nth map n l =
  let prop m _ = m = n in
  if list_apply prop map 0 l then () else raise_error ET.ENoEntry

let list_split prop map l =
  let lt, lf = List.partition prop l in
  List.iter map lt; lf, lt

let rec list_count p s c = function
  | []      -> s, c
  | x :: tl -> list_count p (s + if p x then 1 else 0) (succ c) tl

(* stage *)

let string_of_stage v =
  String.concat "." (List.map string_of_int v)

let stage_of_string s =
  List.map int_of_string (String.split_on_char '.' s)

let stage_compare v1 v2 =
  list_compare compare v1 v2

(* name *)

let string_of_name n =
  String.concat "_" n

let name_of_string s =
  String.split_on_char '_' s

let name_compare n1 n2 =
  list_compare compare n1 n2

(* nobj *)

let string_of_nobj n =
  string_of_name n.ET.nn

let nobj_of_string s = {
  ET.nb = false; ET.nn = name_of_string s;
}

let nobj_selected n = n.ET.nb

let nobj_select n =
  n.ET.nb <- not n.ET.nb

let nobj_compare n1 n2 =
  name_compare n1.ET.nn n2.ET.nn

let nobj_union ns1 ns2 =
  let error n = ET.ENClash n in
  list_union error nobj_compare ns1 ns2

(* oobj *)

let string_of_oobj o =
  Printf.sprintf "%s/%s" (string_of_stage o.ET.os) (string_of_name o.ET.on)

let oobj_of_string s =
  match String.split_on_char '/' s with
  | [ss;sn] -> {ET.ob = false; ET.os = stage_of_string ss; ET.on = name_of_string sn}
  | _       -> failwith "oobj_of_string"

let oobj_selected o = o.ET.ob

let oobj_select o =
  o.ET.ob <- not o.ET.ob

let oobj_compare o1 o2 =
  let b = stage_compare o1.ET.os o2.ET.os in
  if b = 0 then name_compare o1.ET.on o2.ET.on else b

let oobj_union os1 os2 =
  let error o = ET.EOClash o in
  list_union error oobj_compare os1 os2

let oobj_of_nobj v n =
  {ET.ob = n.ET.nb; ET.os = v; ET.on = n.ET.nn} 

let rec oobj_match oi ni os ns =
  match os, ns with
  | _       , []       -> None
  | []      , _        -> None
  | o :: otl, n :: ntl ->
    let b = name_compare o.ET.on n.ET.nn in
    if b > 0 then oobj_match oi (succ ni) os ntl else
    if b < 0 then oobj_match (succ oi) ni otl ns else
    Some (oi, ni)

(* robj *)

let oobj_of_robj r =
  let n = match r.ET.rn with
    | []     -> []
    | n :: _ -> n.ET.nn
  in
  {ET.ob = r.ET.rb; ET.os = r.ET.rs; ET.on = n}

let string_of_robj r =
  string_of_oobj (oobj_of_robj r)

let robj_selected r = r.ET.rb

let robj_select r =
  r.ET.rb <- not r.ET.rb

let robj_expand r =
  r.ET.rx <- not r.ET.rx

let robj_compare r1 r2 =
  oobj_compare (oobj_of_robj r1) (oobj_of_robj r2)

let robj_union rs1 rs2 =
  let error r = ET.ERClash r in
  list_union error robj_compare rs1 rs2

let rec robj_tops v = function
  | []      -> [], []
  | r :: tl ->
    let ds, ts = robj_tops v tl in
    if stage_compare v r.ET.rs = 0 then begin
      if r.ET.rn = [] then oobj_union r.ET.ro ds, ts else
      let tops = List.rev_map (oobj_of_nobj v) r.ET.rn in
      ds, oobj_union (List.rev tops) ts
    end else
      ds, ts

let robj_split s rs =
  let rec aux rs os ns = function
  | []      -> List.rev rs, os, ns
  | r :: tl ->
    if stage_compare s r.ET.rs <> 0 then aux (r :: rs) os ns tl else
    if r.ET.rb then aux rs (oobj_union os r.ET.ro) (nobj_union ns r.ET.rn) tl else
    let ro, so = list_split oobj_selected oobj_select r.ET.ro in
    let rn, sn = list_split nobj_selected nobj_select r.ET.rn in
    if ro = [] && rn = [] then aux rs (oobj_union os so) (nobj_union ns sn) tl else begin
      r.ET.ro <- ro; r.ET.rn <- rn;
      aux (r :: rs) (oobj_union os so) (nobj_union ns sn) tl
    end
  in
  aux [] [] [] rs

(* status *)

let new_status = {
  ET.sm = false; ET.sr = []; ET.ss = []; ET.so = []; ET.sn = [];
}

(* pointer *)

let string_of_pointer = string_of_stage

let pointer_of_string = stage_of_string

let list_visit before each visit after selected string_of p l =
  let ptr p = string_of_pointer (List.rev p) in
  let rec aux i = function
    | []      -> ()
    | x :: tl ->
      each (ptr (i::p)) (selected x) (string_of x);
      visit (i::p) x;
      aux (succ i) tl
  in
  let s, c = list_count selected 0 0 l in
  let count = Printf.sprintf "%u/%u" s c in
  before (ptr p) count;
  aux 0 l;
  after ()

(* error *)

let string_of_error = function
  | ET.EWrongExt x         ->
    Printf.sprintf "unknown input file type %S" x
  | ET.EStage v            ->
    Printf.sprintf "current stage %S" (string_of_stage v)
  | ET.ENoStage            ->
    Printf.sprintf "current stage not defined"
  | ET.EWaiting            ->
    Printf.sprintf "current stage not finished"
  | ET.ENClash n           ->
    Printf.sprintf "name clash %S" (string_of_nobj n)
  | ET.EOClash o           ->
    Printf.sprintf "object clash %S" (string_of_oobj o)
  | ET.ERClash r           ->
    Printf.sprintf "role clash %S" (string_of_robj r)
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
