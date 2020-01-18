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

module L  = List

module U  = NUri
module US = U.UriSet
module R  = NReference
module C  = NCic
module P  = NCicPp
module E  = NCicEnvironment

module O  = Options

type status = {
(* current complexity *)
  c: int;
(* current uri *)
  u: U.uri;
}

let status = new P.status

let malformed () =
  failwith "probe: malformed term"

let add_name str =
  let u = U.uri_of_string str in
  if US.mem u !O.names then Printf.eprintf "probe: name clash: %S\n" str;
  O.names := US.add u !O.names

let add_attr n (_, xf, _) = O.add_xflavour n (xf:>O.def_xflavour)

let add_ind n = O.add_xflavour n `Inductive

let rec set_list c ts cts =
  let map cts t = (c, t) :: cts in
  L.fold_left map cts ts

let set_funs c rfs cts =
  let map cts (_, s, _, t0, t1) =
    add_name s;
    set_list c [t0; t1] cts
  in
  L.fold_left map cts rfs

let set_type c cts (_, s, t, css) =
  let map cts (_, s, t) = add_name s; (c, t) :: cts in
  add_name s; (c, t) :: L.fold_left map cts css

let inc st = {st with c = succ st.c}

let add st c = {st with c = st.c + c}

let scan_lref st c i =
  try match List.nth c (pred i) with
    | _, C.Decl _ -> inc st
    | _, C.Def  _ -> st
  with
    | Failure _ -> inc st

let scan_gref st = function
  | R.Ref (u, R.Decl)
  | R.Ref (u, R.Ind _)
  | R.Ref (u, R.Con _)   ->
    O.add_dep st.u u;
    inc st
  | R.Ref (u, R.Def _)
  | R.Ref (u, R.Fix _)
  | R.Ref (u, R.CoFix _) ->
    O.add_dep st.u u;
    if US.mem u !O.objs then st else inc st

let rec scan_term st = function
  | []                                 -> st
  | (_, C.Meta _)                :: tl
  | (_, C.Implicit _)            :: tl -> scan_term st tl
  | (_, C.Sort _)                :: tl -> scan_term (inc st) tl
  | (c, C.Rel i)                 :: tl -> scan_term (scan_lref st c i) tl
  | (_, C.Const p)               :: tl -> scan_term (scan_gref st p) tl
  | (_, C.Appl [])               :: tl -> malformed ()
  | (c, C.Appl ts)               :: tl ->
    scan_term (add st (pred (L.length ts))) (set_list c ts tl)
  | (c, C.Match (_, t0, t1, ts)) :: tl ->
    scan_term st (set_list c (t0::t1::ts) tl)
  | (c, C.Prod (s, t0, t1))      :: tl
  | (c, C.Lambda (s, t0, t1))    :: tl ->
    scan_term (inc st) ((c, t0) :: ((s, C.Decl t0) :: c, t1) :: tl)
  | (c, C.LetIn (s, t0, t1, t2)) :: tl ->
    scan_term st ((c, t0) :: (c, t1) :: ((s, C.Def (t1, t0)) :: c, t2) :: tl)

let scan_obj u c =
  let st = {c; u} in
  let _, _, _, _, obj = E.get_checked_obj status u in
  let st = match obj with
    | C.Constant (_, s, None, t, m)     ->
      add_name s; add_attr 1 m;
      scan_term (inc st) [[], t]
    | C.Constant (_, s, Some t0, t1, m) ->
      add_name s; add_attr 1 m;
      scan_term (inc st) (set_list [] [t0; t1] [])
    | C.Fixpoint (_, rfs, m)            ->
      add_attr (L.length rfs) m;
      scan_term (add st (L.length rfs)) (set_funs [] rfs [])
    | C.Inductive (_, _, its, _)        ->
      add_ind (L.length its);
      let cts = L.fold_left (set_type []) [] its in
      scan_term (add st (L.length cts)) cts
  in
  st.c

let accept_obj u =
  let _, _, _, _, obj = E.get_checked_obj status u in
  let g = match obj with
    | C.Constant (_, _, _, _, (g, _, _))
    | C.Fixpoint (_, _, (g, _, _))
    | C.Inductive (_, _, _, (g, _))    -> g
  in
  if L.mem g !O.exclude then false else true

let scan () =
  if !O.exclude <> [] then
    O.objs := US.filter accept_obj !O.objs;
  O.net := US.fold scan_obj !O.objs !O.net
