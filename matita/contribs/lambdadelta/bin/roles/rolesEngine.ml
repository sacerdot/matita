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

module EG = RolesGlobal
module EI = RolesInput
module EO = RolesOutput
module EU = RolesUtils
module ET = RolesTypes

let st = EU.new_status

let new_stage v =
  if st.ET.w = [] then begin
    if EU.compare_versions st.ET.s v <> 0 then begin
      st.ET.s <- v; st.ET.m <- true
    end
  end else EU.raise_error ET.EWaiting

let select_entry = function
  | [0]       -> st.ET.r <- EU.list_select_all st.ET.r
  | [0;m]     -> st.ET.r <- EU.list_select m st.ET.r
  | [0;m;1]   ->
    let r = EU.list_nth m st.ET.r in
    r.ET.o <- EU.list_select_all r.ET.o
  | [0;m;1;n] ->
    let r = EU.list_nth m st.ET.r in
    r.ET.o <- EU.list_select n r.ET.o
  | [0;m;2]   ->
    let r = EU.list_nth m st.ET.r in
    r.ET.n <- EU.list_select_all r.ET.n
  | [0;m;2;n] ->
    let r = EU.list_nth m st.ET.r in
    r.ET.n <- EU.list_select n r.ET.n
  | [1]       -> st.ET.t <- EU.list_select_all st.ET.t
  | [1;m]     -> st.ET.t <- EU.list_select m st.ET.t
  | [2]       -> st.ET.w <- EU.list_select_all st.ET.w
  | [2;m]     -> st.ET.w <- EU.list_select m st.ET.w
  | _         -> EU.raise_error ET.ENoEntry

let expand_entry = function
  | [0]   -> EU.roles_expand_all st.ET.r
  | [0;m] -> EU.roles_expand m st.ET.r
  | _     -> EU.raise_error ET.ENoEntry

let add_role () =
  let ts,os = EU.list_split st.ET.t in
  let ws,ns = EU.list_split st.ET.w in
  if os = [] && ns = [] then () else
  begin match EU.list_find_selected None st.ET.r with
  | None   ->
    let r = {ET.x = false; ET.v = st.ET.s; ET.o = os; ET.n = ns} in
    st.ET.r <- EU.roles_union [false, r] st.ET.r
  | Some r ->
    if r.ET.v <> st.ET.s then EU.raise_error ET.EWrongVersion else
    r.ET.o <- EU.objs_union os r.ET.o;
    r.ET.n <- EU.names_union ns r.ET.n;
  end;
  st.ET.t <- ts; st.ET.w <- ws; st.ET.m <- true

let add_tops v =
  if EU.exists_role_deleted st.ET.s st.ET.r || st.ET.t <> []
  then EU.raise_error ET.ETops else
  let ds, ts = EU.get_tops v st.ET.r in
  if ds <> [] then begin
    let r = {ET.x = false; ET.v = st.ET.s; ET.o = ds; ET.n = []} in
    st.ET.r <- EU.roles_union [false, r] st.ET.r
  end;
  if ts <> [] then st.ET.t <- ts;
  if ds <> [] || ts <> [] then st.ET.m <- true

let rec add_matching () =
  match EU.match_names 0 0 st.ET.t st.ET.w with
  | None          -> ()
  | Some  (ti,wi) ->
    select_entry [1;ti];
    select_entry [2;wi];
    add_role ();
    add_matching ()

let remove_roles () =
  let rs, os, ns = EU.roles_split st.ET.s st.ET.r in
  if os = [] && ns = [] then () else begin
    st.ET.t <- EU.objs_union os st.ET.t; 
    st.ET.w <- EU.names_union ns st.ET.w; 
    st.ET.r <- rs; st.ET.m <- true
  end

let read_waiting fname =
  if st.ET.s = [] then EU.raise_error ET.ENoStage else
  let ich = Scanf.Scanning.open_in fname in
  let ws = EI.read_rev_names ich [] in
  Scanf.Scanning.close_in ich;
  let map ws w = EU.names_union ws [w] in
  st.ET.w <- List.fold_left map st.ET.w ws;
  if ws <> [] then st.ET.m <- true

let read_status () =
  if st.ET.s <> [] then EU.raise_error (ET.EStage st.ET.s) else
  let fname = Filename.concat !EG.cwd "roles.osn" in
  let ich = open_in fname in
  let tmp = EI.read_status ich in
  close_in ich;
  st.ET.m <- tmp.ET.m;
  st.ET.r <- tmp.ET.r;
  st.ET.s <- tmp.ET.s;
  st.ET.t <- tmp.ET.t;
  st.ET.w <- tmp.ET.w

let write_status () =
  let fname = Filename.concat !EG.cwd "roles.osn" in
  let och = open_out fname in
  EO.out_status och st;
  close_out och;
  st.ET.m <- false

let print_status () =
  EO.out_status stdout st

let visit_status
  before_r each_r before after after_r stage
  before_t each_t after_t before_w each_w after_w =
  let visit_tw _ _ = () in
  let visit_r p r =
    if r.ET.x then begin
      before ();
      EU.list_visit before_t each_t visit_tw after_t EU.string_of_obj (1::p) r.ET.o;
      EU.list_visit before_w each_w visit_tw after_w EU.string_of_name (2::p) r.ET.n;
      after ()
    end
  in
  EU.list_visit before_r each_r visit_r after_r EU.string_of_role [0] st.ET.r;
  stage (EU.string_of_version st.ET.s) st.ET.m;
  EU.list_visit before_t each_t visit_tw after_t EU.string_of_obj [1] st.ET.t;
  EU.list_visit before_w each_w visit_tw after_w EU.string_of_name [2] st.ET.w
