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
  if st.ET.sn = [] then begin
    if EU.stage_compare st.ET.ss v <> 0 then begin
      st.ET.ss <- v; st.ET.sm <- true
    end
  end else EU.raise_error ET.EWaiting

let select_entry = function
  | [0]       -> List.iter EU.robj_select st.ET.sr
  | [0;m]     -> EU.list_nth EU.robj_select m st.ET.sr
  | [0;m;1]   ->
    let pred r = List.iter EU.oobj_select r.ET.ro in
    EU.list_nth pred m st.ET.sr
  | [0;m;1;n] ->
    let pred r = EU.list_nth EU.oobj_select n r.ET.ro in
    EU.list_nth pred m st.ET.sr
  | [0;m;2]   ->
    let pred r = List.iter EU.nobj_select r.ET.rn in
    EU.list_nth pred m st.ET.sr
  | [0;m;2;n] ->
    let pred r = EU.list_nth EU.nobj_select n r.ET.rn in
    EU.list_nth pred m st.ET.sr
  | [1]       -> List.iter EU.oobj_select st.ET.so
  | [1;n]     -> EU.list_nth EU.oobj_select n st.ET.so
  | [2]       -> List.iter EU.nobj_select st.ET.sn
  | [2;n]     -> EU.list_nth EU.nobj_select n st.ET.sn
  | _         -> EU.raise_error ET.ENoEntry

let expand_entry = function
  | [0]   -> List.iter EU.robj_expand st.ET.sr
  | [0;m] -> EU.list_nth EU.robj_expand m st.ET.sr
  | _     -> EU.raise_error ET.ENoEntry

let add_role () =
  let ts, os = EU.list_split EU.oobj_selected EU.oobj_select st.ET.so in
  let ws, ns = EU.list_split EU.nobj_selected EU.nobj_select st.ET.sn in
  if os = [] && ns = [] then () else
  let add r =
    r.ET.ro <- EU.oobj_union os r.ET.ro;
    r.ET.rn <- EU.nobj_union ns r.ET.rn;
    r.ET.rb <- false
  in
  let is_selected _ r = r.ET.rb && EU.stage_compare r.ET.rs st.ET.ss = 0 in
  let is_new _ r = r.ET.ro = [] && EU.stage_compare r.ET.rs st.ET.ss = 0 in
  let is_deleted _ r = r.ET.rn = [] && EU.stage_compare r.ET.rs st.ET.ss = 0 in
  begin 
    if EU.list_apply is_selected add 0 st.ET.sr then () else
    if os = [] && EU.list_apply is_new add 0 st.ET.sr then () else
    if ns = [] && EU.list_apply is_deleted add 0 st.ET.sr then () else
    let r = {ET.rb = false; ET.rx = false; ET.rs = st.ET.ss; ET.ro = os; ET.rn = ns} in
    st.ET.sr <- EU.robj_union st.ET.sr [r]
  end;
  st.ET.so <- ts; st.ET.sn <- ws; st.ET.sm <- true

let add_tops v =
  let prop _ r = EU.stage_compare r.ET.rs v = 0 && r.ET.rn = [] in
  if EU.list_apply prop ignore 0 st.ET.sr || st.ET.so <> []
  then EU.raise_error ET.ETops else
  let ds, ts = EU.robj_tops v st.ET.sr in
  if ds <> [] then begin
    let r = {ET.rb = false; ET.rx = false; ET.rs = st.ET.ss; ET.ro = ds; ET.rn = []} in
    st.ET.sr <- EU.robj_union [r] st.ET.sr
  end;
  if ts <> [] then st.ET.so <- ts;
  if ds <> [] || ts <> [] then st.ET.sm <- true

let rec add_matching () =
  match EU.oobj_match 0 0 st.ET.so st.ET.sn with
  | None          -> ()
  | Some  (ti,wi) ->
    select_entry [1;ti];
    select_entry [2;wi];
    add_role ();
    add_matching ()

let remove_roles () =
  let rs, os, ns = EU.robj_split st.ET.ss st.ET.sr in
  if os = [] && ns = [] then () else begin
    st.ET.so <- EU.oobj_union os st.ET.so; 
    st.ET.sn <- EU.nobj_union ns st.ET.sn; 
    st.ET.sr <- rs; st.ET.sm <- true
  end

let read_waiting fname =
  if EU.stage_compare st.ET.ss [] = 0 then EU.raise_error ET.ENoStage else
  let ich = Scanf.Scanning.open_in fname in
  let ws = EI.read_rev_nobjs ich [] in
  Scanf.Scanning.close_in ich;
  let map ws w = EU.nobj_union ws [w] in
  st.ET.sn <- List.fold_left map st.ET.sn ws;
  if ws <> [] then st.ET.sm <- true

let read_status () =
  if EU.stage_compare st.ET.ss [] <> 0 then EU.raise_error (ET.EStage st.ET.ss) else
  let fname = Filename.concat !EG.cwd "roles.osn" in
  let ich = open_in fname in
  let tmp = EI.read_status ich in
  close_in ich;
  st.ET.sm <- tmp.ET.sm;
  st.ET.sr <- tmp.ET.sr;
  st.ET.ss <- tmp.ET.ss;
  st.ET.so <- tmp.ET.so;
  st.ET.sn <- tmp.ET.sn

let write_status () =
  let fname = Filename.concat !EG.cwd "roles.osn" in
  let och = open_out fname in
  EO.out_status och st;
  close_out och;
  st.ET.sm <- false

let print_status () =
  EO.out_status stdout st

let visit_status
  before_r each_r before after after_r stage
  before_t each_t after_t before_w each_w after_w =
  let visit_tw _ _ = () in
  let visit_r p r =
    before r.ET.rx (r.ET.ro=[]) (r.ET.rn=[]);
    if r.ET.rx then begin
      EU.list_visit before_t each_t visit_tw after_t EU.oobj_selected EU.key_of_oobj EU.string_of_oobj (1::p) r.ET.ro;
      EU.list_visit before_w each_w visit_tw after_w EU.nobj_selected EU.key_of_nobj EU.string_of_nobj (2::p) r.ET.rn
    end;
    after r.ET.rx
  in
  EU.list_visit before_r each_r visit_r after_r EU.robj_selected EU.key_of_robj EU.string_of_robj [0] st.ET.sr;
  stage (EU.string_of_stage st.ET.ss) st.ET.sm;
  EU.list_visit before_t each_t visit_tw after_t EU.oobj_selected EU.key_of_oobj EU.string_of_oobj [1] st.ET.so;
  EU.list_visit before_w each_w visit_tw after_w EU.nobj_selected EU.key_of_nobj EU.string_of_nobj [2] st.ET.sn
