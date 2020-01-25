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
  if st.ET.w = [] then st.ET.s <- v
  else EU.raise_error ET.ENews

let toggle_entry = function
  | [0]       -> st.ET.r <- EU.list_toggle_all st.ET.r
  | [0;m]     -> st.ET.r <- EU.list_toggle m st.ET.r
  | [0;m;1]   ->
    let r = EU.list_nth m st.ET.r in
    r.ET.o <- EU.list_toggle_all r.ET.o
  | [0;m;1;n] -> 
    let r = EU.list_nth m st.ET.r in
    r.ET.o <- EU.list_toggle n r.ET.o
  | [0;m;2]   -> 
    let r = EU.list_nth m st.ET.r in
    r.ET.n <- EU.list_toggle_all r.ET.n
  | [0;m;2;n] -> 
    let r = EU.list_nth m st.ET.r in
    r.ET.n <- EU.list_toggle n r.ET.n
  | [1]        -> st.ET.t <- EU.list_toggle_all st.ET.t
  | [1;m]      -> st.ET.t <- EU.list_toggle m st.ET.t
  | [2]        -> st.ET.w <- EU.list_toggle_all st.ET.w
  | [2;m]      -> st.ET.w <- EU.list_toggle m st.ET.w
  | _          -> EU.raise_error ET.ENoEntry

let read_waiting fname =
  if st.ET.s = [] then EU.raise_error ET.ENoStage else
  let ich = Scanf.Scanning.open_in fname in
  let w = EI.read_names ich [] in
  Scanf.Scanning.close_in ich;
  let error n = ET.ENameClash n in
  st.ET.w <- EU.list_union error EU.compare_names st.ET.w (List.rev w)

let read_status () =
  if st.ET.s <> [] then EU.raise_error (ET.EStage st.ET.s) else
  let fname = Filename.concat !EG.wd "roles.osn" in
  let ich = open_in fname in
  let tmp = EI.read_status ich in
  close_in ich;
  st.ET.r <- tmp.ET.r;
  st.ET.s <- tmp.ET.s;
  st.ET.t <- tmp.ET.t;
  st.ET.w <- tmp.ET.w

let write_status () =
  let fname = Filename.concat !EG.wd "roles.osn" in
  let och = open_out fname in
  EO.out_status och st;
  close_out och
