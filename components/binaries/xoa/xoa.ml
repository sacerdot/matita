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

module R = Helm_registry

module L = Lib
module A = Ast
module E = Engine

let incremental = ref true
let separate = ref false
let base = ref Filename.current_dir_name

let clear () =
  incremental := true;
  separate := false;
  base := Filename.current_dir_name;
  R.clear ()

let unm_ex s =
  Scanf.sscanf s "%u %u" A.mk_exists

let unm_or s =
  Scanf.sscanf s "%u" A.mk_or

let unm_and s =
  Scanf.sscanf s "%u" A.mk_and

let local name =
  Filename.concat (R.get_string "xoa.baseuri") name

let process_centralized dir =
  if R.has "xoa.objects" && R.has "xoa.notations" then begin
    let ooch = L.open_out true !base dir (R.get_string "xoa.objects") in
    let noch = L.open_out false !base dir (R.get_string "xoa.notations") in
    List.iter (L.out_include ooch) (R.get_list R.string "xoa.include");
    L.out_include ooch (R.get_string "xoa.notations" ^ ".ma");
    List.iter (E.generate ooch noch) (R.get_list unm_ex "xoa.ex");
    List.iter (E.generate ooch noch) (R.get_list unm_or "xoa.or");
    List.iter (E.generate ooch noch) (R.get_list unm_and "xoa.and");
    close_out noch; close_out ooch
  end

let generate (dir, o, n) d =
  let oname, nname = match d with
    | A.Exists (c, v) ->
      let oname = Printf.sprintf "%s/ex_%u_%u" o c v in
      let nname = Printf.sprintf "%s/ex_%u_%u" n c v in
      oname, nname
    | A.Or c          ->
      let oname = Printf.sprintf "%s/or_%u" o c in
      let nname = Printf.sprintf "%s/or_%u" n c in
      oname, nname
    | A.And c         ->
      let oname = Printf.sprintf "%s/and_%u" o c in
      let nname = Printf.sprintf "%s/and_%u" n c in
      oname, nname
  in
  if !incremental &&
     L.exists_out !base dir oname &&
     L.exists_out !base dir nname
  then () else
  begin
    let ooch = L.open_out true !base dir oname in
    let noch = L.open_out false !base dir nname in
    List.iter (L.out_include ooch) (R.get_list R.string "xoa.include");
    L.out_include ooch (local (nname ^ ".ma"));
    E.generate ooch noch d;
    close_out noch; close_out ooch
  end

let process_distributed dir =
  if R.has "xoa.objects" && R.has "xoa.notations" then begin
    let st = dir, R.get_string "xoa.objects", R.get_string "xoa.notations" in
    List.iter (generate st) (R.get_list unm_ex "xoa.ex");
    List.iter (generate st) (R.get_list unm_or "xoa.or");
    List.iter (generate st) (R.get_list unm_and "xoa.and");
  end

let process dir =
  L.load_conf !base dir;
  if !separate then process_distributed dir else process_centralized dir

let _ =
  let help = "Usage: xoa [ -Xsu | -b <dir> | <dir> ]*\n" in
  let help_X  = " Clear configuration" in
  let help_b  = "<dir>  Set this base directory (default: .)" in
  let help_s  = " Generate separate objects (default: false)" in
  let help_u  = " Update existing separate files (default: false)" in

  Arg.parse [
    "-X", Arg.Unit clear, help_X;
    "-b", Arg.String ((:=) base), help_b;
    "-s", Arg.Set separate, help_s;
    "-u", Arg.Clear incremental, help_u;
  ] process help
