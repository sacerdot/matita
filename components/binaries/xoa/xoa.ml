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

let clear () =
  incremental := true;
  separate := false;
  R.clear ()

let unm_ex s =
  Scanf.sscanf s "%u %u" A.mk_exists

let unm_or s =
  Scanf.sscanf s "%u" A.mk_or

let unm_and s =
  Scanf.sscanf s "%u" A.mk_and

let process_centralized conf =
  let preamble = L.get_preamble conf in
  if R.has "xoa.objects" && R.has "xoa.notations" then begin
    let ooch = L.open_out true preamble (R.get_string "xoa.objects") in
    let noch = L.open_out false preamble (R.get_string "xoa.notations") in
    List.iter (L.out_include ooch) (R.get_list R.string "xoa.include");
    L.out_include ooch (R.get_string "xoa.notations" ^ ".ma");
    List.iter (E.generate ooch noch) (R.get_list unm_ex "xoa.ex");
    List.iter (E.generate ooch noch) (R.get_list unm_or "xoa.or");
    List.iter (E.generate ooch noch) (R.get_list unm_and "xoa.and");
    close_out noch; close_out ooch
  end

let generate (p, o, n) d =
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
  if !incremental && L.exists_out oname && L.exists_out nname then () else
  begin
    let ooch = L.open_out true p oname in
    let noch = L.open_out false p nname in
    List.iter (L.out_include ooch) (R.get_list R.string "xoa.include");
    L.out_include ooch (nname ^ ".ma");
    E.generate ooch noch d;
    close_out noch; close_out ooch
  end

let process_distributed conf =
  let preamble = L.get_preamble conf in
  if R.has "xoa.objects" && R.has "xoa.notations" then begin
    let st = preamble, R.get_string "xoa.objects", R.get_string "xoa.notations" in
    List.iter (generate st) (R.get_list unm_ex "xoa.ex");
    List.iter (generate st) (R.get_list unm_or "xoa.or");
    List.iter (generate st) (R.get_list unm_and "xoa.and");
  end

let process conf =
  if !separate then process_distributed conf else process_centralized conf

let _ =
  let help = "Usage: xoa [ -Xs | <configuration file> ]*\n" in
  let help_X  = " Clear configuration" in
  let help_s  = " Generate separate objects" in
  let help_u  = " Update existing separate files" in
  Arg.parse [
    "-X", Arg.Unit clear, help_X;
    "-s", Arg.Set separate, help_s;
    "-u", Arg.Clear incremental, help_u;
  ] process help
