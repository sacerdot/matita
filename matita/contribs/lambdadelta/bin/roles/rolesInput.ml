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

module EL = RolesLexer
module EP = RolesParser
module EU = RolesUtils

let input_string_opt ich =
  let map s = Some s in
  try Scanf.bscanf ich " %S" map
  with End_of_file -> None

let rec read_rev_nobjs ich nobjs =
  match input_string_opt ich with
  | None   -> nobjs
  | Some s -> read_rev_nobjs ich (EU.nobj_of_string s :: nobjs)

let read_status ich =
  let lexbuf = Lexing.from_channel ich in
  EP.status EL.token lexbuf
