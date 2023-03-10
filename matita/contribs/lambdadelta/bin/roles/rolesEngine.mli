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

val new_stage: RolesTypes.stage -> unit

val select_entry: RolesTypes.pointer -> unit

val expand_entry: RolesTypes.pointer -> unit

val make_tops: unit -> unit

val add_role: unit -> unit

val add_tops: RolesTypes.stage -> unit

val add_matching: unit -> unit

val remove_roles: unit -> unit

val read_waiting: string -> unit

val read_status: unit -> unit

val write_status: unit -> unit

val print_status: unit -> unit

val visit_status:
  (string -> string -> unit) -> RolesTypes.each ->
  (bool -> bool -> bool -> unit) -> (bool -> unit) -> (unit -> unit) ->
  (string -> bool -> unit) ->
  (string -> string -> unit) -> RolesTypes.each -> (unit -> unit) ->
  (string -> string -> unit) -> RolesTypes.each -> (unit -> unit) ->
  unit
