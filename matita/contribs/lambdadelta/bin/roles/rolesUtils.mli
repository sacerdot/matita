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

val raise_error: RolesTypes.error -> 'a

val list_nth: int -> ('a * 'b) list -> 'b

val list_toggle: int -> (bool * 'b) list -> (bool * 'b) list

val list_toggle_all: (bool * 'b) list -> (bool * 'b) list

val list_split: (bool * 'b) list -> (bool * 'b) list * (bool * 'b) list

val list_select: 'b option -> (bool * 'b) list -> 'b option

val string_of_version: RolesTypes.version -> string

val version_of_string: string -> RolesTypes.version

val string_of_name: RolesTypes.name -> string

val name_of_string: string -> RolesTypes.name

val names_union: RolesTypes.names -> RolesTypes.names -> RolesTypes.names

val string_of_obj: RolesTypes.obj -> string

val obj_of_string: string -> RolesTypes.obj

val objs_union: RolesTypes.objs -> RolesTypes.objs -> RolesTypes.objs

val roles_union: RolesTypes.roles -> RolesTypes.roles -> RolesTypes.roles

val exists_role_deleted: RolesTypes.version -> RolesTypes.roles -> bool

val get_tops: RolesTypes.version -> RolesTypes.roles -> RolesTypes.objs * RolesTypes.objs

val match_names: int -> int -> RolesTypes.objs -> RolesTypes.names -> (int * int) option

val new_status: RolesTypes.status

val pointer_of_string: string -> RolesTypes.pointer

val string_of_error: RolesTypes.error -> string