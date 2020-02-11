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

val list_apply: (int -> 'a -> bool) -> ('a -> unit) -> int -> 'a list -> bool

val list_nth: ('a -> unit) -> int -> 'a list -> unit

val list_split: ('a -> bool) -> ('a -> unit) -> 'a list -> 'a list * 'a list

val list_visit:
  (string -> string -> unit) -> RolesTypes.each ->
  (RolesTypes.pointer -> 'a -> unit) -> (unit -> unit) ->
  ('a -> bool) -> ('a -> string) -> ('a -> string) -> RolesTypes.pointer -> 'a list -> unit

val string_of_stage: RolesTypes.stage -> string

val stage_of_string: string -> RolesTypes.stage

val stage_compare: RolesTypes.stage -> RolesTypes.stage -> int

val string_of_nobj: RolesTypes.nobj -> string

val nobj_of_string: string -> RolesTypes.nobj

val key_of_nobj: RolesTypes.nobj -> string

val nobj_selected: RolesTypes.nobj -> bool

val nobj_select: RolesTypes.nobj -> unit

val nobj_union: RolesTypes.nobjs -> RolesTypes.nobjs -> RolesTypes.nobjs

val string_of_oobj: RolesTypes.oobj -> string

val oobj_of_string: string -> RolesTypes.oobj

val key_of_oobj: RolesTypes.oobj -> string

val oobj_selected: RolesTypes.oobj -> bool

val oobj_select: RolesTypes.oobj -> unit

val oobj_union: RolesTypes.oobjs -> RolesTypes.oobjs -> RolesTypes.oobjs

val oobj_match: int -> int -> RolesTypes.oobjs -> RolesTypes.nobjs -> (int * int) option

val string_of_robj: RolesTypes.robj -> string

val key_of_robj: RolesTypes.robj -> string

val robj_selected: RolesTypes.robj -> bool

val robj_select: RolesTypes.robj -> unit

val robj_expand: RolesTypes.robj -> unit

val robj_union: RolesTypes.robjs -> RolesTypes.robjs -> RolesTypes.robjs

val robj_tops: RolesTypes.stage -> RolesTypes.robjs -> RolesTypes.oobjs * RolesTypes.oobjs 

val robj_split:
  RolesTypes.stage -> RolesTypes.robjs ->
  RolesTypes.robjs * RolesTypes.oobjs * RolesTypes.nobjs

val new_status: RolesTypes.status

val string_of_pointer: RolesTypes.pointer -> string

val pointer_of_string: string -> RolesTypes.pointer

val string_of_error: RolesTypes.error -> string
