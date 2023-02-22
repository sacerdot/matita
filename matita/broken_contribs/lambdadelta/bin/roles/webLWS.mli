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

type request = (string * string) list * string

val open_out: string -> int -> unit

val close_out: unit -> unit

val loop_in: ('a -> 'a) -> (string -> string -> 'a -> 'a) -> ('a -> 'a) -> 'a -> 'a

val string_of_request: string -> request -> string

val control_input: string -> unit

val open_out_html: string -> string -> string -> string -> string -> string -> unit

val close_out_html: unit -> unit
