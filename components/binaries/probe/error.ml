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

module L = List
module P = Printf

exception Error of string

let error s =
  raise (Error s)

let unsupported protocol =
  error (P.sprintf "unsupported protocol: %s" protocol)

let missing path =
  error (P.sprintf "missing path: %s" path)

let unrooted path roots =
  error (P.sprintf "missing root: %s (found roots: %u)" path (L.length roots))

let malformed () =
  error "malformed term"
