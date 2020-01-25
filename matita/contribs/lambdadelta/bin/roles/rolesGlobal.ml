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

let default_wd = ""

let default_debug_lexer = false

let wd = ref default_wd

let debug_lexer = ref default_debug_lexer

let clear () =
  wd := default_wd;
  debug_lexer := default_debug_lexer
