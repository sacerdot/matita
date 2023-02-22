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

let default_base_url = "http://helm.cs.unibo.it/lambdadelta/"

let default_cwd = Filename.dirname Sys.argv.(0)

let default_debug_lexer = false

let base_url = ref default_base_url

let cwd = ref default_cwd

let debug_lexer = ref default_debug_lexer

let clear () =
  base_url := default_base_url;
  cwd := default_cwd;
  debug_lexer := default_debug_lexer
