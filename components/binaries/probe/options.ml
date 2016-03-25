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

module A = Array
module P = Printf

module C = NCic
module R  = Helm_registry
module US = NUri.UriSet

type def_xflavour = [ C.def_flavour
                    | `Inductive
                    ]

let default_objs = US.empty

let default_srcs = US.empty

let default_remove = []

let default_exclude = []

let default_net = 0

let default_chars = 0

let default_debug_lexer = false

let default_no_devel = true

let default_no_init = true

let xflavours = 8

let slot = A.make xflavours 0

let objs = ref default_objs

let srcs = ref default_srcs

let remove = ref default_remove

let exclude = ref default_exclude

let net = ref default_net

let chars = ref default_chars

let debug_lexer = ref default_debug_lexer

let no_devel = ref default_no_devel

let no_init = ref default_no_init

let index_of_xflavour = function 
   | `Inductive  -> 0
   | `Axiom      -> 1 
   | `Definition -> 2
   | `Fact       -> 3
   | `Lemma      -> 4
   | `Theorem    -> 5
   | `Corollary  -> 6
   | `Example    -> 7

let add_xflavour n xf =
   let i = index_of_xflavour xf in
   slot.(i) <- slot.(i) + n

let clear_slot i _ = slot.(i) <- 0

let iter_xflavours map = A.iteri (fun _ -> map) slot

let clear () =
   R.clear (); A.iteri clear_slot slot;
   objs := default_objs; srcs := default_srcs; remove := default_remove;
   exclude := default_exclude; net := default_net;
   chars := default_chars; debug_lexer := default_debug_lexer;
   no_devel := default_no_devel; no_init := default_no_init
