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

let debug_lexer_default = false

let count_default = 0

let page_default = 5120

let debug_lexer = ref debug_lexer_default

let count = ref count_default

let page = ref page_default

let clear () =
   debug_lexer := debug_lexer_default;
   count := count_default;
   page := page_default
