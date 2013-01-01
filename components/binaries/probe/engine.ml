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

module U = NUri

let out_uris uris =
   let map uri = P.printf "%s\n" (U.string_of_uri uri) in
   L.iter map uris

let out_int i = P.printf "%u\n" i

let out_length l = out_int (L.length l)
