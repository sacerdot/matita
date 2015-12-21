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
module S = String

module T = TeX

(* internal functions *******************************************************)

let special = "_"

let quote c =
   if S.contains special c then '.' else c

let rec out_item och = function
   | T.Free s  -> P.fprintf och "%s" (S.map quote s)
   | T.Macro s -> P.fprintf och "\\%s" s
   | T.Group t -> P.fprintf och "%%\n{%a}" out_text t

(* interface functions ******************************************************)

and out_text och t = 
   L.iter (out_item och) t
