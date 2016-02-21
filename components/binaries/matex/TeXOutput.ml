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

module X = Ground
module T = TeX

(* internal functions *******************************************************)

let special = "\\{}$&#^_~%" (* LaTeX reserves these characters *)

let special = [
   '_', "\\_";
]

let quote s c = try s ^ L.assoc c special with
   | Not_found -> s ^ S.make 1 c 

let rec out_item och = function
   | T.Free s  -> P.fprintf och "%s" s
   | T.Text s  -> P.fprintf och "%s" (X.fold_string quote "" s)
   | T.Macro s -> P.fprintf och "\\%s%%\n" s
   | T.Group t -> P.fprintf och "{%a}%%\n" out_text t
   | T.Note s  -> P.fprintf och "%% %s\n" s

(* interface functions ******************************************************)

and out_text och t = 
   L.iter (out_item och) t
