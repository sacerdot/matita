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

type item = Free  of string  (* free text *)
          | Macro of string  (* macro *)
          | Group of text    (* group *)
         
and text = item list         (* structured text *)

let file_ext = ".tex"

let empty = [Free ""]

let newline = [Free "%\n"]

let arg s = Group [Free s]

let mk_rev_args riss =
   L.rev_map (fun t -> Group t) (empty :: riss)
 
