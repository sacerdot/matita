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

module X = Ground

type item = Free  of string  (* free text *)
          | Text  of string  (* quoted text *)
          | Macro of string  (* macro *)
          | Group of text    (* group *)
          | Note  of string  (* comment *)
         
and text = item list         (* structured text *)

let file_ext = ".tex"

let group s = Group s

let arg s = Group [Text s]

let free s = Group [Free s]

let mk_segs us =
   L.rev_map arg ("" :: (L.rev us))

let mk_rev_args riss is =
   X.rev_map_append group ([] :: riss) is

let rev_mk_args iss is =
   free "" :: X.rev_map_append group iss is
