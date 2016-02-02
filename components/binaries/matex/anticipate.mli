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

val typeof: NCic.context -> NCic.term -> NCic.term

val not_prop1: NCic.context -> NCic.term -> bool

val not_prop2: NCic.context -> NCic.term -> bool

val process_top_term: string -> NCic.term -> NCic.term

val process_obj: NCic.obj_kind -> NCic.obj_kind
