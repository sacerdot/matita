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

val objs: NUri.UriSet.t ref

val srcs: NUri.UriSet.t ref

val exclude: NCic.generated list ref

val net: int ref

val no_devel: bool ref

val no_init: bool ref

val clear: unit -> unit
