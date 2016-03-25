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

type def_xflavour = [ NCic.def_flavour
                    | `Inductive
                    ]

val add_xflavour: int -> def_xflavour -> unit 

val iter_xflavours: (int -> unit) -> unit

val objs: NUri.UriSet.t ref

val srcs: NUri.UriSet.t ref

val remove: string list ref

val exclude: NCic.source list ref

val net: int ref

val chars: int ref

val debug_lexer: bool ref

val no_devel: bool ref

val no_init: bool ref

val clear: unit -> unit
