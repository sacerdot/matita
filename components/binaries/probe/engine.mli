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

val out_int: int -> unit

val out_length: NUri.UriSet.t -> unit

val out_uris: NUri.UriSet.t -> unit

val is_registry: string -> bool

val get_uri: string -> string * string

val unsupported: string -> 'a

val missing: string -> 'a
