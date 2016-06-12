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

exception Error of string

val error: string -> 'a

val log: string -> unit

val id: 'a -> 'a

val id2: 'a -> 'b -> 'a * 'b

val segments_of_string: string list -> int -> string -> string list

val rev_map_concat: ('a -> string) -> string -> string -> 'a list -> string

val fold_string: ('a -> char -> 'a) -> 'a -> string -> 'a

val rev_neg_filter : ('a -> bool) -> 'a list -> 'a list -> 'a list

val foldi_left: (int -> 'a -> 'b -> 'a) -> int -> 'a -> 'b list -> 'a 

val rev_mapi: (int -> 'b -> 'a) -> int -> 'b list -> 'a list

val rev_map_append: ('a -> 'b) -> 'a list -> 'b list -> 'b list
