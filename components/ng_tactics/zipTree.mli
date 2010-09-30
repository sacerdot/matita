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

(* $Id: nCic.ml 9058 2008-10-13 17:42:30Z tassi $ *)

type ('s,'g) tree = Node of 's * ('g * ('s,'g) tree) list | Nil 
type ('a,'s,'g) position

val start : ('s,'g) tree -> ('a,'s,'g) position

val up    : ('a,'s,'g) position -> ('b,'s,'g) position option
val down  : ('a,'s,'g) position -> ('b,'s,'g) position option
val downr : ('a,'s,'g) position -> ('b,'s,'g) position option
val left  : ('a,'s,'g) position -> ('b,'s,'g) position option
val right : ('a,'s,'g) position -> ('b,'s,'g) position option

val is_top :  ('a,'s,'g) position -> bool

val root: ('a,'s,'g) position -> ('s,'g) tree

val get: ('a,'s,'g) position -> 's * 'g
val set: 's -> 'g -> ('a,'s,'g) position -> ('a,'s,'g) position

val inject: ('s,'g) tree -> ('a,'s,'g) position -> ('a,'s,'g) position
val eject: ('a,'s,'g) position -> ('s,'g) tree

val dump: ('g -> string) -> ('s -> string -> Format.formatter -> unit) -> 
            ('a,'s,'g) position -> Format.formatter -> unit


