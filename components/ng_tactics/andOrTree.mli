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

type andT
type orT

type ('s,'g) tree = ([ `And of 's | `Or ], 'g) ZipTree.tree
type ('a,'s,'g) position = ('a,[ `And of 's | `Or ], 'g) ZipTree.position

type ('s,'g) subtreeA = 
  Solution of 's | Todo of (andT,'s,'g) position

type ('s,'g) subtreeO = 
  Unexplored | Alternatives of (orT,'s,'g) position

(* fails if Nil *)
val start : ('s,'g) tree -> (andT,'s,'g) position

val upA    : (andT,'s,'g) position -> (orT,'s,'g) position option
val upO    : (orT,'s,'g) position -> (andT,'s,'g) position 
val downA : (andT,'s,'g) position -> ('s,'g) subtreeO
val downO  : (orT,'s,'g) position -> ('s,'g) subtreeA
val downOr : (orT,'s,'g) position -> ('s,'g) subtreeA

val left  : ('a,'s,'g) position -> ('a,'s,'g) position option
val right : ('a,'s,'g) position -> ('a,'s,'g) position option

val is_top : (orT,'s,'g) position -> bool
val is_nil : (andT,'s,'g) position -> bool
val is_solved_leaf : (orT,'s,'g) position -> bool

val get_leaf_solution : (orT,'s,'g) position -> 's

val root: ('a,'s,'g) position -> ('s,'g) tree

val getA: (andT,'s,'g) position -> 's * 'g
val getO: (orT,'s,'g) position -> 'g
val setA: 's -> 'g -> (andT,'s,'g) position -> (andT,'s,'g) position
val setO: 'g -> (orT,'s,'g) position -> (orT,'s,'g) position

val inject: ('s,'g) tree -> ('a,'s,'g) position -> ('a,'s,'g) position
val eject: ('a,'s,'g) position -> ('s,'g) tree

val dump: ('g -> string) -> 
            ('a,'s,'g) position -> Format.formatter -> unit


