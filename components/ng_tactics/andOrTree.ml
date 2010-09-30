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

open ZipTree

(* fails if Nil *)

let start t = 
  match down (start t) with
  | None -> assert false
  | Some pos -> pos

let setO x = set `Or x
let setA x y = set (`And x) y

let getO x = match get x with `And _,_ -> assert false | `Or, x -> x
let getA x = match get x with `And x,y -> x,y | `Or, _ -> assert false

let root = root

let upA p =
  match up p with
  | None -> None
  | Some p -> if is_top p then None else Some p

let upO p = match up p with None -> assert false | Some x -> x

let downA p = 
 match down p with
 | Some x -> Alternatives x
 | None -> assert(eject p = Nil); Unexplored 

let downO p = 
 match down p with
 | Some x -> Todo x
 | None -> 
    match eject p with
    | Node(`And s,[]) -> Solution s
    | _ -> assert false

let downOr p = 
 match downr p with
 | Some x -> Todo x
 | None -> 
    match eject p with
    | Node(`And s,[]) -> Solution s
    | _ -> assert false

let left = left
let right = right

let is_top = is_top
let is_nil p = 
  match eject p with
  | Nil -> true
  | _ -> false
let is_solved_leaf p = 
  match eject p with
  | Node(`And _,[]) -> true
  | _ -> false
let get_leaf_solution p =
  match eject p with
  | Node(`And x,[]) -> x
  | _ -> assert false


let inject = inject
let eject = eject

let dump f = 
  dump f (function 
          | `And _ -> fun _ _ -> ()
          | `Or -> fun node fmt -> 
                          GraphvizPp.Dot.node node ~attrs:["style","rounded"]
                          fmt)
