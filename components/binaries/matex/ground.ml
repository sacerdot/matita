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
module P = Printf
module S = String

exception Error of string

(* interface functions ******************************************************)

let id x = x

let id2 x y = x, y 

let rec segments_of_string ss l s =
   match try Some (S.index s '/') with Not_found -> None with
      | None   -> s :: ss
      | Some i -> segments_of_string (S.sub s 0 i :: ss) (l-i-1) (S.sub s (i+1) (l-i-1))

let rec rev_map_concat map sep r = function
   | []                  -> r 
   | s :: ss             ->
      if r = "" then rev_map_concat map sep (map s) ss else
      rev_map_concat map sep (map s ^ sep ^ r) ss 

let fold_string map a s =
   let l = S.length s in
   let rec aux i a =
      if i >= l then a else aux (succ i) (map a s.[i])
   in
   aux 0 a

let rec rev_neg_filter filter r = function
   | []       -> r
   | hd :: tl ->
      if filter hd then rev_neg_filter filter r tl else rev_neg_filter filter (hd :: r) tl

let rec foldi_left mapi i a = function
   | []       -> a
   | hd :: tl -> foldi_left mapi (succ i) (mapi i a hd) tl

let rec rev_map_append map l r = match l with
   | []       -> r
   | hd :: tl -> rev_map_append map tl (map hd :: r)

let error s = raise (Error s)

let log s = P.eprintf "MaTeX: %s\n%!" s
