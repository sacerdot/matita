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

module C = NCic

module X = Ground
module G = Options
module K = Kernel

type term = Meta
          | Sort of C.sort
          | GRef of string * string
          | LRef of int
          | Appl of term list
          | Prod of string * term * term
          | Abst of string * term * term
          | Abbr of string * term * term * term
          | Case of term * term * term * term list
          | Sigs of string list * term list * term list

(* internal functions *******************************************************)

let get_sigs s =
   let rec aux = function
      | []              -> G.nan, G.nan
      | (n, i, j) :: tl -> 
         if n = s then i, j else aux tl
   in
   aux !G.sigs_gref

let rec get_names ss j t =
   if j <= 0 then ss else match t with
      | Abst (s, _, t) -> get_names (s :: ss) (pred j) t
      | _              -> assert false  

let rec trim_absts j t =
   if j <= 0 then t else match t with
      | Abst (_, _, t) -> trim_absts (pred j) t
      | _              -> assert false  

let proc_appl ts = match ts with
   | GRef (s, _) :: vs ->
      let i, j = get_sigs s in
      if L.length vs <> i + j || i = 0 || j = 0 then Appl ts else
      let types, preds = X.split_at j vs in
      let names = get_names [] j (L.hd preds) in
      let preds = L.rev_map (trim_absts j) preds in
      Sigs (names, types, preds)
   | ts                -> Appl ts

let rec proc_term = function
   | C.Meta _
   | C.Implicit _          -> Meta
   | C.Sort s              -> Sort s
   | C.Const c             ->
      let s, name = K.resolve_reference c in
      GRef (s, name)
   | C.Rel m               -> LRef m
   | C.Appl ts             -> proc_appl (proc_terms ts)
   | C.Prod (s, w, t)      -> Prod (s, proc_term w, proc_term t)
   | C.Lambda (s, w, t)    -> Abst (s, proc_term w, proc_term t)
   | C.LetIn (s, w, v, t)  -> Abbr (s, proc_term w, proc_term v, proc_term t)
   | C.Match (c, u, v, ts) -> Case (proc_term (C.Const c), proc_term u, proc_term v, proc_terms ts)

and proc_terms ts =
   L.rev (L.rev_map proc_term ts)

(* interface functions ******************************************************)

let process = proc_term
