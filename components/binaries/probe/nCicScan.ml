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

module L  = List

module U  = NUri
module US = U.UriSet
module R  = NReference
module C  = NCic
module P  = NCicPp
module E  = NCicEnvironment

module O  = Options

let status = new P.status

let malformed () =
   failwith "probe: malformed term"

let rec set_list c ts cts =
   let map cts t = (c, t) :: cts in
   L.fold_left map cts ts

let set_funs c rfs cts =
   let map cts (_, _, _, t0, t1) = set_list c [t0; t1] cts in
   L.fold_left map cts rfs

let set_type c cts (_, _, t, css) =
   let map cts (_, _, t) = (c, t) :: cts in 
   (c, t) :: L.fold_left map cts css 

let scan_lref a c i = 
   try match List.nth c (pred i) with
      | _, C.Decl _ -> succ a
      | _, C.Def  _ -> a
   with 
      | Failure _ -> succ a 

let scan_gref a = function
   | R.Ref (_, R.Decl) 
   | R.Ref (_, R.Ind _)
   | R.Ref (_, R.Con _)   -> succ a
   | R.Ref (u, R.Def _)
   | R.Ref (u, R.Fix _)
   | R.Ref (u, R.CoFix _) ->
      if US.mem u !O.objs then a else succ a

let rec scan_term a = function
   | []                                 -> a
   | (_, C.Meta _)                :: tl
   | (_, C.Implicit _)            :: tl -> scan_term a tl
   | (_, C.Sort _)                :: tl -> scan_term (succ a) tl
   | (c, C.Rel i)                 :: tl -> scan_term (scan_lref a c i) tl
   | (_, C.Const p)               :: tl -> scan_term (scan_gref a p) tl
   | (_, C.Appl [])               :: tl -> malformed ()
   | (c, C.Appl ts)               :: tl ->
      scan_term (L.length ts + pred a) (set_list c ts tl)
   | (c, C.Match (_, t0, t1, ts)) :: tl ->
      scan_term a (set_list c (t0::t1::ts) tl)   
   | (c, C.Prod (s, t0, t1))      :: tl
   | (c, C.Lambda (s, t0, t1))    :: tl ->
      scan_term (succ a) ((c, t0) :: ((s, C.Decl t0) :: c, t1) :: tl)
   | (c, C.LetIn (s, t0, t1, t2)) :: tl ->
      scan_term a ((c, t0) :: (c, t1) :: ((s, C.Def (t1, t0)) :: c, t2) :: tl)

let scan_obj u a = 
   let _, _, _, _, obj = E.get_checked_obj status u in 
   match obj with
      | C.Constant (_, _, None, t, _)     ->
         scan_term (succ a) [[], t]
      | C.Constant (_, _, Some t0, t1, _) ->
         scan_term (succ a) (set_list [] [t0; t1] [])
      | C.Fixpoint (_, rfs, _)            ->
         scan_term (a + L.length rfs) (set_funs [] rfs [])
      | C.Inductive (_, _, its, _)        ->
	 let cts = L.fold_left (set_type []) [] its in
         scan_term (a + L.length cts) cts

let accept_obj u = 
   let _, _, _, _, obj = E.get_checked_obj status u in 
   let g = match obj with
      | C.Constant (_, _, _, _, (g, _, _))
      | C.Fixpoint (_, _, (g, _, _))
      | C.Inductive (_, _, _, (g, _))    -> g
   in
   if L.mem g !O.exclude then false else true

let scan () = 
   if !O.exclude <> [] then 
      O.objs := US.filter accept_obj !O.objs;
   O.net := US.fold scan_obj !O.objs !O.net
