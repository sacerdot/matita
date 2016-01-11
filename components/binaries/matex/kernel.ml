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
module F = Filename
module P = Printf
module S = String

module U = NUri
module C = NCic
module B = NCicSubstitution
module D = NCicReduction
module K = NCicTypeChecker
module H = HLog
module A = NCicLibrary
module E = NCicEnvironment
module R = NReference

module X = Ground
module G = Options

(* internal functions *******************************************************)

let trusted _ = true

let no_log _ _ = ()

let mk_type_universe i =
   [`Type, U.uri_of_string (P.sprintf "cic:/matita/pts/Type%s.univ" i)]

(* interface functions ******************************************************)

let init () =
   A.init (); 
   K.set_trust trusted;
   H.set_log_callback no_log;
   let u0 = mk_type_universe "0" in
   let u1 = mk_type_universe "1" in
   E.add_lt_constraint u0 u1

let fst_var = 1

let snd_var = 2

let lambda s w t = C.Lambda (s, w, t)

let letin s w v t = C.LetIn (s, w, v, t)

let case w u v ts = C.Match (w, u, v, ts)

let add_dec s w c = (s, C.Decl w) :: c

let add_def s w v c = (s, C.Def (v, w)) :: c

let rec shift t = function
   | []                     -> t
   | (s, C.Decl w) :: c     -> shift (lambda s w t) c
   | (s, C.Def (v, w)) :: c -> shift (letin s w v t) c

let rec is_atomic = function
   | C.Appl [t]   -> is_atomic t
   | C.Appl []
   | C.Meta _
   | C.Implicit _ 
   | C.Sort _
   | C.Rel _
   | C.Const _    -> true
   | C.Appl _
   | C.Prod _
   | C.Lambda _ 
   | C.LetIn _
   | C.Match _    -> false

let resolve_lref c i = fst (L.nth c (i - fst_var))

let lift d e t =
   B.lift G.status ~from:d e t

let lifts d e ts =
    L.rev_map (lift d e) (L.rev ts)

let whd c t =
   D.whd G.status ~delta:max_int ~subst:[] c t

let typeof c t =
   K.typeof G.status [] [] c t

let segments_of_uri u =
   let s = U.string_of_uri u in
   let s = F.chop_extension s in
   let l = S.length s in
   let i = S.index s ':' in
   let s = S.sub s (i+2) (l-i-2) in
   X.segments_of_string [] (l-i-2) s

let name_of_reference ss = function
   | C.Constant (_, name, _, _, _), R.Decl      ->
      ss, name
   | C.Constant (_, name, _, _, _), R.Def _     ->
      ss, name
   | C.Inductive (_, _, us, _), R.Ind (_, i, _) -> 
      let _, name, _, _ = L.nth us i in
      (name :: ss), name
   | C.Inductive (_, _, us, _), R.Con (i, j, _) ->
      let _, _, _, ts = L.nth us i in
      let _, name, _ = L.nth ts (pred j) in
      (name :: ss), name
   | C.Fixpoint (_, ts, _)    , R.Fix (i, _, _) ->
      let _, name, _, _, _ = L.nth ts i in
      (name :: ss), name
   | C.Fixpoint (_, ts, _)    , R.CoFix i       ->
      let _, name, _, _, _ = L.nth ts i in
      (name :: ss), name
   | _                                          ->
      failwith "name_of_reference"
