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

module C = NCic
module T = NCicTypeChecker

module X = Ground
module G = Options
module K = Kernel

(* internal functions *******************************************************)

let fresh = ref 0

let malformed s =
   X.error ("anticipate: malformed term: " ^ s)

let ok s =
   X.log ("anticipate: ok " ^ s)

let anticipate c v =
   incr fresh;
   let w = K.typeof c v in
   P.sprintf "%s%u" !G.proc_id !fresh, w, v, C.Rel K.fst_var

let initial = None, []

let proc_arg c i (d, rtts) t = match d with
   | Some _ -> d, (t :: rtts)
   | None   ->
      if K.is_atomic t || K.not_prop2 c t then d, (t :: rtts) else
      let s, w, v, tt = anticipate c t in
      Some (i, s, w, v), (tt :: rtts)

let lift_arg ri i tts t =
   if ri = i then t :: tts
   else K.lift K.fst_var 1 t :: tts

let rec proc_term c t = match t with
   | C.Appl []
   | C.Meta _
   | C.Implicit _             -> malformed "2"
   | C.Sort _
   | C.Rel _
   | C.Const _
   | C.Prod _                 -> [], t
   | C.Lambda (s, w, t)       -> 
      let tt = shift_term (K.add_dec s w c) t in
      [], K.lambda s w tt
   | C.LetIn (s, w, v, t)     ->
      if K.not_prop1 c w then
         let dt, tt = proc_term (K.add_def s w v c) t in
         dt @ K.add_def s w v [], tt
      else
         let dv, vv = proc_term c v in
         let l = L.length dv in
         let c = dv @ c in
         let w = K.lift K.fst_var l w in
         let t = K.lift K.snd_var l t in
         let dt, tt = proc_term (K.add_def s w vv c) t in
         dt @ (K.add_def s w vv dv), tt
   | C.Appl [t]               -> proc_term c t
   | C.Appl (C.Appl ts :: vs) -> proc_term c (K.appl (ts @ vs))
   | C.Appl ts                -> proc_appl c t ts
   | C.Match (w, u, v, ts)    -> proc_case c t w u v ts

and proc_appl c t ts = match X.foldi_left (proc_arg c) 1 initial ts with
   | None             , _    -> [], t
   | Some (i, s, w, v), rtts ->
      let ri = L.length rtts - i in
      let tts = X.foldi_left (lift_arg ri) 0 [] rtts in
      proc_term c (K.letin s w v (K.appl tts))

and proc_case c t w u v ts = match X.foldi_left (proc_arg c) 1 initial ts with
   | None               , _    -> 
      if K.is_atomic v || K.not_prop1 c (C.Const w) then [], t else
      let s, w0, v0, vv = anticipate c v in
      let u = K.lift K.fst_var 1 u in
      let ts = K.lifts K.fst_var 1 ts in
      proc_term c (K.letin s w0 v0 (K.case w u vv ts))
   | Some (i, s, w0, v0), rtts ->
      let ri = L.length rtts - i in
      let u = K.lift K.fst_var 1 u in
      let v = K.lift K.fst_var 1 v in
      let tts = X.foldi_left (lift_arg ri) 0 [] rtts in
      proc_term c (K.letin s w0 v0 (K.case w u v tts))

and shift_term c t =
   let d, tt = proc_term c t in
   K.shift tt d

let shift_named_term s c t =
try
   fresh := 0;
   let tt = shift_term c t in
   if !G.check then begin
      let _ = K.typeof c tt in
      ok s
   end;
   tt
with
   | T.TypeCheckerFailure s
   | T.AssertFailure s           -> malformed (Lazy.force s)

let proc_fun c =
   let r, s, i, u, t = c in
   if K.not_prop1 [] u then c else
   r, s, i, u, shift_named_term s [] t

let proc_obj obj = match obj with
   | C.Inductive _
   | C.Constant (_, _, None, _, _)   -> obj
   | C.Constant (r, s, Some t, u, a) ->
      if K.not_prop1 [] u then obj else 
      let tt = shift_named_term s [] t in
      C.Constant (r, s, Some tt, u, a)
   | C.Fixpoint (b, cs, a)           ->
      C.Fixpoint (b, L.map proc_fun cs, a)

(* interface functions ******************************************************)

let process_top_term s t = shift_named_term s [] t

let process_obj obj = proc_obj obj
