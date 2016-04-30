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
module S = Scanf
module N = String

module U = NUri
module C = NCic
module R = NReference
module E = NCicEnvironment
module T = NCicTypeChecker

module X = Ground
module G = Options
module K = Kernel

let dno = "_" (* does not occur *)

let nan = -1  (* not a number *)

(* internal functions *******************************************************)

let malformed s =
   X.error ("alpha: malformed term: " ^ s)

let ok s =
   X.log ("alpha: ok " ^ s)

let rec trim r =
   let r1, r2 = S.sscanf r "%s@_%s" X.id2 in
   if r2 = "" then r1 else trim r1

let split s = 
   let rec aux i l =
      let j = pred i in
      if j >=0 && s.[j] >= '0' && s.[j] <= '9' then aux j (succ l) else i, l
   in 
   let i, l = aux (N.length s) 0 in
   let s1, s2 = N.sub s 0 i, N.sub s i l in
   let s1 = if s1 = "" then "_" else s1 in 
   s1, if l = 0 then nan else int_of_string s2

let rec strip = function
   | C.Appl (t :: _) 
   | C.Prod (_, _, t) -> strip t
   | t                -> t

let get_constant c t = match strip (K.whd c t) with
   | C.Sort (C.Prop)             ->
      P.sprintf "Prop"
   | C.Sort (C.Type [`Type, u])  ->
      P.sprintf "Type[%s]" (U.string_of_uri u)
   | C.Sort (C.Type [`CProp, u]) ->
      P.sprintf "CProp[%s]" (U.string_of_uri u)
   | C.Const (R.Ref (u, r))      ->
      let ss = K.segments_of_uri u in
      let _, _, _, _, obj = E.get_checked_obj G.status u in  
      let ss, _ = K.name_of_reference ss (obj, r) in
      X.rev_map_concat X.id "." "type" ss
   | _                           -> ""

let read l s r =
   let rec aux = function
      | []              -> ""
      | (a, b, c) :: tl ->
         if s = a && (r = b || r = c) then c else aux tl
   in
   aux l 

let type_check r c w =
   let s0 = get_constant c w in
   let r0 = read !G.alpha_type s0 r in
   if r0 <> "" then r0 else
   let s1 = get_constant c (K.typeof c w) in
   let r0 = read !G.alpha_sort s1 r in
   if r0 <> "" then r0 else begin
      if !G.log_alpha then
         X.log (P.sprintf "alpha: not found %s: type \"%s\" sort \"%s\"" r s0 s1);
      r
   end

let rec get r = function
   | []           -> r
   | (h, d) :: tl ->
      if fst r = h && snd r <= d then h, succ d else get r tl

let alpha d c s w t =
   if K.does_not_occur K.fst_var c t then dno, nan else
   let r, i = split (trim s) in
   get (type_check r c w, i) d

let mk_name (s, i) =
   if i < 0 then s else P.sprintf "%s%u" s i

let add_name r d = r :: d

let rec proc_term d c t = match t with
   | C.Meta _
   | C.Implicit _             
   | C.Sort _
   | C.Rel _
   | C.Const _             -> t
   | C.Appl ts             ->
      let tts = proc_terms d c ts in
      K.appl tts
   | C.Match (w, u, v, ts) ->
      let uu = proc_term d c u in
      let vv = proc_term d c v in
      let tts = proc_terms d c ts in
      K.case w uu vv tts
   | C.Prod (s, w, t)    -> 
      let rr = alpha d c s w t in
      let ss = mk_name rr in
      let ww = proc_term d c w in
      let tt = proc_term (add_name rr d) (K.add_dec ss w c) t in
      K.prod ss ww tt
   | C.Lambda (s, w, t)    -> 
      let rr = alpha d c s w t in
      let ss = mk_name rr in
      let ww = proc_term d c w in
      let tt = proc_term (add_name rr d) (K.add_dec ss w c) t in
      K.lambda ss ww tt
   | C.LetIn (s, w, v, t)  ->
      let rr = alpha d c s w t in
      let ss = mk_name rr in
      let ww = proc_term d c w in
      let vv = proc_term d c v in
      let tt = proc_term (add_name rr d) (K.add_def ss w v c) t in
      K.letin ss ww vv tt

and proc_terms d c ts =
   let rtts = L.rev_map (proc_term d c) ts in
   L.rev rtts

let proc_named_term s d c t =
try
   let tt = proc_term d c t in
   if !G.test then begin
      let _ = K.typeof c tt in
      ok s
   end;
   tt
with
   | T.TypeCheckerFailure s
   | T.AssertFailure s           -> malformed (Lazy.force s)

(* interface functions ******************************************************)

let process_top_term s t = proc_named_term s [] [] t
