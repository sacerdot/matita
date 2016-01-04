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

module F = Filename
module L = List
module S = String

module U = NUri
module R = NReference
module C = NCic
module P = NCicPp
module E = NCicEnvironment

module G = Options
module T = TeX
module O = TeXOutput

let status = new P.status

(* internal functions *******************************************************)

let rec segments_of_string ss l s =
   match try Some (S.index s '/') with Not_found -> None with
      | None   -> s :: ss
      | Some i -> segments_of_string (S.sub s 0 i :: ss) (l-i-1) (S.sub s (i+1) (l-i-1))

let segments_of_uri u =
   let s = U.string_of_uri u in
   let s = F.chop_extension s in
   let l = S.length s in
   let i = S.index s ':' in
   let s = S.sub s (i+2) (l-i-2) in
   segments_of_string [] (l-i-2) s

let rec mk_string sep r = function
   | []      -> r 
   | s :: ss -> mk_string sep (s ^ sep ^ r) ss 

let alpha c s = s

let malformed s =
   failwith ("MaTeX: malformed term: " ^ s)

let not_supported () =
   failwith "MaTeX: object not supported"

let proc_sort = function
   | C.Prop             -> [T.Macro "Prop"]
   | C.Type [`Type, u]  -> [T.Macro "Type"; T.arg (U.string_of_uri u)]
   | C.Type [`CProp, u] -> [T.Macro "Crop"; T.arg (U.string_of_uri u)]
   | C.Type _           -> malformed "1"

let proc_gref ss = function
   | C.Constant _             , R.Decl          ->
      T.Macro "GRef" :: T.mk_segs ("type" :: ss)
   | C.Constant _             , R.Def _         ->
      T.Macro "GRef" :: T.mk_segs ("body" :: ss)
   | C.Inductive (_, _, us, _), R.Ind (_, i, _) -> 
      let _, name, _, _ = L.nth us i in
      T.Macro "IRef" :: T.mk_segs (name :: ss)
   | C.Inductive (_, _, us, _), R.Con (i, j, _) ->
      let _, _, _, ts = L.nth us i in
      let _, name, _ = L.nth ts (pred j) in
      T.Macro "IRef" :: T.mk_segs (name :: ss)
   | C.Fixpoint (_, ts, _)    , R.Fix (i, _, _) ->
      let _, name, _, _, _ = L.nth ts i in
      T.Macro "IRef" :: T.mk_segs (name :: ss)
   | C.Fixpoint (_, ts, _)    , R.CoFix i       ->
      let _, name, _, _, _ = L.nth ts i in
      T.Macro "IRef" :: T.mk_segs (name :: ss)
   | _                                          ->
      malformed "2"

let rec proc_term c = function
   | C.Appl []
   | C.Meta _
   | C.Implicit _          -> malformed "3" 
   | C.Rel m               ->
      let name = L.nth c (m-1) in
      [T.Macro "LRef"; T.arg name]
   | C.Appl ts             ->
      let riss = L.rev_map (proc_term c) ts in
      T.Macro "Appl" :: T.mk_rev_args riss
  | C.Prod (s, w, t)       ->
      let s = alpha c s in
      let is_w = proc_term c w in
      let is_t = proc_term (s::c) t in
      T.Macro "Prod" :: T.arg s :: T.Group is_w :: is_t
  | C.Lambda (s, w, t)     -> 
      let s = alpha c s in
      let is_w = proc_term c w in
      let is_t = proc_term (s::c) t in
      T.Macro "Abst" :: T.arg s :: T.Group is_w :: is_t
  | C.LetIn (s, w, v, t)   -> 
      let s = alpha c s in
      let is_w = proc_term c w in
      let is_v = proc_term c v in
      let is_t = proc_term (s::c) t in
      T.Macro "Abbr" :: T.arg s :: T.Group is_w :: T.Group is_v :: is_t
  | C.Sort s               ->
      proc_sort s
  | C.Const (R.Ref (u, r)) ->
      let ss = segments_of_uri u in
      let _, _, _, _, obj = E.get_checked_obj status u in  
      proc_gref ss (obj, r)
  | C.Match (w, u, v, ts)  ->
      let is_w = proc_term c (C.Const w) in
      let is_u = proc_term c u in
      let is_v = proc_term c v in
      let riss = L.rev_map (proc_term c) ts in
      T.Macro "Case" :: T.Group is_w :: T.Group is_u :: T.Group is_v :: T.mk_rev_args riss

let proc_term c t = try proc_term c t with
   | E.ObjectNotFound _ 
   | Failure "nth" 
   | Invalid_argument "List.nth" -> malformed "4"

let open_out_tex s =
   open_out (F.concat !G.out_dir (s ^ T.file_ext))

let proc_obj u =
   let ss = segments_of_uri u in
   let _, _, _, _, obj = E.get_checked_obj status u in 
   match obj with
      | C.Constant (_, _, None, u, _)   -> not_supported ()
      | C.Constant (_, _, Some t, u, _) ->
         let name = mk_string "." "body" ss in
         let och = open_out_tex name in
         O.out_text och (proc_term [] t);
         O.out_text och T.newline;
         close_out och;
         let name = mk_string "." "type" ss in
         let och = open_out_tex name in
         O.out_text och (proc_term [] u);
         O.out_text och T.newline;
         close_out och
      | C.Fixpoint (_, _, _)            -> not_supported ()
      | C.Inductive (_, _, _, _)        -> not_supported ()

(* interface functions ******************************************************)

let process = proc_obj
