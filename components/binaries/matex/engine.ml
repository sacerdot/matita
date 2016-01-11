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
module P = Printf
module S = String

module U = NUri
module R = NReference
module C = NCic
module E = NCicEnvironment
module V = NCicTypeChecker

module X = Ground
module G = Options
module K = Kernel
module T = TeX
module O = TeXOutput
module A = Anticipate

type status = {
   n: string;   (* object name *)
   s: int list; (* scope *)
} 

(* internal functions *******************************************************)

let alpha c s = s

let malformed s =
   X.error ("engine: malformed term: " ^ s)

let not_supported () =
   X.error "engine: object not supported"

(* generic term processing *)

let proc_sort = function
   | C.Prop             -> [T.Macro "PROP"]
   | C.Type [`Type, u]  -> [T.Macro "TYPE"; T.arg (U.string_of_uri u)]
   | C.Type [`CProp, u] -> [T.Macro "CROP"; T.arg (U.string_of_uri u)]
   | C.Type _           -> malformed "T1"

let rec proc_term c = function
   | C.Appl []
   | C.Meta _
   | C.Implicit _           -> malformed "T2" 
   | C.Rel m                ->
      let name = K.resolve_lref c m in
      [T.Macro "LREF"; T.arg name; T.free name]
   | C.Appl ts              ->
      let riss = L.rev_map (proc_term c) ts in
      T.Macro "APPL" :: T.mk_rev_args riss
   | C.Prod (s, w, t)       ->
      let s = alpha c s in
      let is_w = proc_term c w in
      let is_t = proc_term (K.add_dec s w c) t in
      T.Macro "PROD" :: T.arg s :: T.Group is_w :: is_t
   | C.Lambda (s, w, t)     -> 
      let s = alpha c s in
      let is_w = proc_term c w in
      let is_t = proc_term (K.add_dec s w c) t in
      T.Macro "ABST" :: T.arg s :: T.Group is_w :: is_t
   | C.LetIn (s, w, v, t)   -> 
      let s = alpha c s in
      let is_w = proc_term c w in
      let is_v = proc_term c v in
      let is_t = proc_term (K.add_def s w v c) t in
      T.Macro "ABBR" :: T.arg s :: T.Group is_w :: T.Group is_v :: is_t
   | C.Sort s               ->
      proc_sort s
   | C.Const (R.Ref (u, r)) ->
      let ss = K.segments_of_uri u in
      let _, _, _, _, obj = E.get_checked_obj G.status u in  
      let ss, name = K.name_of_reference ss (obj, r) in
      [T.Macro "GREF"; T.arg name; T.free (X.rev_concat "." "type" ss)]
   | C.Match (w, u, v, ts)  ->
      let is_w = proc_term c (C.Const w) in
      let is_u = proc_term c u in
      let is_v = proc_term c v in
      let riss = L.rev_map (proc_term c) ts in
      T.Macro "CASE" :: T.Group is_w :: T.Group is_u :: T.Group is_v :: T.mk_rev_args riss

let proc_term c t = try proc_term c t with
   | E.ObjectNotFound _ 
   | Invalid_argument "List.nth"
   | Failure "nth" 
   | Failure "name_of_reference" -> malformed "T3"

(* proof processing *)

let init n = {
   n = n; s = [];
}

let mk_dec w s is =
   let w = if !G.no_types then [] else w in
   T.Group w :: T.free s :: T.arg s :: T.Macro "DECL" :: is

let rec proc_proof st ris c t = match t with
   | C.Appl []
   | C.Meta _
   | C.Implicit _  
   | C.Sort _
   | C.Prod _              -> malformed "P1"
   | C.Const _
   | C.Rel _               -> proc_proof st ris c (C.Appl [t])
   | C.Lambda (s, w, t)    -> 
      let s = alpha c s in
      let is_w = proc_term c w in
      proc_proof st (T.Macro "PRIM" :: mk_dec is_w s ris) (K.add_dec s w c) t
   | C.Appl ts              ->
      let rts = X.rev_neg_filter (A.not_prop2 c) [] ts in
      let ris = T.Macro "STEP" :: ris in
      let tts = L.rev_map (proc_term c) rts in
      T.rev_mk_args tts ris
   | C.Match (w, u, v, ts) ->
      let rts = X.rev_neg_filter (A.not_prop2 c) [v] ts in
      let ris = T.Macro "DEST" :: ris in
      let tts = L.rev_map (proc_term c) rts in
      T.rev_mk_args tts ris
   | C.LetIn (s, w, v, t)  -> 
      let s = alpha c s in
      let is_w = proc_term c w in
      if A.not_prop1 c w then
         let is_v = proc_term c v in
         proc_proof st (T.Group is_v :: T.Macro "BODY" :: mk_dec is_w s ris) (K.add_def s w v c) t
      else
         let ris_v = proc_proof st ris c v in
         proc_proof st (mk_dec is_w s ris_v) (K.add_def s w v c) t

let proc_proof c t = try proc_proof (init "") [] c t with 
   | E.ObjectNotFound _ 
   | Invalid_argument "List.nth"
   | Failure "nth" 
   | Failure "name_of_reference" -> malformed "P2"
   | V.TypeCheckerFailure s
   | V.AssertFailure s           -> malformed (Lazy.force s)

(* top level processing *)

let proc_top_type s t = 
   [T.Macro "Object"; T.arg s; T.free s; T.Group (proc_term [] t)]

let proc_top_body s t = proc_term [] t

let proc_top_proof s t =
   let tt = A.process_top_term s t in (* anticipation *)
   L.rev (proc_proof [] tt)

let open_out_tex s =
   open_out (F.concat !G.out_dir (s ^ T.file_ext))

let proc_pair s ss u xt =
   let name = X.rev_concat "." "type" ss in
   let och = open_out_tex name in
   O.out_text och (proc_top_type s u);
   close_out och;
   match xt with
      | None   -> ()
      | Some t ->
         let name = X.rev_concat "." "body" ss in
         let och = open_out_tex name in
         let text = if A.not_prop1 [] u then proc_top_body else proc_top_proof in
         O.out_text och (text s t);
         close_out och

let proc_fun ss (r, s, i, u, t) =
   proc_pair s (s :: ss) u (Some t)

let proc_obj u =
   let ss = K.segments_of_uri u in
   let _, _, _, _, obj = E.get_checked_obj G.status u in 
   match obj with 
      | C.Constant (_, s, xt, u, _) -> proc_pair s ss u xt
      | C.Fixpoint (_, fs, _)       -> L.iter (proc_fun ss) fs
      | C.Inductive (_, _, _, _)    -> not_supported ()

(* interface functions ******************************************************)

let process = proc_obj
