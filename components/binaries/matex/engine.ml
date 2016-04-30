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
module N = Alpha

type status = {
   n: string;   (* reference name *)
   s: int list; (* scope *)
} 

(* internal functions *******************************************************)

let internal s =
   X.error ("engine: malformed stack: " ^ s)

let malformed s =
   X.error ("engine: malformed term: " ^ s)

(* generic term processing *)

let proc_sort is = function
   | C.Prop             -> T.Macro "PROP" :: is
   | C.Type [`Type, u]  -> T.Macro "TYPE" :: T.arg (U.string_of_uri u) :: is
   | C.Type [`CProp, u] -> T.Macro "CROP" :: T.arg (U.string_of_uri u) :: is
   | C.Type _           -> malformed "T1"

let rec proc_term is c = function
   | C.Appl []
   | C.Meta _
   | C.Implicit _           -> malformed "T2" 
   | C.Rel m                ->
      let name = K.resolve_lref c m in
      T.Macro "LREF" :: T.arg name :: T.free name :: is
   | C.Appl ts              ->
      let riss = L.rev_map (proc_term [] c) ts in
      T.Macro "APPL" :: T.mk_rev_args riss is
   | C.Prod (s, w, t)       ->
      let is_w = proc_term [] c w in
      let is_t = proc_term is (K.add_dec s w c) t in
      T.Macro "PROD" :: T.arg s :: T.Group is_w :: is_t
   | C.Lambda (s, w, t)     -> 
      let is_w = proc_term [] c w in
      let is_t = proc_term is (K.add_dec s w c) t in
      T.Macro "ABST" :: T.arg s :: T.Group is_w :: is_t
   | C.LetIn (s, w, v, t)   ->
      let is_w = proc_term [] c w in
      let is_v = proc_term [] c v in
      let is_t = proc_term is (K.add_def s w v c) t in
      T.Macro "ABBR" :: T.arg s :: T.Group is_w :: T.Group is_v :: is_t
   | C.Sort s               ->
      proc_sort is s
   | C.Const (R.Ref (u, r)) ->
      let ss = K.segments_of_uri u in
      let _, _, _, _, obj = E.get_checked_obj G.status u in  
      let ss, name = K.name_of_reference ss (obj, r) in
      T.Macro "GREF" :: T.arg name :: T.free (X.rev_map_concat X.id "." "type" ss) :: is
   | C.Match (w, u, v, ts)  ->
      let is_w = proc_term [] c (C.Const w) in
      let is_u = proc_term [] c u in
      let is_v = proc_term [] c v in
      let riss = L.rev_map (proc_term [] c) ts in
      T.Macro "CASE" :: T.Group is_w :: T.Group is_u :: T.Group is_v :: T.mk_rev_args riss is

let proc_term is c t = try proc_term is c t with
   | E.ObjectNotFound _ 
   | Invalid_argument "List.nth"
   | Failure "nth" 
   | Failure "name_of_reference" -> malformed "T3"

(* proof processing *)

let typeof c = function
   | C.Appl [t]
   | t          -> K.whd_typeof c t

let init () = {
   n =  ""; s = [1]
}

let push st n = {
   n = n; s = 1 :: st.s;
}

let next st = {
   n = ""; s = match st.s with [] -> failwith "hd" | i :: tl -> succ i :: tl
}

let scope st =
   X.rev_map_concat string_of_int "." "" (L.tl st.s)

let mk_exit st ris =
   if st.n <> "" || L.tl st.s = [] then ris else
   T.free (scope st) :: T.Macro "EXIT" :: ris

let mk_open st ris =
   if st.n = "" then ris else
   T.free (scope st) :: T.free st.n :: T.arg st.n :: T.Macro "OPEN" :: ris

let mk_dec kind w s ris =
   let w = if !G.no_types then [] else w in
   T.Group w :: T.free s :: T.arg s :: T.Macro kind :: ris

let mk_inferred st c t ris =
   let u = typeof c t in
   let is_u = proc_term [] c u in
   mk_dec "DECL" is_u st.n ris

let rec proc_proof st ris c t = match t with
   | C.Appl []
   | C.Meta _
   | C.Implicit _  
   | C.Sort _
   | C.Prod _              -> malformed "P1"
   | C.Const _
   | C.Rel _               -> proc_proof st ris c (C.Appl [t])
   | C.Lambda (s, w, t)    ->
      let is_w = proc_term [] c w in
      let ris = mk_open st ris in
      proc_proof (next st) (mk_dec "PRIM" is_w s ris) (K.add_dec s w c) t
   | C.Appl (t0 :: ts)     ->
      let rts = X.rev_neg_filter (K.not_prop2 c) [t0] ts in
      let ris = T.Macro "STEP" :: mk_inferred st c t ris in
      let tts = L.rev_map (proc_term [] c) rts in
      mk_exit st (T.rev_mk_args tts ris)
   | C.Match (w, u, v, ts) ->
      let rts = X.rev_neg_filter (K.not_prop2 c) [v] ts in
      let ris = T.Macro "DEST" :: mk_inferred st c t ris in
      let tts = L.rev_map (proc_term [] c) rts in
      mk_exit st (T.rev_mk_args tts ris)
   | C.LetIn (s, w, v, t)  -> 
      let is_w = proc_term [] c w in
      let ris = mk_open st ris in
      if K.not_prop1 c w then
         let is_v = proc_term [] c v in
         let ris = T.Group is_v :: T.Macro "BODY" :: mk_dec "DECL" is_w s ris in
         proc_proof (next st) ris (K.add_def s w v c) t
      else
         let ris_v = proc_proof (push st s) ris c v in
         proc_proof (next st) ris_v (K.add_def s w v c) t

let proc_proof rs c t = try proc_proof (init ()) rs c t with 
   | E.ObjectNotFound _ 
   | Invalid_argument "List.nth"
   | Failure "nth"
   | Failure "name_of_reference" -> malformed "P2"
   | V.TypeCheckerFailure s
   | V.AssertFailure s           -> malformed (Lazy.force s)
   | Failure "hd"
   | Failure "tl"                -> internal "P2"

(* top level processing *)

let note = T.Note "This file was automatically generated by MaTeX: do not edit"

let proc_item item s ss t =
   let tt = N.process_top_term s t in (* alpha-conversion *)
   let is = [T.Macro "end"; T.arg item] in
   note :: T.Macro "begin" :: T.arg item :: T.arg s :: T.free ss :: proc_term is [] tt

let proc_top_proof s ss t =
   let t0 = A.process_top_term s t in  (* anticipation *)
   let tt = N.process_top_term s t0 in (* alpha-conversion *)
   let ris = [T.free ss; T.arg s; T.arg "proof"; T.Macro "begin"; note] in
   L.rev (T.arg "proof" :: T.Macro "end" :: proc_proof ris [] tt)

let open_out_tex s =
   let fname = s ^ T.file_ext in
   begin match !G.list_och with
      | None     -> ()
      | Some och -> P.fprintf och "%s\n" fname
   end;
   open_out (F.concat !G.out_dir fname)

let proc_pair s ss u = function
   | None   -> 
      let name = X.rev_map_concat X.id "." "type" ss in
      let och = open_out_tex name in
         O.out_text och (proc_item "axiom" s name u);
      close_out och
   | Some t ->
      let text_u, text_t =
         if K.not_prop1 [] u then proc_item "declaration", proc_item "definition"
         else proc_item "proposition", proc_top_proof
      in
      let name = X.rev_map_concat X.id "." "type" ss in
      let och = open_out_tex name in
         O.out_text och (text_u s name u);
      close_out och;
      let name = X.rev_map_concat X.id "." "body" ss in
      let och = open_out_tex name in
         O.out_text och (text_t s name t);
      close_out och

let proc_fun ss (r, s, i, u, t) =
   proc_pair s (s :: ss) u (Some t)

let proc_constructor ss (r, s, u) =
   proc_pair s (s :: ss) u None

let proc_type ss (r, s, u, cs) =
   proc_pair s (s :: ss) u None;
   L.iter (proc_constructor ss) cs

let proc_obj u =
   let ss = K.segments_of_uri u in
   let _, _, _, _, obj = E.get_checked_obj G.status u in 
   match obj with 
      | C.Constant (_, s, xt, u, _) -> proc_pair s ss u xt
      | C.Fixpoint (_, fs, _)       -> L.iter (proc_fun ss) fs
      | C.Inductive (_, _, ts, _)   -> L.iter (proc_type ss) ts

(* interface functions ******************************************************)

let process = proc_obj
