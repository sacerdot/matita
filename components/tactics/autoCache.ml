(* Copyright (C) 2002, HELM Team.
 * 
 * This file is part of HELM, an Hypertextual, Electronic
 * Library of Mathematics, developed at the Computer Science
 * Department, University of Bologna, Italy.
 * 
 * HELM is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 * 
 * HELM is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with HELM; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston,
 * MA  02111-1307, USA.
 * 
 * For details, see the HELM World-Wide-Web page,
 * http://cs.unibo.it/helm/.
 *)

type cache_key = Cic.term
type cache_elem = 
  | Failed_in of int
  | Succeded of Cic.term
  | UnderInspection
  | Notfound
type cache = (Universe.universe * ((cache_key * cache_elem) list));;

let debug = false;;
let prerr_endline s = 
  if debug then prerr_endline s else ()
;;

let cache_empty = (Universe.empty,[]);;

let get_candidates (univ,_) ty = 
(*   if Universe.key ty = ty then *)
    Universe.get_candidates univ ty
(*
  else 
    (prerr_endline ("skip: " ^ CicPp.ppterm (Universe.key ty)); [])
 *)
;;

let index (univ,cache) key term =
  Universe.index univ key term,cache
;;

let index_term_and_unfolded_term (univ,cache) context t ty =
  Universe.index_local_term univ context t ty, cache
;;

let cache_add_list (univ,cache) context terms_and_types =
  let univ = 
    List.fold_left
      (fun univ (t,ty) -> 
         prerr_endline ("indexing: " ^ CicPp.ppterm ty);
	 Universe.index_local_term univ context t ty)
      univ terms_and_types  
  in
  univ, cache

let cache_examine (_,oldcache) cache_key = 
  prerr_endline ("examine : " ^ CicPp.ppterm cache_key);
  try snd (List.find (fun (x,_) -> CicUtil.alpha_equivalence x cache_key) 
        oldcache) with Not_found -> 
    prerr_endline "notfound";
    Notfound
;;
let cache_replace (univ,oldcache) key v =
  let oldcache = List.filter (fun (i,_) -> i <> key) oldcache in
  univ, (key,v)::oldcache
;;
let cache_remove (univ,oldcache) key =
  let oldcache = List.filter (fun (i,_) -> i <> key) oldcache in
  univ,oldcache
;;
let cache_add_failure cache cache_key depth =
  prerr_endline 
    ("CACHE: ADD FAIL " ^ CicPp.ppterm cache_key ^ 
      " depth: " ^ string_of_int depth);
  match cache_examine cache cache_key with
  | Failed_in i when i > depth -> cache
  | Notfound  
  | Failed_in _ 
  | UnderInspection -> cache_replace cache cache_key (Failed_in depth)
  | Succeded t -> cache 
                  (*
      prerr_endline (CicPp.ppterm t);
      assert false (* if succed it can't fail *) *)
;;
let cache_add_success ((univ,_) as cache) cache_key proof =
  let u_key = Universe.key cache_key in
  if u_key <> cache_key then
    Universe.index univ u_key proof, snd cache
  else
    univ, 
    snd 
    (match cache_examine cache cache_key with
    | Failed_in _ -> cache_replace cache cache_key (Succeded proof)
    | UnderInspection -> cache_replace cache cache_key (Succeded proof)
    | Succeded t -> (* we may decide to keep the smallest proof *) cache
    | Notfound -> cache_replace cache cache_key (Succeded proof))
(*
  (if Universe.key cache_key = cache_key then
    Universe.index univ cache_key proof
  else
    univ),snd
  (prerr_endline ("CACHE: ADD SUCCESS" ^ CicPp.ppterm cache_key);
  match cache_examine cache cache_key with
  | Failed_in _ -> cache_replace cache cache_key (Succeded proof)
  | UnderInspection -> cache_replace cache cache_key (Succeded proof)
  | Succeded t -> (* we may decide to keep the smallest proof *) cache
  | Notfound -> cache_replace cache cache_key (Succeded proof))
;;
*)
let cache_add_underinspection ((univ,oldcache) as cache) cache_key depth =
  prerr_endline ("CACHE: ADD INSPECTING" ^ CicPp.ppterm cache_key);
  match cache_examine cache cache_key with
  | Failed_in i when i < depth -> cache_replace cache cache_key UnderInspection
  | Notfound -> univ,(cache_key,UnderInspection)::oldcache
  | Failed_in _ 
  | UnderInspection 
  | Succeded _ -> assert false (* it must be a new goal *)
;;
let cache_print context (_,oldcache) = 
  let names = List.map (function None -> None | Some (x,_) -> Some x) context in
  String.concat "\n" 
    (HExtlib.filter_map 
      (function 
        | (k,Succeded _) -> Some ("CACHE SUCCESS: " ^ CicPp.pp k names)
        | _ -> None)
      oldcache)
;;
let cache_remove_underinspection ((univ,oldcache) as cache) cache_key =
  prerr_endline ("CACHE: REMOVE INSPECTING" ^ CicPp.ppterm cache_key);
  match cache_examine cache cache_key with
  | Notfound 
  | Failed_in _ (* -> assert false  *)
  | UnderInspection ->  cache_remove cache cache_key
  | Succeded _ -> cache (* 
      prerr_endline (CicPp.ppterm cache_key);            
      assert false (* it must be a new goal *) *)
;;
let cache_size (_,oldcache) = 
  List.length (List.filter (function (_,Succeded _) -> true | _ -> false) oldcache)
;;
let cache_clean (univ,oldcache) = 
  univ,List.filter (function (_,Succeded _) -> true | _ -> false) oldcache
;;
let cache_reset_underinspection (u,c) =
  u,List.filter (function (_,UnderInspection) -> false | _ -> true) c
;;
