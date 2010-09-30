(* Copyright (C) 2000, HELM Team.
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

(*****************************************************************************)
(*                                                                           *)
(*                              PROJECT HELM                                 *)
(*                                                                           *)
(*                     Enrico Tassi <tassi@cs.unibo.it>                      *)
(*                                23/04/2004                                 *)
(*                                                                           *)
(* This module implements some useful function regarding univers graphs      *)
(*                                                                           *)
(*****************************************************************************)

(* $Id$ *)

module C = Cic
module H = UriManager.UriHashtbl 
let eq  = UriManager.eq

(* uri is the uri of the actual object that must be 'skipped' *)
let universes_of_obj uri t =
  (* don't the same work twice *)
  let visited_objs = H.create 31 in
  let visited u = H.replace visited_objs u true in 
  let is_not_visited u = not (H.mem visited_objs u) in 
  visited uri;
  (* the result *)
  let results = ref [] in
  let add_result l = results := l :: !results in
  (* the iterators *)
  let rec aux = function
    | C.Const (u,exp_named_subst) when is_not_visited u ->
        aux_uri u;
        visited u;
        C.Const (u, List.map (fun (x,t) -> x,aux t) exp_named_subst)
    | C.Var (u,exp_named_subst) when is_not_visited u ->
        aux_uri u;
        visited u;
        C.Var (u,  List.map (fun (x,t) -> x,aux t) exp_named_subst)
    | C.Const (u,exp_named_subst) ->
        C.Const (u, List.map (fun (x,t) -> x,aux t) exp_named_subst)
    | C.Var (u,exp_named_subst) ->
        C.Var (u,  List.map (fun (x,t) -> x,aux t) exp_named_subst)
    | C.MutInd (u,x,exp_named_subst) when is_not_visited u ->
        aux_uri u;
        visited u;
        C.MutInd (u,x,List.map (fun (x,t) -> x,aux t) exp_named_subst)
    | C.MutInd (u,x,exp_named_subst) ->
        C.MutInd (u,x, List.map (fun (x,t) -> x,aux t) exp_named_subst)
    | C.MutConstruct (u,x,y,exp_named_subst) when is_not_visited u ->
        aux_uri u;
        visited u;
        C.MutConstruct (u,x,y,List.map (fun (x,t) -> x,aux t) exp_named_subst)
    | C.MutConstruct (x,y,z,exp_named_subst) ->
        C.MutConstruct (x,y,z,List.map (fun (x,t) -> x,aux t) exp_named_subst)
    | C.Meta (n,l1) -> C.Meta (n, List.map (HExtlib.map_option aux) l1)
    | C.Sort (C.Type i) -> add_result [i]; 
      C.Sort (C.Type (CicUniv.name_universe i uri))
    | C.Sort (C.CProp i) -> add_result [i]; 
      C.Sort (C.CProp (CicUniv.name_universe i uri))
    | C.Rel _ 
    | C.Sort _
    | C.Implicit _ as x -> x
    | C.Cast (v,t) -> C.Cast (aux v, aux t)
    | C.Prod (b,s,t) -> C.Prod (b,aux s, aux t)
    | C.Lambda (b,s,t) ->  C.Lambda (b,aux s, aux t)
    | C.LetIn (b,s,ty,t) -> C.LetIn (b,aux s, aux ty, aux t)
    | C.Appl li -> C.Appl (List.map aux li)
    | C.MutCase (uri,n1,ty,te,patterns) ->
        C.MutCase (uri,n1,aux ty,aux te, List.map aux patterns)
    | C.Fix (no, funs) -> 
        C.Fix(no, List.map (fun (x,y,b,c) -> (x,y,aux b,aux c)) funs)
    | C.CoFix (no,funs) -> 
        C.CoFix(no, List.map (fun (x,b,c) -> (x,aux b,aux c)) funs)
  and aux_uri u =
    if is_not_visited u then
      let _, _, l = 
        CicEnvironment.get_cooked_obj_with_univlist CicUniv.empty_ugraph u in 
      add_result l
  and aux_obj = function
    | C.Constant (x,Some te,ty,v,y) ->
        List.iter aux_uri v;
        C.Constant (x,Some (aux te),aux ty,v,y)
    | C.Variable (x,Some te,ty,v,y) -> 
        List.iter aux_uri v;
        C.Variable (x,Some (aux te),aux ty,v,y)
    | C.Constant (x,None, ty, v,y) ->
        List.iter aux_uri v;
        C.Constant (x,None, aux ty, v,y)
    | C.Variable (x,None, ty, v,y) ->
        List.iter aux_uri v;
        C.Variable (x,None, aux ty, v,y)
    | C.CurrentProof (_,conjs,te,ty,v,_) -> assert false
    | C.InductiveDefinition (l,v,x,y) -> 
        List.iter aux_uri v; 
        C.InductiveDefinition (
          List.map
           (fun (x,y,t,l') ->
             (x,y,aux t, List.map (fun (x,t) -> x,aux t) l'))
          l,v,x,y)  
  in 
  let o = aux_obj t in
  List.flatten !results, o

let list_uniq l = 
  HExtlib.list_uniq (List.fast_sort CicUniv.compare l)
  
let clean_and_fill uri obj ugraph =
  (* universes of obj fills the universes of the obj with the right uri *)
  let list_of_universes, obj = universes_of_obj uri obj in
  let list_of_universes = list_uniq list_of_universes in
(*  CicUniv.print_ugraph ugraph;*)
(*  List.iter (fun u -> prerr_endline (CicUniv.string_of_universe u))*)
(*  list_of_universes;*)
  let ugraph = CicUniv.clean_ugraph ugraph list_of_universes in
(*  CicUniv.print_ugraph ugraph;*)
  let ugraph, list_of_universes = 
    CicUniv.fill_empty_nodes_with_uri ugraph list_of_universes uri 
  in
  ugraph, list_of_universes, obj

(*
let profiler = (HExtlib.profile "clean_and_fill").HExtlib.profile
let clean_and_fill u o g =
  profiler (clean_and_fill u o) g
*)
