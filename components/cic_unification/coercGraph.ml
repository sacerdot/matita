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

(* $Id$ *)

open Printf;;

type coercion_search_result = 
     (* metasenv, last coercion argument, fully saturated coercion *)
     (* to apply the coercion it is sufficient to unify the last coercion
        argument (that is a Meta) with the term to be coerced *)
  | SomeCoercion of (Cic.metasenv * Cic.term * Cic.term) list
  | SomeCoercionToTgt of (Cic.metasenv * Cic.term * Cic.term) list
  | NoCoercion
  | NotHandled

let debug = false
let debug_print s = if debug then prerr_endline (Lazy.force s) else ()

let saturate_coercion ul metasenv subst context =
  let cl =
   List.map 
     (fun u,saturations -> 
        let t = CicUtil.term_of_uri u in 
        let arity = 
          match CoercDb.is_a_coercion t with
          | Some (_,CoercDb.Fun i,_,_,_) -> i
          | _ -> 0
        in
        arity,t,saturations) ul
  in
  let freshmeta = CicMkImplicit.new_meta metasenv subst in
   List.map
    (fun (arity,c,saturations) -> 
      let ty,_ =
       CicTypeChecker.type_of_aux' ~subst metasenv context c
        CicUniv.oblivion_ugraph in
      let _,metasenv,args,lastmeta =
       TermUtil.saturate_term ~delta:false freshmeta metasenv context ty arity in
      let irl =
       CicMkImplicit.identity_relocation_list_for_metavariable context
      in
       metasenv, Cic.Meta (lastmeta - saturations - 1,irl),
        match args with
           [] -> c
         | _ -> Cic.Appl (c::args)
    ) cl
;;
          
(* searches a coercion fron src to tgt in the !coercions list *)
let look_for_coercion_carr metasenv subst context src tgt =
  let is_dead = function CoercDb.Dead -> true | _ -> false in
  let pp_l s l =
   match l with
   | [] -> 
       debug_print 
         (lazy 
         (sprintf ":-( coercion non trovata[%s] da %s a %s" s
             (CoercDb.string_of_carr src) 
             (CoercDb.string_of_carr tgt)));
   | _::_ -> 
       debug_print (lazy (
               sprintf ":-) TROVATE[%s] %d coercion(s) da %s a %s" s
           (List.length l)
           (CoercDb.string_of_carr src) 
           (CoercDb.string_of_carr tgt)));
  in
  if is_dead src || is_dead tgt then NotHandled
  else
    let l = 
      CoercDb.find_coercion 
        (fun (s,t) -> 
          CoercDb.eq_carr s src && 
          match t, tgt with
          | CoercDb.Sort Cic.Prop, CoercDb.Sort Cic.Prop 
          | CoercDb.Sort Cic.Set, CoercDb.Sort Cic.Set 
          | CoercDb.Sort _, CoercDb.Sort (Cic.Type _|Cic.CProp _) -> true
          | _ -> CoercDb.eq_carr t tgt) 
    in
    pp_l "precise" l;
     (match l with
     | [] -> 
         let l = 
           CoercDb.find_coercion 
             (fun (_,t) -> CoercDb.eq_carr t tgt) 
         in
         pp_l "approx" l;
         (match l with
         | [] -> NoCoercion
         | ul -> 
            SomeCoercionToTgt (saturate_coercion ul metasenv subst context))
     | ul -> SomeCoercion (saturate_coercion ul metasenv subst context))
;;

let rec count_pi c s t =
  match CicReduction.whd ~delta:false ~subst:s c t with
  | Cic.Prod (_,_,t) -> 1 + count_pi c s t
  | _ -> 0
;;

let look_for_coercion metasenv subst context src tgt = 
  let src_arity = count_pi context subst src in
  let tgt_arity = count_pi context subst tgt in
  let src_carr = CoercDb.coerc_carr_of_term src src_arity in
  let tgt_carr = CoercDb.coerc_carr_of_term tgt tgt_arity in
  look_for_coercion_carr metasenv subst context src_carr tgt_carr

let source_of t = 
  match CoercDb.is_a_coercion t with
  | None -> assert false
  | Some (CoercDb.Sort s,_,_,_,_) -> Cic.Sort s
  | Some (CoercDb.Uri u,_,_,_,_) -> CicUtil.term_of_uri u
  | Some _ -> assert false (* t must be a coercion not to funclass *)
;;

let generate_dot_file fmt =
  let l = CoercDb.to_list (CoercDb.dump ()) in
  let module Pp = GraphvizPp.Dot in
  if List.exists (fun (_,t,_) -> CoercDb.string_of_carr t = "Type") l then
    Format.fprintf fmt "subgraph cluster_rest { style=\"filled\";
    color=\"white\"; label=<%s>; labelloc=\"b\"; %s; }\n" 
       ("<FONT POINT-SIZE=\"10.0\"><TABLE BORDER=\"1\" CELLBORDER=\"1\" >
         <TR><TD BGCOLOR=\"gray95\">Source</TD>
         <TD BGCOLOR=\"gray95\">Target</TD>
         <TD BGCOLOR=\"gray95\">Arrows</TD></TR>"^
       String.concat "</TR>"   
         (List.map 
           (fun (src,tgt,ul) -> 
            let src_name = CoercDb.string_of_carr src in
            let tgt_name = CoercDb.string_of_carr tgt in
            let names = 
              List.map (fun (u,_,_) -> 
                UriManager.name_of_uri u ^ 
                  (match CicEnvironment.get_obj CicUniv.empty_ugraph u with
                  | Cic.Constant (_,Some (Cic.Const (u',_)),_,_,attrs), _
                    when List.exists ((=) (`Flavour `Variant)) attrs -> "*"
                  | _ -> "")
              ) ul 
            in
            "<TR><TD>"  ^ src_name ^ "</TD><TD>" ^ tgt_name ^ "</TD><TD>" ^
            String.concat ",&nbsp;" names ^ "</TD>")
         (List.sort (fun (x,y,_) (x1,y1,_) -> 
             let rc = compare x x1 in
             if rc = 0 then compare y y1 else rc) l))
       ^ "</TR></TABLE></FONT>")
       (String.concat ";" ["Type"]);
  let type_uri u = 
    let ty, _ = 
      CicTypeChecker.type_of_aux' [] [] (CicUtil.term_of_uri u)
      CicUniv.oblivion_ugraph
    in
      ty
  in
  let deref_coercion u =
   match CicEnvironment.get_obj CicUniv.empty_ugraph u with
   | Cic.Constant (_,Some (Cic.Const (u',_)),_,_,attrs), _
     when List.exists ((=) (`Flavour `Variant)) attrs ->
       UriManager.name_of_uri u'
   | Cic.Constant (_,Some t,_,_,_), _ when
       let rec is_id = function 
         | Cic.Lambda (_,_,t) -> is_id t
         | Cic.Rel _ -> true
         | _ -> false
         in is_id t -> "ID"
   | _ -> UriManager.name_of_uri u
  in
  List.iter
    (fun (src, tgt, ul) ->
      List.iter
        (fun (u,saturations,cpos) ->
          let ty = type_uri u in
          let src_name, tgt_name = 
            let rec aux ctx cpos t =
              match cpos, t with
              | 0,Cic.Prod (_,src,tgt) ->
                  CicPp.pp src ctx, tgt, (Some (Cic.Name "_")::ctx)
              | 0,t -> CicPp.pp t ctx, Cic.Implicit None, []
              | n,Cic.Prod (_,_,tgt) -> aux (Some (Cic.Name "_")::ctx) (n-1) tgt
              | _ -> assert false
            in
            let ssrc, rest, ctx = aux [] cpos ty in
            let stgt, rest, _ = aux ctx saturations rest in
            let stgt = 
              if rest <> Cic.Implicit None then
                match tgt with 
                | CoercDb.Fun _ -> CoercDb.string_of_carr tgt
                | _ -> assert false
              else
                stgt
            in
            ssrc, stgt
          in
          Pp.node src_name fmt;
          Pp.node tgt_name fmt;
          Pp.edge src_name tgt_name
            ~attrs:[ "label",
                 (deref_coercion u ^
                  if saturations = 0 then ""
                  else "(" ^ string_of_int saturations ^ ")");
              "href", UriManager.string_of_uri u ]
            fmt)
        ul)
    l;
;;
    
let coerced_arg l =
  match l with
  | [] | [_] -> None
  | c::tl -> 
     match CoercDb.is_a_coercion c with 
     | None -> None
     | Some (_,_,_,_,cpos) -> 
        if List.length tl > cpos then Some (List.nth tl cpos, cpos) else None
;;

(************************* meet calculation stuff ********************)
let eq_uri_opt u1 u2 = 
  match u1,u2 with
  | Some (u1,_), Some (u2,_) -> UriManager.eq u1 u2
  | None,Some _ | Some _, None -> false
  | None, None -> true
;;

let eq_carr_uri (c1,u1) (c2,u2) = CoercDb.eq_carr c1 c2 && eq_uri_opt u1 u2;;

let eq_carr_uri_uri (c1,u1,u11) (c2,u2,u22) = 
  CoercDb.eq_carr c1 c2 && eq_uri_opt u1 u2 && eq_uri_opt u11 u22
;;

let uniq = HExtlib.list_uniq ~eq:eq_carr_uri;;

let uniq2 = HExtlib.list_uniq ~eq:eq_carr_uri_uri;;

let splat e l = List.map (fun (x1,x2,_) -> e, Some (x1,x2)) l;;

(* : carr -> (carr * uri option) where the option is always Some *)
let get_coercions_to carr = 
  let l = CoercDb.to_list (CoercDb.dump ()) in
  let splat_coercion_to carr (src,tgt,cl) =
    if CoercDb.eq_carr tgt carr then Some (splat src cl) else None
  in
  let l = List.flatten (HExtlib.filter_map (splat_coercion_to carr) l) in
  l
;;

(* : carr -> (carr * uri option) where the option is always Some *)
let get_coercions_from carr = 
  let l = CoercDb.to_list (CoercDb.dump ()) in
  let splat_coercion_from carr (src,tgt,cl) =
    if CoercDb.eq_carr src carr then Some (splat tgt cl) else None
  in
  List.flatten (HExtlib.filter_map (splat_coercion_from carr) l)
;;

(* intersect { (s1,u1) | u1:s1->t1 } { (s2,u2) | u2:s2->t2 } 
 * gives the set { (s,u1,u2) | u1:s->t1 /\ u2:s->t2 } *)
let intersect l1 l2 = 
  let is_in_l1 (x,u2) = 
    HExtlib.filter_map 
      (fun (src,u1) -> 
         if CoercDb.eq_carr x src then Some (src,u1,u2) else None)
    l1
  in
  uniq2 (List.flatten (List.map is_in_l1 l2))
;;

(* grow tgt gives all the (src,u) such that u:tgt->src *)
let grow tgt = 
  uniq ((tgt,None)::(get_coercions_to tgt))
;;

let lb (c,_,_) = 
  let l = get_coercions_from c in
  fun (x,_,_) -> List.exists (fun (y,_) -> CoercDb.eq_carr x y) l
;;

(* given the set { (s,u1,u2) | u1:s->t1 /\ u2:s->t2 } removes the elements 
 * (s,_,_) such that (s',_,_) is in the set and there exists a coercion s->s' *)
let rec min acc skipped = function
  | c::tl -> 
    if List.exists (lb c) (tl@acc) 
    then min acc (c::skipped) tl else min (c::acc) skipped tl
  | [] -> acc, skipped
;;


let sort l = 
  let low, high = min [] [] l in low @ high
;;

let meets metasenv subst context (grow_left,left) (grow_right,right) =
  let saturate metasenv uo =
    match uo with 
    | None -> metasenv, None
    | Some u -> 
        match saturate_coercion [u] metasenv subst context with
        | [metasenv, sat, last] -> metasenv, Some (sat, last)
        | _ -> assert false
  in
  List.map 
    (fun (c,uo1,uo2) -> 
      let metasenv, uo1 = saturate metasenv uo1 in
      let metasenv, uo2 = saturate metasenv uo2 in
      c,metasenv, uo1, uo2)
    (sort (intersect 
      (if grow_left then grow left else [left,None]) 
      (if grow_right then grow right else [right,None])))
;;

(* EOF *)
