(* Copyright (C) 2000-2002, HELM Team.
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
(*                               PROJECT HELM                                *)
(*                                                                           *)
(*                Claudio Sacerdoti Coen <sacerdot@cs.unibo.it>              *)
(*                                 18/02/2003                                *)
(*                                                                           *)
(*                                                                           *)
(*****************************************************************************)

(* $Id$ *)

module MQI = MQueryInterpreter
module MQIC = MQIConn
module I = MQueryInterpreter
module U = MQGUtil
module G = MQueryGenerator

  (* search arguments on which Apply tactic doesn't fail *)
let matchConclusion mqi_handle ?(output_html = (fun _ -> ())) ~choose_must() status =
 let ((_, metasenv, _, _), metano) = status in
 let (_, ey ,ty) = CicUtil.lookup_meta metano metasenv in
  let list_of_must, only = CGMatchConclusion.get_constraints metasenv ey ty in
match list_of_must with
  [] -> []
|_ ->
  let must = choose_must list_of_must only in
  let result =
   I.execute mqi_handle 
      (G.query_of_constraints
        (Some CGMatchConclusion.universe)
        (must,[],[]) (Some only,None,None)) in 
  let uris =
   List.map
    (function uri,_ ->
      MQueryMisc.wrong_xpointer_format_from_wrong_xpointer_format' uri
    ) result
  in
  let uris =
    (* TODO ristretto per ragioni di efficienza *)
    prerr_endline "STO FILTRANDO";
    List.filter (fun uri -> Pcre.pmatch ~pat:"^cic:/Coq/" uri) uris
  in
     prerr_endline "HO FILTRATO"; 
  let uris',exc =
    let rec filter_out =
     function
        [] -> [],""
      | uri::tl ->
         let tl',exc = filter_out tl in
          try
           if 
	     let time = Unix.gettimeofday() in
            (try
             ignore(ProofEngineTypes.apply_tactic 
               (PrimitiveTactics.apply_tac
		  ~term:(MQueryMisc.term_of_cic_textual_parser_uri
			   (MQueryMisc.cic_textual_parser_uri_of_string uri)))
		  status);
	       let time1 = Unix.gettimeofday() in
		 prerr_endline (Printf.sprintf "%1.3f" (time1 -. time) );
               true
            with ProofEngineTypes.Fail _ -> 
	      let time1 = Unix.gettimeofday() in
              prerr_endline (Printf.sprintf "%1.3f" (time1 -. time)); false)
           then
            uri::tl',exc
           else
            tl',exc
          with
           (ProofEngineTypes.Fail _) as e ->
             let exc' =
              "<h1 color=\"red\"> ^ Exception raised trying to apply " ^
               uri ^ ": " ^ Printexc.to_string e ^ " </h1>" ^ exc
             in
              tl',exc'
    in
     filter_out uris
  in
    let html' =
     " <h1>Objects that can actually be applied: </h1> " ^
     String.concat "<br>" uris' ^ exc ^
     " <h1>Number of false matches: " ^
      string_of_int (List.length uris - List.length uris') ^ "</h1>" ^
     " <h1>Number of good matches: " ^
      string_of_int (List.length uris') ^ "</h1>"
    in
     output_html html' ;
     uris'
;;


(*matchConclusion modificata per evitare una doppia apply*)
let matchConclusion2 mqi_handle ?(output_html = (fun _ -> ())) ~choose_must() status =
  let ((_, metasenv, _, _), metano) = status in
  let (_, ey ,ty) = CicUtil.lookup_meta metano metasenv in
  let conn = 
    match mqi_handle.MQIConn.pgc with
	MQIConn.MySQL_C conn -> conn
      | _ -> assert false in
  let uris = Match_concl.cmatch conn ty in
  (* List.iter 
    (fun (n,u) -> prerr_endline ((string_of_int n) ^ " " ^u)) uris; *)
  (* delete all .var uris *)
  let uris = List.filter UriManager.is_var uris in 
  (* delete all not "cic:/Coq" uris *)
  (*
  let uris =
    (* TODO ristretto per ragioni di efficienza *)
    List.filter (fun _,uri -> Pcre.pmatch ~pat:"^cic:/Coq/" uri) uris in
  *)
  (* concl_cost are the costants in the conclusion of the proof 
     while hyp_const are the constants in the hypothesis *)
  let (main_concl,concl_const) = NewConstraints.mainandcons ty in
  prerr_endline ("Ne sono rimasti" ^ string_of_int (List.length uris));
  let hyp t set =
    match t with
      Some (_,Cic.Decl t) -> (NewConstraints.StringSet.union set (NewConstraints.constants_concl t))
    | Some (_,Cic.Def (t,_)) -> (NewConstraints.StringSet.union set (NewConstraints.constants_concl t))
    | _ -> set in
  let hyp_const =
    List.fold_right hyp ey NewConstraints.StringSet.empty in
  prerr_endline (NewConstraints.pp_StringSet (NewConstraints.StringSet.union hyp_const concl_const));
  (* uris with new constants in the proof are filtered *)
  let all_const = NewConstraints.StringSet.union hyp_const concl_const in
  let uris = 
    if (List.length uris < (Filter_auto.power 2 (List.length (NewConstraints.StringSet.elements all_const))))
     then 
     (prerr_endline("metodo vecchio");List.filter (Filter_auto.filter_new_constants conn all_const) uris)
    else Filter_auto.filter_uris conn all_const uris main_concl in 
(*
  let uris =
    (* ristretto all cache *)
    prerr_endline "SOLO CACHE";
    List.filter 
      (fun uri -> CicEnvironment.in_cache (UriManager.uri_of_string uri)) uris
  in 
  prerr_endline "HO FILTRATO2";
*)
  let uris =
    List.map
      (fun (n,u) -> 
	 (n,MQueryMisc.wrong_xpointer_format_from_wrong_xpointer_format' u)) 
      uris in
  let uris' =
    let rec filter_out =
     function
        [] -> []
      | (m,uri)::tl ->
          let tl' = filter_out tl in
            try
	           prerr_endline ("STO APPLICANDO " ^ uri);
              let res = (m,
		(ProofEngineTypes.apply_tactic( PrimitiveTactics.apply_tac
		   ~term:(MQueryMisc.term_of_cic_textual_parser_uri
			    (MQueryMisc.cic_textual_parser_uri_of_string uri)))
		   status))::tl' in
		prerr_endline ("OK");res
            (* with ProofEngineTypes.Fail _ -> tl' *)
            (* patch to cover CSC's exportation bug *)
            with _ -> prerr_endline ("FAIL");tl' 
     in    
     prerr_endline ("Ne sono rimasti 2 " ^ string_of_int (List.length uris));
     filter_out uris
   in
     prerr_endline ("Ne sono rimasti 3 " ^ string_of_int (List.length uris'));
   
     uris'
;;

(*funzione che sceglie il penultimo livello di profondita' dei must*)

(* 
let choose_must list_of_must only=
let n = (List.length list_of_must) - 1 in
   List.nth list_of_must n
;;*)

(* questa prende solo il main *) 
let choose_must list_of_must only =
   List.nth list_of_must 0 
 
(* livello 1
let choose_must list_of_must only =
   try 
     List.nth list_of_must 1
   with _ -> 
     List.nth list_of_must 0 *)

let  searchTheorems mqi_handle (proof,goal) =
  let subproofs =
    matchConclusion2 mqi_handle ~choose_must() (proof, goal) in
 let res =
  List.sort 
    (fun (n1,(_,gl1)) (n2,(_,gl2)) -> 
       let l1 = List.length gl1 in
       let l2 = List.length gl2 in
       (* if the list of subgoals have the same lenght we use the
	  prefix tag, where higher tags have precedence *)
       if l1 = l2 then n2 - n1
       else l1 - l2)
    subproofs
 in
  (* now we may drop the prefix tag *)
 (*let res' =
   List.map snd res in*)
 let order_goal_list proof goal1 goal2 =
   let _,metasenv,_,_ = proof in
   let (_, ey1, ty1) = CicUtil.lookup_meta goal1 metasenv in
   let (_, ey2, ty2) =  CicUtil.lookup_meta goal2 metasenv in
(*
   prerr_endline "PRIMA DELLA PRIMA TYPE OF " ;
*)
   let ty_sort1,u = (*TASSI: FIXME *)
     CicTypeChecker.type_of_aux' metasenv ey1 ty1 CicUniv.oblivion_ugraph in
(*
   prerr_endline (Printf.sprintf "PRIMA DELLA SECONDA TYPE OF %s \n### %s @@@%s " (CicMetaSubst.ppmetasenv metasenv []) (CicMetaSubst.ppcontext [] ey2) (CicMetaSubst.ppterm [] ty2));
*)
   let ty_sort2,u1 = CicTypeChecker.type_of_aux' metasenv ey2 ty2 u in
(*
   prerr_endline "DOPO LA SECONDA TYPE OF " ;
*)
   let b,u2 = 
     CicReduction.are_convertible ey1 (Cic.Sort Cic.Prop) ty_sort1 u1 in
   let prop1 = if b then 0 else 1 in
   let b,_ = CicReduction.are_convertible ey2 (Cic.Sort Cic.Prop) ty_sort2 u2 in
   let prop2 = if b then 0 else 1 in
     prop1 - prop2 in
   List.map (
     fun (level,(proof,goallist)) -> 
       (proof, (List.stable_sort (order_goal_list proof) goallist))
   ) res  
;;

