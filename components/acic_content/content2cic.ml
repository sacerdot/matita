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

(***************************************************************************)
(*                                                                         *)
(*                            PROJECT HELM                                 *)
(*                                                                         *)
(*                Andrea Asperti <asperti@cs.unibo.it>                     *)
(*                              17/06/2003                                 *)
(*                                                                         *)
(***************************************************************************)

(* $Id$ *)

exception TO_DO;;

let proof2cic deannotate p =
  let rec proof2cic premise_env p =
    let module C = Cic in 
    let module Con = Content in
      let rec extend_premise_env current_env = 
        function
            [] -> current_env
          | p::atl ->
              extend_premise_env 
              ((p.Con.proof_id,(proof2cic current_env p))::current_env) atl in
      let new_premise_env = extend_premise_env premise_env p.Con.proof_apply_context in
      let body = conclude2cic new_premise_env p.Con.proof_conclude in
      context2cic premise_env p.Con.proof_context body

  and context2cic premise_env context body =
    List.fold_right (ce2cic premise_env) context body

  and ce2cic premise_env ce target =
    let module C = Cic in
    let module Con = Content in
      match ce with
        `Declaration d -> 
          (match d.Con.dec_name with
              Some s ->
                C.Lambda (C.Name s, deannotate d.Con.dec_type, target)
            | None -> 
                C.Lambda (C.Anonymous, deannotate d.Con.dec_type, target))
      | `Hypothesis h ->
          (match h.Con.dec_name with
              Some s ->
                C.Lambda (C.Name s, deannotate h.Con.dec_type, target)
            | None -> 
                C.Lambda (C.Anonymous, deannotate h.Con.dec_type, target))
      | `Proof p -> 
          let ty =
           match p.Con.proof_conclude.Con.conclude_conclusion with
              None -> (*Cic.Implicit None*) assert false
            | Some ty -> deannotate ty
          in
          (match p.Con.proof_name with
              Some s ->
                C.LetIn (C.Name s, proof2cic premise_env p, ty , target)
            | None -> 
                C.LetIn (C.Anonymous, proof2cic premise_env p, ty, target)) 
      | `Definition d -> 
           (match d.Con.def_name with
              Some s ->
                C.LetIn (C.Name s, proof2cic premise_env p, deannotate d.Con.def_type, target)
            | None -> 
                C.LetIn (C.Anonymous, proof2cic premise_env p, deannotate d.Con.def_type, target)) 
      | `Joint {Con.joint_kind = kind; Con.joint_defs = defs} -> 
            (match target with
               C.Rel n ->
                 (match kind with 
                    `Recursive l ->
                      let funs = 
                        List.map2 
                          (fun n bo ->
                             match bo with
                               `Proof bo ->
                                  (match 
                                    bo.Con.proof_conclude.Con.conclude_conclusion,
                                    bo.Con.proof_name
                                   with
                                      Some ty, Some name -> 
                                       (name,n,deannotate ty,
                                         proof2cic premise_env bo)
                                    | _,_ -> assert false)
                             | _ -> assert false)
                          l defs in 
                      C.Fix (n, funs)
                  | `CoRecursive ->
                     let funs = 
                        List.map 
                          (function bo ->
                             match bo with
                              `Proof bo ->
                                 (match 
                                    bo.Con.proof_conclude.Con.conclude_conclusion,
                                    bo.Con.proof_name 
                                  with
                                     Some ty, Some name ->
                                      (name,deannotate ty,
                                        proof2cic premise_env bo)
                                   | _,_ -> assert false)
                             | _ -> assert false)
                           defs in 
                      C.CoFix (n, funs)
                  | _ -> (* no inductive types in local contexts *)
                       assert false)
             | _ -> assert false)

  and conclude2cic premise_env conclude =
    let module C = Cic in 
    let module Con = Content in
    if conclude.Con.conclude_method = "TD_Conversion" then
      (match conclude.Con.conclude_args with
         [Con.ArgProof p] -> proof2cic [] p (* empty! *)
       | _ -> prerr_endline "1"; assert false)
    else if conclude.Con.conclude_method = "BU_Conversion" then
      (match conclude.Con.conclude_args with
         [Con.Premise prem] -> 
           (try List.assoc prem.Con.premise_xref premise_env
            with Not_found -> 
              prerr_endline
               ("Not_found in BU_Conversion: " ^ prem.Con.premise_xref);
              raise Not_found)
       | _ -> prerr_endline "2"; assert false)
    else if conclude.Con.conclude_method = "Exact" then
      (match conclude.Con.conclude_args with
         [Con.Term (_,t)] -> deannotate t
       | [Con.Premise prem] -> 
           (match prem.Con.premise_n with
              None -> assert false
            | Some n -> C.Rel n)
       | _ -> prerr_endline "3"; assert false)
    else if conclude.Con.conclude_method = "Intros+LetTac" then
      (match conclude.Con.conclude_args with
         [Con.ArgProof p] -> proof2cic [] p (* empty! *)
       | _ -> prerr_endline "4"; assert false)
    else if (conclude.Con.conclude_method = "ByInduction" ||
             conclude.Con.conclude_method = "AndInd" ||
             conclude.Con.conclude_method = "Exists" ||
             conclude.Con.conclude_method = "FalseInd") then
      (match (List.tl conclude.Con.conclude_args) with
         Con.Term (_,C.AAppl (
            id,((C.AConst(idc,uri,exp_named_subst))::params_and_IP)))::args ->
           let subst =
             List.map (fun (u,t) -> (u, deannotate t)) exp_named_subst in 
           let cargs = args2cic premise_env args in
           let cparams_and_IP = List.map deannotate params_and_IP in
           C.Appl (C.Const(uri,subst)::cparams_and_IP@cargs)
       | _ -> prerr_endline "5"; assert false)
    else if (conclude.Con.conclude_method = "Rewrite") then
      (match conclude.Con.conclude_args with
         Con.Term (_,C.AConst (sid,uri,exp_named_subst))::args ->
           let subst =
             List.map (fun (u,t) -> (u, deannotate t)) exp_named_subst in
           let  cargs = args2cic premise_env args in
           C.Appl (C.Const(uri,subst)::cargs)
       | _ -> prerr_endline "6"; assert false)
    else if (conclude.Con.conclude_method = "Case") then
      (match conclude.Con.conclude_args with
        Con.Aux(uri)::Con.Aux(notype)::Con.Term(_,ty)::Con.Premise(prem)::patterns ->
           C.MutCase
            (UriManager.uri_of_string uri,
             int_of_string notype, deannotate ty, 
             List.assoc prem.Con.premise_xref premise_env,
             List.map 
               (function 
                   Con.ArgProof p -> proof2cic [] p
                 | _ -> prerr_endline "7a"; assert false) patterns)
      | Con.Aux(uri)::Con.Aux(notype)::Con.Term(_,ty)::Con.Term(_,te)::patterns ->           C.MutCase
            (UriManager.uri_of_string uri,
             int_of_string notype, deannotate ty, deannotate te,
             List.map 
               (function 
                   (Con.ArgProof p) -> proof2cic [] p
                 | _ -> prerr_endline "7a"; assert false) patterns) 
      | _ -> (prerr_endline "7"; assert false))
    else if (conclude.Con.conclude_method = "Apply") then
      let cargs = (args2cic premise_env conclude.Con.conclude_args) in
      C.Appl cargs 
    else (prerr_endline "8"; assert false)

  and args2cic premise_env l =
    List.map (arg2cic premise_env) l

  and arg2cic premise_env =
    let module C = Cic in
    let module Con = Content in
    function
        Con.Aux n -> prerr_endline "8"; assert false
      | Con.Premise prem ->
          (match prem.Con.premise_n with
              Some n -> C.Rel n
            | None ->
              (try List.assoc prem.Con.premise_xref premise_env
               with Not_found -> 
                  prerr_endline ("Not_found in arg2cic: premise " ^ (match prem.Con.premise_binder with None -> "previous" | Some p -> p) ^ ", xref=" ^ prem.Con.premise_xref);
                  raise Not_found))
      | Con.Lemma lemma ->
         CicUtil.term_of_uri (UriManager.uri_of_string lemma.Con.lemma_uri)
      | Con.Term (_,t) -> deannotate t
      | Con.ArgProof p -> proof2cic [] p (* empty! *)
      | Con.ArgMethod s -> raise TO_DO

in proof2cic [] p
;;

exception ToDo;;

let cobj2obj deannotate (id,params,metasenv,obj) =
 let module K = Content in
 match obj with
    `Def (Content.Const,ty,`Proof bo) ->
      (match metasenv with
          None ->
           Cic.Constant
            (id, Some (proof2cic deannotate bo), deannotate ty, params, [])
        | Some metasenv' ->
           let metasenv'' =
            List.map
             (function (_,i,canonical_context,term) ->
               let canonical_context' =
                List.map
                 (function
                     None -> None
                   | Some (`Declaration d) 
                   | Some (`Hypothesis d) ->
                     (match d with
                        {K.dec_name = Some n ; K.dec_type = t} ->
                          Some (Cic.Name n, Cic.Decl (deannotate t))
                      | _ -> assert false)
                   | Some (`Definition d) ->
                      (match d with
                          {K.def_name = Some n ; K.def_term = t ; K.def_type = ty} ->
                            Some (Cic.Name n, Cic.Def (deannotate t,deannotate ty))
                        | _ -> assert false)
                   | Some (`Proof d) ->
                      (match d with
                          {K.proof_name = Some n } ->
                            Some (Cic.Name n,
                              Cic.Def ((proof2cic deannotate d),assert false))
                        | _ -> assert false)
                 ) canonical_context
               in
                (i,canonical_context',deannotate term)
             ) metasenv'
           in
            Cic.CurrentProof
             (id, metasenv'', proof2cic deannotate bo, deannotate ty, params,
              []))
  | _ -> raise ToDo
;;

let cobj2obj = cobj2obj Deannotate.deannotate_term;;
