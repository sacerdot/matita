(* Copyright (C) 2005, HELM Team.
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
 * http://helm.cs.unibo.it/
 *)

let debug = false;;
let debug_print = 
  if not debug then (fun _ -> ()) else (fun s -> prerr_endline (Lazy.force s))
;;

let rec count_pi = function Cic.Prod (_,_,t) -> count_pi t + 1 | _ -> 0 ;;

let compose_core t2 t1 (proof, goal) =
  let _,metasenv,_subst,_,_,_ = proof in
  let _,context,_ = CicUtil.lookup_meta goal metasenv in
  let ty1,_ = 
    CicTypeChecker.type_of_aux' metasenv context t1 CicUniv.oblivion_ugraph 
  in
  let ty2,_ = 
    CicTypeChecker.type_of_aux' metasenv context t2 CicUniv.oblivion_ugraph 
  in
  let saturated_ty2, menv_for_saturated_ty2, args_t2 = 
    let maxm = CicMkImplicit.new_meta metasenv [] in
    let ty2, menv, args, _ = 
      TermUtil.saturate_term ~delta:false maxm metasenv context ty2 0 in
    ty2, menv, args
  in
  let saturations_t2 = 
    let rec aux n = function 
      | Cic.Meta (i,_)::tl -> 
          let _,c,ty = CicUtil.lookup_meta i menv_for_saturated_ty2 in
          if fst (CicReduction.are_convertible c ty (Cic.Sort Cic.Prop)
            CicUniv.oblivion_ugraph) 
          then n else aux (n+1) tl
      | _::tl -> aux (n+1) tl
      | [] -> n+1
    in
      List.length args_t2 - aux 0 args_t2 +1
  in
  debug_print (lazy("saturated_ty2: "^CicMetaSubst.ppterm_in_context
    [] ~metasenv:menv_for_saturated_ty2 saturated_ty2 context ^
    " saturations_t2:" ^ string_of_int saturations_t2));
  (* unifies t with saturated_ty2 and gives back a fresh meta of type t *)
  let unif menv t = 
    let m, menv2 =
      let n = CicMkImplicit.new_meta menv [] in
      let irl = 
        CicMkImplicit.identity_relocation_list_for_metavariable context
      in
      Cic.Meta (n,irl), ((n,context,t)::menv)
    in
    try 
      let _ = 
        CicUnification.fo_unif menv context t saturated_ty2
          CicUniv.oblivion_ugraph
      in 
        true, menv2, m
    with
    | CicUnification.UnificationFailure _
    | CicUnification.Uncertain _ -> false, menv2, m
  in
  (* check which "positions" in the input arrow unifies with saturated_ty2 *)
  let rec positions menv cur saturations = function 
    | Cic.Prod (n,s,t) -> 
        let b, newmenv, sb = unif menv s in
        if b then
          (saturations - cur - 1) :: 
            (positions newmenv (cur + 1) saturations 
             (CicSubstitution.subst sb t))
        else
          positions newmenv (cur + 1) saturations (CicSubstitution.subst sb t)
    | _ -> []
  in
  (* position is a list of arities, that is if t1 : a -> b -> c and saturations
   * is 0 then the computed term will be (t1 ? t2) of type a -> c if saturations
   * is 1 then (t1 t2 ?) of type b -> c *)
  let rec generate positions menv acc =
    match positions with
    | [] -> acc, menv
    | saturations_t1::tl ->
      try
        let t, menv1, _ =
          CloseCoercionGraph.generate_composite t2 t1 context menv
            CicUniv.oblivion_ugraph saturations_t2 saturations_t1
        in
        assert (List.length menv1 = List.length menv);
        generate tl menv (t::acc)
      with 
      | CloseCoercionGraph.UnableToCompose -> generate tl menv acc
  in
  let terms, metasenv =
    generate (positions menv_for_saturated_ty2 0 (count_pi ty1) ty1) metasenv []
  in
  (* the new proof has the resulting metasenv (shouldn't it be the same?) *)
  let proof = 
    let uri, _, _subst, bo, ty, attrs = proof in
    uri, metasenv, _subst, bo, ty, attrs
  in
  (* now we have the terms, we generalize them and intros them *)
  let proof, goal =
    List.fold_left 
      (fun (proof,goal) t ->
        let lazy_of t =
          ProofEngineTypes.const_lazy_term t
        in
        let proof, gl = 
          ProofEngineTypes.apply_tactic
            (PrimitiveTactics.generalize_tac (Some (lazy_of t), [], None))
            (proof,goal)
        in
        assert(List.length gl = 1);
        proof,List.hd gl)
      (proof,goal) terms
  in
  (proof, goal), List.length terms
;;

let compose_tac ?howmany ?mk_fresh_name_callback n t1 t2 proofstatus =
  let ((proof, goal), k), n = 
    match t2 with
    | Some t2 -> compose_core t1 t2 proofstatus, n-1
    | None -> 
        let k = 
          let proof, goal = proofstatus in
          let _,metasenv,subst,_,_,_ = proof in
          let _,_,ty = CicUtil.lookup_meta goal metasenv in
          count_pi (CicMetaSubst.apply_subst subst ty)
        in
        (proofstatus, k), n
  in
  let (proof, goal), k = 
    (* fix iterates n times the composition *)
    let rec fix proofstatus k t = function
      | 0 -> proofstatus, k
      | n ->
          let t = CicSubstitution.lift k t in
          let proof, gl =  
            ProofEngineTypes.apply_tactic 
              (PrimitiveTactics.intros_tac 
                ~howmany:k ?mk_fresh_name_callback ()) proofstatus
          in
          assert (List.length gl = 1);
          let goal = List.hd gl in
          let k, proofstatus =
            (* aux compose t with every previous result *)
            let rec aux k proofstatus = function
              | 0 -> k, proofstatus
              | n -> 
                 let (proof, goal), k1 = 
                   compose_core t (Cic.Rel n) proofstatus 
                 in
                 aux (k+k1) (proof, goal) (n-1)
            in
              aux 0 (proof, goal) k
          in
          fix proofstatus k t (n-1)
    in
      fix (proof, goal) k t1 n
  in
  let howmany = 
    match howmany with
    | None -> None
    | Some i ->
        if i - k < 0 then (* we should generalize back and clear *) Some 0
        else Some (i - k)
  in
     ProofEngineTypes.apply_tactic 
      (PrimitiveTactics.intros_tac ?howmany ?mk_fresh_name_callback ())
      (proof,goal)
;;

let compose_tac ?howmany ?mk_fresh_name_callback times t1 t2 =
  ProofEngineTypes.mk_tactic 
    (compose_tac ?howmany ?mk_fresh_name_callback times t1 t2)
;;
