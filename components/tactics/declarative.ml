(* Copyright (C) 2006, HELM Team.
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

type just = [ `Term of Cic.term | `Auto of Auto.auto_params ]

let mk_just ~dbd ~automation_cache =
 function
    `Auto (l,params) -> 
       Tactics.auto ~dbd 
       ~params:(l,("skip_trie_filtering","1")::(*("skip_context","1")::*)params) ~automation_cache
  | `Term t -> Tactics.apply t
;;

let assume id t =
  Tacticals.then_
     ~start:
       (Tactics.intros ~howmany:1
        ~mk_fresh_name_callback:(fun _ _ _ ~typ -> Cic.Name id) ())
     ~continuation:
       (Tactics.change ~pattern:(None,[id,Cic.Implicit (Some `Hole)],None)
         (fun _ metasenv ugraph -> t,metasenv,ugraph))
;;

let suppose t id ty =
(*BUG: check on t missing *)
 let ty = match ty with None -> t | Some ty -> ty in
 Tacticals.then_
   ~start:
     (Tactics.intros ~howmany:1
       ~mk_fresh_name_callback:(fun _ _ _ ~typ -> Cic.Name id) ())
   ~continuation:
     (Tactics.change ~pattern:(None,[id,Cic.Implicit (Some `Hole)],None)  
      (fun _ metasenv ugraph -> ty,metasenv,ugraph))
;;

let by_just_we_proved ~dbd ~automation_cache just ty id ty' =
 let just = mk_just ~dbd ~automation_cache just in
  match id with
     None ->
      (match ty' with
          None -> assert false
        | Some ty' ->
           Tacticals.then_
            ~start:(Tactics.change
              ~pattern:(ProofEngineTypes.conclusion_pattern None)
              (fun _ metasenv ugraph -> ty,metasenv,ugraph))
            ~continuation:just
      )
   | Some id ->
       let ty',continuation =
        match ty' with
           None -> ty,just
         | Some ty' ->
            ty',
            Tacticals.then_
             ~start:
               (Tactics.change
                 ~with_cast:true
                 ~pattern:(None,[id,Cic.Implicit (Some `Hole)],None)
                 (fun _ metasenv ugraph -> ty,metasenv,ugraph))
             ~continuation:just
       in
        Tacticals.thens
        ~start:
          (Tactics.cut ty'
            ~mk_fresh_name_callback:(fun _ _ _  ~typ -> Cic.Name id))
        ~continuations:[ Tacticals.id_tac ; continuation ]
;;

let bydone ~dbd ~automation_cache just =
 mk_just ~dbd ~automation_cache just
;;

let we_need_to_prove t id ty =
 match id with
    None ->
     (match ty with
         None -> Tacticals.id_tac (*BUG: check missing here *)
       | Some ty ->
          Tactics.change ~pattern:(ProofEngineTypes.conclusion_pattern None)
           (fun _ metasenv ugraph -> ty,metasenv,ugraph))
  | Some id ->
     let aux status =
      let cont,cutted =
       match ty with
          None -> Tacticals.id_tac,t
        | Some ty ->
           Tactics.change ~pattern:(None,[id,Cic.Implicit (Some `Hole)],None)
             (fun _ metasenv ugraph -> t,metasenv,ugraph), ty in
      let proof,goals =
       ProofEngineTypes.apply_tactic
        (Tacticals.thens
          ~start:
           (Tactics.cut cutted
             ~mk_fresh_name_callback:(fun _ _ _  ~typ -> Cic.Name id))
          ~continuations:[cont])
        status
      in
       let goals' =
        match goals with
           [fst; snd] -> [snd; fst]
         | _ -> assert false
       in
        proof,goals'
     in
      ProofEngineTypes.mk_tactic aux
;;

let existselim ~dbd ~automation_cache just id1 t1 id2 t2 =
 let aux (proof, goal) = 
  let (n,metasenv,_subst,bo,ty,attrs) = proof in
  let metano,context,_ = CicUtil.lookup_meta goal metasenv in
  let t2, metasenv, _ = t2 (Some (Cic.Name id1, Cic.Decl t1) :: context) metasenv CicUniv.oblivion_ugraph in
  let proof' = (n,metasenv,_subst,bo,ty,attrs) in
   ProofEngineTypes.apply_tactic (
   Tacticals.thens
    ~start:(Tactics.cut (Cic.Appl [Cic.MutInd (UriManager.uri_of_string "cic:/matita/logic/connectives/ex.ind", 0, []); t1 ; Cic.Lambda (Cic.Name id1, t1, t2)]))
    ~continuations:
     [ Tactics.elim_intros (Cic.Rel 1)
        ~mk_fresh_name_callback:
          (let i = ref 0 in
            fun _ _ _  ~typ ->
             incr i;
             if !i = 1 then Cic.Name id1 else Cic.Name id2) ;
       (mk_just ~dbd ~automation_cache just)
     ]) (proof', goal)
 in
  ProofEngineTypes.mk_tactic aux
;;

let andelim ~dbd ~automation_cache just id1 t1 id2 t2 = 
   Tacticals.thens
    ~start:(Tactics.cut (Cic.Appl [Cic.MutInd (UriManager.uri_of_string "cic:/matita/logic/connectives/And.ind", 0, []); t1 ; t2]))
    ~continuations:
     [ Tactics.elim_intros (Cic.Rel 1)
        ~mk_fresh_name_callback:
          (let i = ref 0 in
            fun _ _ _  ~typ ->
             incr i;
             if !i = 1 then Cic.Name id1 else Cic.Name id2) ;
       (mk_just ~dbd ~automation_cache just) ]
;;

let rewritingstep ~dbd ~automation_cache lhs rhs just last_step =
 let aux ((proof,goal) as status) =
  let (curi,metasenv,_subst,proofbo,proofty, attrs) = proof in
  let _,context,gty = CicUtil.lookup_meta goal metasenv in
  let eq,trans =
   match LibraryObjects.eq_URI () with
      None -> raise (ProofEngineTypes.Fail (lazy "You need to register the default equality first. Please use the \"default\" command"))
    | Some uri ->
      Cic.MutInd (uri,0,[]), Cic.Const (LibraryObjects.trans_eq_URI ~eq:uri,[])
  in
  let ty,_ =
   CicTypeChecker.type_of_aux' metasenv context rhs CicUniv.oblivion_ugraph in
  let just' =
   match just with
      `Auto (univ, params) ->
        let params =
         if not (List.exists (fun (k,_) -> k = "timeout") params) then
          ("timeout","3")::params
         else params
        in
        let params' =
         if not (List.exists (fun (k,_) -> k = "paramodulation") params) then
          ("paramodulation","1")::params
         else params
        in
         if params = params' then
          Tactics.auto ~dbd ~params:(univ, params) ~automation_cache
         else
          Tacticals.first
           [Tactics.auto ~dbd ~params:(univ, params) ~automation_cache ;
            Tactics.auto ~dbd ~params:(univ, params') ~automation_cache]
    | `Term just -> Tactics.apply just
    | `SolveWith term -> 
                    Tactics.demodulate ~automation_cache ~dbd
                    ~params:(Some [term],
                      ["all","1";"steps","1"; "use_context","false"])
    | `Proof ->
        Tacticals.id_tac
  in
   let plhs,prhs,prepare =
    match lhs with
       None ->
        let plhs,prhs =
         match gty with 
            Cic.Appl [_;_;plhs;prhs] -> plhs,prhs
          | _ -> assert false
        in
         plhs,prhs,
          (fun continuation ->
            ProofEngineTypes.apply_tactic continuation status)
     | Some (None,lhs) ->
        let plhs,prhs =
         match gty with 
            Cic.Appl [_;_;plhs;prhs] -> plhs,prhs
          | _ -> assert false
        in
         (*CSC: manca check plhs convertibile con lhs *)
         plhs,prhs,
          (fun continuation ->
            ProofEngineTypes.apply_tactic continuation status)
     | Some (Some name,lhs) ->
        let newmeta = CicMkImplicit.new_meta metasenv [] in
        let irl =
         CicMkImplicit.identity_relocation_list_for_metavariable context in
        let plhs = lhs in
        let prhs = Cic.Meta(newmeta,irl) in
         plhs,prhs,
          (fun continuation ->
            let metasenv = (newmeta, context, ty)::metasenv in
            let mk_fresh_name_callback =
             fun metasenv context _ ~typ ->
	      FreshNamesGenerator.mk_fresh_name ~subst:[] metasenv context
               (Cic.Name name) ~typ
	    in
            let proof = curi,metasenv,_subst,proofbo,proofty, attrs in
            let proof,goals =
             ProofEngineTypes.apply_tactic
              (Tacticals.thens
                ~start:(Tactics.cut ~mk_fresh_name_callback
                 (Cic.Appl [eq ; ty ; lhs ; prhs]))
                ~continuations:[Tacticals.id_tac ; continuation]) (proof,goal)
            in
             let goals =
              match just,goals with
                 `Proof, [g1;g2;g3] -> [g2;g3;newmeta;g1]
               | _, [g1;g2] -> [g2;newmeta;g1]
               | _, l -> 
                 prerr_endline (String.concat "," (List.map string_of_int l));
                 prerr_endline (CicMetaSubst.ppmetasenv [] metasenv);
                 assert false
             in
              proof,goals)
   in
    let continuation =
     if last_step then
      (*CSC:manca controllo sul fatto che rhs sia convertibile con prhs*)
      just'
     else
      Tacticals.thens
       ~start:(Tactics.apply ~term:(Cic.Appl [trans;ty;plhs;rhs;prhs]))
       ~continuations:[just' ; Tacticals.id_tac]
    in
     prepare continuation
 in
  ProofEngineTypes.mk_tactic aux
;;

let we_proceed_by_cases_on t pat =
 (*BUG here: pat unused *)
 Tactics.cases_intros t
;;

let we_proceed_by_induction_on t pat =
(*  let pattern = None, [], Some pat in *)
 Tactics.elim_intros ~depth:0 (*~pattern*) t
;;

let case id ~params =
 (*BUG here: id unused*)
 (*BUG here: it does not verify that the previous branch is closed *)
 (*BUG here: the params should be parsed telescopically*)
 (*BUG here: the tactic_terms should be terms*)
 let rec aux ~params ((proof,goal) as status) =
  match params with
     [] -> proof,[goal]
   | (id,t)::tl ->
      match ProofEngineTypes.apply_tactic (assume id t) status with
         proof,[goal] -> aux tl (proof,goal)
       | _ -> assert false
 in
  ProofEngineTypes.mk_tactic (aux ~params)
;;

let thesisbecomes t =
let ty = None in
 match ty with
    None ->
     Tactics.change ~pattern:(None,[],Some (Cic.Implicit (Some `Hole)))
      (fun _ metasenv ugraph -> t,metasenv,ugraph)
  | Some ty ->
     (*BUG here: missing check on t *)
     Tactics.change ~pattern:(None,[],Some (Cic.Implicit (Some `Hole)))
      (fun _ metasenv ugraph -> ty,metasenv,ugraph)
;;

let byinduction t id  = suppose t id None;;
