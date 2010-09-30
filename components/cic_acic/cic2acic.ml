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

type sort_kind = [ `Prop | `Set | `Type of CicUniv.universe | `CProp of CicUniv.universe | `NType of string | `NCProp of string]

let string_of_sort = function
  | `Prop -> "Prop"
  | `Set -> "Set"
  | `Type u -> "Type:" ^ string_of_int (CicUniv.univno u) ^ ":" ^ UriManager.string_of_uri (CicUniv.univuri u)
  | `NType s -> "Type[" ^ s ^ "]"
  | `NCProp s -> "CProp[" ^ s ^ "]"
  | `CProp u -> "CProp:" ^ string_of_int (CicUniv.univno u) ^ ":" ^ UriManager.string_of_uri (CicUniv.univuri u)


let sort_of_sort = function
  | Cic.Prop  -> `Prop
  | Cic.Set   -> `Set
  | Cic.Type u -> `Type u
  | Cic.CProp u -> `CProp u

(* let hashtbl_add_time = ref 0.0;; *)

let xxx_add_profiler = HExtlib.profile "xxx_add";;
let xxx_add h k v =
 xxx_add_profiler.HExtlib.profile (Hashtbl.add h k) v
;;

let xxx_type_of_aux' m c t =
 let res,_ =
   try
    CicTypeChecker.type_of_aux' m c t CicUniv.oblivion_ugraph
   with
   | CicTypeChecker.AssertFailure _
   | CicTypeChecker.TypeCheckerFailure _ ->
       Cic.Sort Cic.Prop, CicUniv.oblivion_ugraph
  in
 res
;;

let xxx_type_of_aux'_profiler = HExtlib.profile "xxx_type_of_aux'";;
let xxx_type_of_aux' m c t =
 xxx_type_of_aux'_profiler.HExtlib.profile (xxx_type_of_aux' m c) t

type anntypes =
 {annsynthesized : Cic.annterm ; annexpected : Cic.annterm option}
;;

let gen_id seed =
 let res = "i" ^ string_of_int !seed in
  incr seed ;
  res
;;

let fresh_id seed ids_to_terms ids_to_father_ids =
 fun father t ->
  let res = gen_id seed in
   xxx_add ids_to_father_ids res father ;
   xxx_add ids_to_terms res t ;
   res
;;

let source_id_of_id id = "#source#" ^ id;;

exception NotEnoughElements of string;;

(*CSC: cut&paste da cicPp.ml *)
(* get_nth l n   returns the nth element of the list l if it exists or *)
(* raises NotEnoughElements if l has less than n elements             *)
let rec get_nth msg l n =
 match (n,l) with
    (1, he::_) -> he
  | (n, he::tail) when n > 1 -> get_nth msg tail (n-1)
  | (_,_) -> raise (NotEnoughElements msg)
;;


let profiler_for_find = HExtlib.profile "CicHash" ;;
let profiler_for_whd = HExtlib.profile "whd" ;;

let cic_CicHash_find a b =  
  profiler_for_find.HExtlib.profile (Cic.CicHash.find a) b
;;

let cicReduction_whd c t = 
 profiler_for_whd.HExtlib.profile (CicReduction.whd c) t
;;

let acic_of_cic_context' ~computeinnertypes:global_computeinnertypes
  seed ids_to_terms ids_to_father_ids ids_to_inner_sorts ids_to_inner_types
  metasenv context idrefs t expectedty
=
 let module D = DoubleTypeInference in
 let module C = Cic in
  let fresh_id' = fresh_id seed ids_to_terms ids_to_father_ids in
(*    let time1 = Sys.time () in *)
   let terms_to_types =
(*
     let time0 = Sys.time () in
     let prova = CicTypeChecker.type_of_aux' metasenv context t in
     let time1 = Sys.time () in
     prerr_endline ("*** Fine type_inference:" ^ (string_of_float (time1 -. time0)));
     let res = D.double_type_of metasenv context t expectedty in
     let time2 = Sys.time () in
   prerr_endline ("*** Fine double_type_inference:" ^ (string_of_float (time2 -. time1)));
     res 
*)
    if global_computeinnertypes then
     D.double_type_of metasenv context t expectedty
    else
     Cic.CicHash.create 1 (* empty table *)
   in
(*
   let time2 = Sys.time () in
   prerr_endline
    ("++++++++++++ Tempi della double_type_of: "^ string_of_float (time2 -. time1)) ;
*)
    let rec aux computeinnertypes father context idrefs tt =
     let fresh_id'' = fresh_id' father tt in
     (*CSC: computeinnertypes era true, il che e' proprio sbagliato, no? *)
      (* First of all we compute the inner type and the inner sort *)
      (* of the term. They may be useful in what follows.          *)
      (*CSC: This is a very inefficient way of computing inner types *)
      (*CSC: and inner sorts: very deep terms have their types/sorts *)
      (*CSC: computed again and again.                               *)
      let sort_of t =
       match cicReduction_whd context t with 
          C.Sort C.Prop  -> `Prop
        | C.Sort C.Set   -> `Set
        | C.Sort (C.Type u) -> `Type u
        | C.Meta _       -> `Type (CicUniv.fresh())
        | C.Sort (C.CProp u) -> `CProp u
        | t              ->
            prerr_endline ("Cic2acic.sort_of applied to: " ^ CicPp.ppterm t) ;
            assert false
      in
       let ainnertypes,innertype,innersort,expected_available =

(*CSC: Here we need the algorithm for Coscoy's double type-inference  *)
(*CSC: (expected type + inferred type). Just for now we use the usual *)
(*CSC: type-inference, but the result is very poor. As a very weak    *)
(*CSC: patch, I apply whd to the computed type. Full beta             *)
(*CSC: reduction would be a much better option.                       *)
(*CSC: solo per testare i tempi *)
(*XXXXXXX *)
        try
(* *)
        let {D.synthesized = synthesized; D.expected = expected} =
         if computeinnertypes then
          cic_CicHash_find terms_to_types tt
         else
          (* We are already in an inner-type and Coscoy's double *)
          (* type inference algorithm has not been applied.      *)
          { D.synthesized =
(***CSC: patch per provare i tempi
            CicReduction.whd context (xxx_type_of_aux' metasenv context tt) ; *)
            (*if global_computeinnertypes then
              Cic.Sort (Cic.Type (CicUniv.fresh()))
            else*)
              cicReduction_whd context (xxx_type_of_aux' metasenv context tt);
          D.expected = None}
        in
(*          incr number_new_type_of_aux' ; *)
         let innersort = (*XXXXX *) xxx_type_of_aux' metasenv context synthesized (* Cic.Sort Cic.Prop *) in
          let ainnertypes,expected_available =
           if computeinnertypes then
            let annexpected,expected_available =
               match expected with
                  None -> None,false
                | Some expectedty' ->
                   Some
                    (aux false (Some fresh_id'') context idrefs expectedty'),
                    true
            in
             Some
              {annsynthesized =
                aux false (Some fresh_id'') context idrefs synthesized ;
               annexpected = annexpected
              }, expected_available
           else
            None,false
          in
           ainnertypes,synthesized, sort_of innersort, expected_available
(*XXXXXXXX *)
        with
         Not_found ->  (* l'inner-type non e' nella tabella ==> sort <> Prop *)
          (* CSC: Type or Set? I can not tell *)
          let u = CicUniv.fresh() in
          None,Cic.Sort (Cic.Type u),`Type u,false 
	  (* TASSI non dovrebbe fare danni *)
(* *)
       in
        let aux' =
         if innersort = `Prop then
          aux computeinnertypes (Some fresh_id'')
         else
          aux false (Some fresh_id'')
        in
        let add_inner_type id =
         match ainnertypes with
            None -> ()
          | Some ainnertypes -> xxx_add ids_to_inner_types id ainnertypes
        in
         match tt with
            C.Rel n ->
             let id =
              match get_nth "1" context n with
                 (Some (C.Name s,_)) -> s
               | _ -> "__" ^ string_of_int n
             in
              xxx_add ids_to_inner_sorts fresh_id'' innersort ;
              if innersort = `Prop  && expected_available then
               add_inner_type fresh_id'' ;
              C.ARel (fresh_id'', List.nth idrefs (n-1), n, id)
          | C.Var (uri,exp_named_subst) ->
             xxx_add ids_to_inner_sorts fresh_id'' innersort ;
             if innersort = `Prop  && expected_available then
              add_inner_type fresh_id'' ;
             let exp_named_subst' =
              List.map
               (function i,t -> i, (aux' context idrefs t)) exp_named_subst
             in
              C.AVar (fresh_id'', uri,exp_named_subst')
          | C.Meta (n,l) ->
             let (_,canonical_context,_) = CicUtil.lookup_meta n metasenv in
             xxx_add ids_to_inner_sorts fresh_id'' innersort ;
             if innersort = `Prop  && expected_available then
              add_inner_type fresh_id'' ;
             C.AMeta (fresh_id'', n,
              (List.map2
                (fun ct t ->
                  match (ct, t) with
                  | None, _ -> None
                  | _, Some t -> Some (aux' context idrefs t)
                  | Some _, None -> assert false (* due to typing rules *))
                canonical_context l))
          | C.Sort s -> C.ASort (fresh_id'', s)
          | C.Implicit annotation -> C.AImplicit (fresh_id'', annotation)
          | C.Cast (v,t) ->
             xxx_add ids_to_inner_sorts fresh_id'' innersort ;
             if innersort = `Prop then
              add_inner_type fresh_id'' ;
             C.ACast (fresh_id'', aux' context idrefs v, aux' context idrefs t)
          | C.Prod (n,s,t) ->
              xxx_add ids_to_inner_sorts fresh_id''
               (sort_of innertype) ;
	            let sourcetype = xxx_type_of_aux' metasenv context s in
	             xxx_add ids_to_inner_sorts (source_id_of_id fresh_id'')
	              (sort_of sourcetype) ;
              let n' =
               match n with
                  C.Anonymous -> n
                | C.Name n' ->
                   if DoubleTypeInference.does_not_occur 1 t then
                    C.Anonymous
                   else
                    C.Name n'
              in
               C.AProd
                (fresh_id'', n', aux' context idrefs s,
                 aux' ((Some (n, C.Decl s))::context) (fresh_id''::idrefs) t)
          | C.Lambda (n,s,t) ->
             xxx_add ids_to_inner_sorts fresh_id'' innersort ;
	           let sourcetype = xxx_type_of_aux' metasenv context s in
	            xxx_add ids_to_inner_sorts (source_id_of_id fresh_id'')
	             (sort_of sourcetype) ;
              if innersort = `Prop then
               begin
                let father_is_lambda =
                 match father with
                    None -> false
                  | Some father' ->
                     match Hashtbl.find ids_to_terms father' with
                        C.Lambda _ -> true
                      | _ -> false
                in
                 if (not father_is_lambda) || expected_available then
                  add_inner_type fresh_id''
               end ;
              C.ALambda
               (fresh_id'',n, aux' context idrefs s,
                aux' ((Some (n, C.Decl s)::context)) (fresh_id''::idrefs) t)
          | C.LetIn (n,s,ty,t) ->
              xxx_add ids_to_inner_sorts fresh_id'' innersort ;
              if innersort = `Prop then
               add_inner_type fresh_id'' ;
              C.ALetIn
               (fresh_id'', n, aux' context idrefs s, aux' context idrefs ty,
                aux' ((Some (n, C.Def(s,ty)))::context) (fresh_id''::idrefs) t)
          | C.Appl l ->
             xxx_add ids_to_inner_sorts fresh_id'' innersort ;
             if innersort = `Prop then
              add_inner_type fresh_id'' ;
             C.AAppl (fresh_id'', List.map (aux' context idrefs) l)
          | C.Const (uri,exp_named_subst) ->
             xxx_add ids_to_inner_sorts fresh_id'' innersort ;
             if innersort = `Prop  && expected_available then
              add_inner_type fresh_id'' ;
             let exp_named_subst' =
              List.map
               (function i,t -> i, (aux' context idrefs t)) exp_named_subst
             in
              C.AConst (fresh_id'', uri, exp_named_subst')
          | C.MutInd (uri,tyno,exp_named_subst) ->
             let exp_named_subst' =
              List.map
               (function i,t -> i, (aux' context idrefs t)) exp_named_subst
             in
              C.AMutInd (fresh_id'', uri, tyno, exp_named_subst')
          | C.MutConstruct (uri,tyno,consno,exp_named_subst) ->
             xxx_add ids_to_inner_sorts fresh_id'' innersort ;
             if innersort = `Prop  && expected_available then
              add_inner_type fresh_id'' ;
             let exp_named_subst' =
              List.map
               (function i,t -> i, (aux' context idrefs t)) exp_named_subst
             in
              C.AMutConstruct (fresh_id'', uri, tyno, consno, exp_named_subst')
          | C.MutCase (uri, tyno, outty, term, patterns) ->
             xxx_add ids_to_inner_sorts fresh_id'' innersort ;
             if innersort = `Prop then
              add_inner_type fresh_id'' ;
             C.AMutCase (fresh_id'', uri, tyno, aux' context idrefs outty,
              aux' context idrefs term, List.map (aux' context idrefs) patterns)
          | C.Fix (funno, funs) ->
             let fresh_idrefs =
              List.map (function _ -> gen_id seed) funs in
             let new_idrefs = List.rev fresh_idrefs @ idrefs in
             let tys,_ =
               List.fold_left
                 (fun (types,len) (n,_,ty,_) ->
                    (Some (C.Name n,(C.Decl (CicSubstitution.lift len ty)))::types,
                     len+1)
	         ) ([],0) funs
             in
              xxx_add ids_to_inner_sorts fresh_id'' innersort ;
              if innersort = `Prop then
               add_inner_type fresh_id'' ;
              C.AFix (fresh_id'', funno,
               List.map2
                (fun id (name, indidx, ty, bo) ->
                  (id, name, indidx, aux' context idrefs ty,
                    aux' (tys@context) new_idrefs bo)
                ) fresh_idrefs funs
             )
          | C.CoFix (funno, funs) ->
             let fresh_idrefs =
              List.map (function _ -> gen_id seed) funs in
             let new_idrefs = List.rev fresh_idrefs @ idrefs in
             let tys,_ =
               List.fold_left
                 (fun (types,len) (n,ty,_) ->
                    (Some (C.Name n,(C.Decl (CicSubstitution.lift len ty)))::types,
                     len+1)
	         ) ([],0) funs
             in
              xxx_add ids_to_inner_sorts fresh_id'' innersort ;
              if innersort = `Prop then
               add_inner_type fresh_id'' ;
              C.ACoFix (fresh_id'', funno,
               List.map2
                (fun id (name, ty, bo) ->
                  (id, name, aux' context idrefs ty,
                    aux' (tys@context) new_idrefs bo)
                ) fresh_idrefs funs
              )
        in
(*
         let timea = Sys.time () in
         let res = aux true None context idrefs t in
         let timeb = Sys.time () in
          prerr_endline
           ("+++++++++++++ Tempi della aux dentro alla acic_of_cic: "^ string_of_float (timeb -. timea)) ;
          res
*)
  aux global_computeinnertypes None context idrefs t
;;

let acic_of_cic_context ~computeinnertypes metasenv context idrefs t =
 let ids_to_terms = Hashtbl.create 503 in
 let ids_to_father_ids = Hashtbl.create 503 in
 let ids_to_inner_sorts = Hashtbl.create 503 in
 let ids_to_inner_types = Hashtbl.create 503 in
 let seed = ref 0 in
   acic_of_cic_context' ~computeinnertypes seed ids_to_terms ids_to_father_ids ids_to_inner_sorts
    ids_to_inner_types metasenv context idrefs t,
   ids_to_terms, ids_to_father_ids, ids_to_inner_sorts, ids_to_inner_types
;;

let aconjecture_of_conjecture seed ids_to_terms ids_to_father_ids 
  ids_to_inner_sorts ids_to_inner_types ids_to_hypotheses hypotheses_seed
  metasenv (metano,context,goal)
= 
  let computeinnertypes = false in
  let acic_of_cic_context =
    acic_of_cic_context' seed ids_to_terms ids_to_father_ids ids_to_inner_sorts
      ids_to_inner_types  metasenv in
  let _, acontext,final_idrefs =
    (List.fold_right
      (fun binding (context, acontext,idrefs) ->
         let hid = "h" ^ string_of_int !hypotheses_seed in
           Hashtbl.add ids_to_hypotheses hid binding ;
           incr hypotheses_seed ;
           match binding with
               Some (n,Cic.Def (t,ty)) ->
                 let acic =
                  acic_of_cic_context ~computeinnertypes context idrefs t
                   None in
                 let acic2 =
                  acic_of_cic_context ~computeinnertypes context idrefs ty
                   None
                 in
                  Hashtbl.replace ids_to_father_ids (CicUtil.id_of_annterm acic)
                   (Some hid);
                  Hashtbl.replace ids_to_father_ids
                   (CicUtil.id_of_annterm acic2) (Some hid);
                  (binding::context),
                    ((hid,Some (n,Cic.ADef (acic,acic2)))::acontext),
                    (hid::idrefs)
             | Some (n,Cic.Decl t) ->
                 let acic = acic_of_cic_context ~computeinnertypes context idrefs t None in
                 Hashtbl.replace ids_to_father_ids (CicUtil.id_of_annterm acic)
                  (Some hid);
                 (binding::context),
                   ((hid,Some (n,Cic.ADecl acic))::acontext),(hid::idrefs)
             | None ->
                 (* Invariant: "" is never looked up *)
                  (None::context),((hid,None)::acontext),""::idrefs
         ) context ([],[],[])
       )
  in 
  let agoal = acic_of_cic_context ~computeinnertypes context final_idrefs goal None in
  (metano,acontext,agoal)
;;

let asequent_of_sequent (metasenv:Cic.metasenv) (sequent:Cic.conjecture) = 
    let ids_to_terms = Hashtbl.create 503 in
    let ids_to_father_ids = Hashtbl.create 503 in
    let ids_to_inner_sorts = Hashtbl.create 503 in
    let ids_to_inner_types = Hashtbl.create 503 in
    let ids_to_hypotheses = Hashtbl.create 23 in
    let hypotheses_seed = ref 0 in
    let seed = ref 1 in (* 'i0' is used for the whole sequent *)
    let unsh_sequent =
     let i,canonical_context,term = sequent in
      let canonical_context' =
       List.fold_right
        (fun d canonical_context' ->
          let d =
           match d with
              None -> None
            | Some (n, Cic.Decl t)->
               Some (n, Cic.Decl (Unshare.unshare t))
            | Some (n,Cic.Def (bo,ty)) ->
               Some (n, Cic.Def (Unshare.unshare bo,Unshare.unshare ty))
          in
           d::canonical_context'
        ) canonical_context []
      in
      let term' = Unshare.unshare term in
       (i,canonical_context',term')
    in
    let (metano,acontext,agoal) = 
      aconjecture_of_conjecture seed ids_to_terms ids_to_father_ids 
      ids_to_inner_sorts ids_to_inner_types ids_to_hypotheses hypotheses_seed
      metasenv unsh_sequent in
    (unsh_sequent,
     (("i0",metano,acontext,agoal), 
      ids_to_terms,ids_to_father_ids,ids_to_inner_sorts,ids_to_hypotheses))
;;

let acic_term_or_object_of_cic_term_or_object ?(eta_fix=false) () =
 let module C = Cic in
 let module E = Eta_fixing in
  let ids_to_terms = Hashtbl.create 503 in
  let ids_to_father_ids = Hashtbl.create 503 in
  let ids_to_inner_sorts = Hashtbl.create 503 in
  let ids_to_inner_types = Hashtbl.create 503 in
  let ids_to_conjectures = Hashtbl.create 11 in
  let ids_to_hypotheses = Hashtbl.create 127 in
  let hypotheses_seed = ref 0 in
  let conjectures_seed = ref 0 in
  let seed = ref 0 in
  let acic_term_of_cic_term_context' =
   acic_of_cic_context' seed ids_to_terms ids_to_father_ids ids_to_inner_sorts
    ids_to_inner_types in
  let acic_term_of_cic_term' = acic_term_of_cic_term_context' [] [] [] in
  let aconjecture_of_conjecture' = aconjecture_of_conjecture seed 
    ids_to_terms ids_to_father_ids ids_to_inner_sorts ids_to_inner_types 
    ids_to_hypotheses hypotheses_seed in 
   let eta_fix_and_unshare metasenv context t =
    let t = if eta_fix then E.eta_fix metasenv context t else t in
     Unshare.unshare t in
   (fun context t ->
     let map = function
        | None                     -> None
	| Some (n, C.Decl ty)      -> Some (n, C.Decl (Unshare.unshare ty))
        | Some (n, C.Def (bo, ty)) ->
	    Some (n, C.Def (Unshare.unshare bo, Unshare.unshare ty))
     in
     let t = Unshare.unshare t in
     let context = List.map map context in
     let idrefs = List.map (function _ -> gen_id seed) context in
     let t = acic_term_of_cic_term_context' ~computeinnertypes:true [] context idrefs t None in
     t, ids_to_inner_sorts, ids_to_inner_types
   ),(function obj ->
   let aobj =
    match obj with
      C.Constant (id,Some bo,ty,params,attrs) ->
       let bo' = (*eta_fix_and_unshare[] [] bo*) Unshare.unshare bo in
       let ty' = eta_fix_and_unshare [] [] ty in
       let abo = acic_term_of_cic_term' ~computeinnertypes:true bo' (Some ty') in
       let aty = acic_term_of_cic_term' ~computeinnertypes:false ty' None in
        C.AConstant
         ("mettereaposto",Some "mettereaposto2",id,Some abo,aty,params,attrs)
    | C.Constant (id,None,ty,params,attrs) ->
       let ty' = eta_fix_and_unshare [] [] ty in
       let aty = acic_term_of_cic_term' ~computeinnertypes:false ty' None in
        C.AConstant
         ("mettereaposto",None,id,None,aty,params,attrs)
    | C.Variable (id,bo,ty,params,attrs) ->
       let ty' = eta_fix_and_unshare [] [] ty in
       let abo =
        match bo with
           None -> None
         | Some bo ->
            let bo' = eta_fix_and_unshare [] [] bo in
             Some (acic_term_of_cic_term' ~computeinnertypes:true bo' (Some ty'))
       in
       let aty = acic_term_of_cic_term' ~computeinnertypes:false ty' None in
        C.AVariable
         ("mettereaposto",id,abo,aty,params,attrs)
    | C.CurrentProof (id,conjectures,bo,ty,params,attrs) ->
       let conjectures' =
        List.map
         (function (i,canonical_context,term) ->
           let canonical_context' =
            List.fold_right
             (fun d canonical_context' ->
               let d =
                match d with
                   None -> None
                 | Some (n, C.Decl t)->
                    Some (n, C.Decl (eta_fix_and_unshare conjectures canonical_context' t))
                 | Some (n, C.Def (t,ty)) ->
                    Some (n,
                     C.Def
                      (eta_fix_and_unshare conjectures canonical_context' t,
                       eta_fix_and_unshare conjectures canonical_context' ty))
               in
                d::canonical_context'
             ) canonical_context []
           in
           let term' = eta_fix_and_unshare conjectures canonical_context' term in
            (i,canonical_context',term')
         ) conjectures
       in
       let aconjectures = 
        List.map
         (function (i,canonical_context,term) as conjecture ->
           let cid = "c" ^ string_of_int !conjectures_seed in
            xxx_add ids_to_conjectures cid conjecture ;
            incr conjectures_seed ;
           let (i,acanonical_context,aterm) 
             = aconjecture_of_conjecture' conjectures conjecture in
           (cid,i,acanonical_context,aterm))
          conjectures' in 
       (* let bo' = eta_fix conjectures' [] bo in *)
       let bo' = bo in
       let ty' = eta_fix_and_unshare conjectures' [] ty in
(*
       let time2 = Sys.time () in
       prerr_endline
        ("++++++++++ Tempi della eta_fix: "^ string_of_float (time2 -. time1)) ;
       hashtbl_add_time := 0.0 ;
       type_of_aux'_add_time := 0.0 ;
       DoubleTypeInference.syntactic_equality_add_time := 0.0 ;
*)
       let abo =
        acic_term_of_cic_term_context' ~computeinnertypes:true conjectures' [] [] bo' (Some ty') in
       let aty = acic_term_of_cic_term_context' ~computeinnertypes:false conjectures' [] [] ty' None in
(*
       let time3 = Sys.time () in
       prerr_endline
        ("++++++++++++ Tempi della hashtbl_add_time: " ^ string_of_float !hashtbl_add_time) ;
       prerr_endline
        ("++++++++++++ Tempi della type_of_aux'_add_time(" ^ string_of_int !number_new_type_of_aux' ^ "): " ^ string_of_float !type_of_aux'_add_time) ;
       prerr_endline
        ("++++++++++++ Tempi della type_of_aux'_add_time nella double_type_inference(" ^ string_of_int !DoubleTypeInference.number_new_type_of_aux'_double_work ^ ";" ^ string_of_int !DoubleTypeInference.number_new_type_of_aux'_prop ^ "/" ^ string_of_int !DoubleTypeInference.number_new_type_of_aux' ^ "): " ^ string_of_float !DoubleTypeInference.type_of_aux'_add_time) ;
       prerr_endline
        ("++++++++++++ Tempi della syntactic_equality_add_time: " ^ string_of_float !DoubleTypeInference.syntactic_equality_add_time) ;
       prerr_endline
        ("++++++++++ Tempi della acic_of_cic: " ^ string_of_float (time3 -. time2)) ;
       prerr_endline
        ("++++++++++ Numero di iterazioni della acic_of_cic: " ^ string_of_int !seed) ;
*)
        C.ACurrentProof
         ("mettereaposto","mettereaposto2",id,aconjectures,abo,aty,params,attrs)
    | C.InductiveDefinition (tys,params,paramsno,attrs) ->
       let tys =
        List.map
         (fun (name,i,arity,cl) ->
           (name,i,Unshare.unshare arity,
             List.map (fun (name,ty) -> name,Unshare.unshare ty) cl)) tys in
       let context =
        List.map
         (fun (name,_,arity,_) ->
           Some (C.Name name, C.Decl (Unshare.unshare arity))) tys in
       let idrefs = List.map (function _ -> gen_id seed) tys in
       let atys =
        List.map2
         (fun id (name,inductive,ty,cons) ->
           let acons =
            List.map
             (function (name,ty) ->
               (name,
                 acic_term_of_cic_term_context' ~computeinnertypes:false [] context idrefs ty None)
             ) cons
           in
            (id,name,inductive,
             acic_term_of_cic_term' ~computeinnertypes:false ty None,acons)
         ) (List.rev idrefs) tys
       in
        C.AInductiveDefinition ("mettereaposto",atys,params,paramsno,attrs)
   in
    aobj,ids_to_terms,ids_to_father_ids,ids_to_inner_sorts,ids_to_inner_types,
     ids_to_conjectures,ids_to_hypotheses
);;

let acic_object_of_cic_object ?eta_fix =
   snd (acic_term_or_object_of_cic_term_or_object ?eta_fix ()) 

let plain_acic_term_of_cic_term =
 let module C = Cic in
 let mk_fresh_id =
  let id = ref 0 in
   function () -> incr id; "i" ^ string_of_int !id in
 let rec aux context t =
  let fresh_id = mk_fresh_id () in
  match t with
     C.Rel n ->
      let idref,id =
       match get_nth "2" context n with
          idref,(Some (C.Name s,_)) -> idref,s
        | idref,_ -> idref,"__" ^ string_of_int n
      in
       C.ARel (fresh_id, idref, n, id)
   | C.Var (uri,exp_named_subst) ->
      let exp_named_subst' =
       List.map
        (function i,t -> i, (aux context t)) exp_named_subst
      in
       C.AVar (fresh_id,uri,exp_named_subst')
   | C.Implicit _
   | C.Meta _ -> assert false
   | C.Sort s -> C.ASort (fresh_id, s)
   | C.Cast (v,t) ->
      C.ACast (fresh_id, aux context v, aux context t)
   | C.Prod (n,s,t) ->
        C.AProd
         (fresh_id, n, aux context s,
          aux ((fresh_id, Some (n, C.Decl s))::context) t)
   | C.Lambda (n,s,t) ->
       C.ALambda
        (fresh_id,n, aux context s,
         aux ((fresh_id, Some (n, C.Decl s))::context) t)
   | C.LetIn (n,s,ty,t) ->
      C.ALetIn
       (fresh_id, n, aux context s, aux context ty,
        aux ((fresh_id, Some (n, C.Def(s,ty)))::context) t)
   | C.Appl l ->
      C.AAppl (fresh_id, List.map (aux context) l)
   | C.Const (uri,exp_named_subst) ->
      let exp_named_subst' =
       List.map
        (function i,t -> i, (aux context t)) exp_named_subst
      in
       C.AConst (fresh_id, uri, exp_named_subst')
   | C.MutInd (uri,tyno,exp_named_subst) ->
      let exp_named_subst' =
       List.map
        (function i,t -> i, (aux context t)) exp_named_subst
      in
       C.AMutInd (fresh_id, uri, tyno, exp_named_subst')
   | C.MutConstruct (uri,tyno,consno,exp_named_subst) ->
      let exp_named_subst' =
       List.map
        (function i,t -> i, (aux context t)) exp_named_subst
      in
       C.AMutConstruct (fresh_id, uri, tyno, consno, exp_named_subst')
   | C.MutCase (uri, tyno, outty, term, patterns) ->
      C.AMutCase (fresh_id, uri, tyno, aux context outty,
       aux context term, List.map (aux context) patterns)
   | C.Fix (funno, funs) ->
      let tys,_ =
        List.fold_left
          (fun (types,len) (n,_,ty,_) ->
            (mk_fresh_id (),(Some (C.Name n,(C.Decl (CicSubstitution.lift len ty)))))::types,
              len+1
	  ) ([],0) funs
      in
       C.AFix (fresh_id, funno,
        List.map2
         (fun (id,_) (name, indidx, ty, bo) ->
           (id, name, indidx, aux context ty, aux (tys@context) bo)
         ) tys funs
      )
   | C.CoFix (funno, funs) ->
      let tys,_ =
        List.fold_left
          (fun (types,len) (n,ty,_) ->
            (mk_fresh_id (),(Some (C.Name n,(C.Decl (CicSubstitution.lift len ty)))))::types,
              len+1
	  ) ([],0) funs
      in
       C.ACoFix (fresh_id, funno,
        List.map2
         (fun (id,_) (name, ty, bo) ->
           (id, name, aux context ty, aux (tys@context) bo)
         ) tys funs
       )
 in
  aux
;;

let plain_acic_object_of_cic_object obj =
 let module C = Cic in
 let mk_fresh_id =
  let id = ref 0 in
   function () -> incr id; "it" ^ string_of_int !id
 in
  match obj with
    C.Constant (id,Some bo,ty,params,attrs) ->
     let abo = plain_acic_term_of_cic_term [] bo in
     let aty = plain_acic_term_of_cic_term [] ty in
      C.AConstant
       ("mettereaposto",Some "mettereaposto2",id,Some abo,aty,params,attrs)
  | C.Constant (id,None,ty,params,attrs) ->
     let aty = plain_acic_term_of_cic_term [] ty in
      C.AConstant
       ("mettereaposto",None,id,None,aty,params,attrs)
  | C.Variable (id,bo,ty,params,attrs) ->
     let abo =
      match bo with
         None -> None
       | Some bo -> Some (plain_acic_term_of_cic_term [] bo)
     in
     let aty = plain_acic_term_of_cic_term [] ty in
      C.AVariable
       ("mettereaposto",id,abo,aty,params,attrs)
  | C.CurrentProof _ -> assert false
  | C.InductiveDefinition (tys,params,paramsno,attrs) ->
     let context =
      List.map
       (fun (name,_,arity,_) ->
         mk_fresh_id (), Some (C.Name name, C.Decl arity)) tys in
     let atys =
      List.map2
       (fun (id,_) (name,inductive,ty,cons) ->
         let acons =
          List.map
           (function (name,ty) ->
             (name,
               plain_acic_term_of_cic_term context ty)
           ) cons
         in
          (id,name,inductive,plain_acic_term_of_cic_term [] ty,acons)
       ) context tys
     in
      C.AInductiveDefinition ("mettereaposto",atys,params,paramsno,attrs)
;;

let acic_term_of_cic_term ?eta_fix =
   fst (acic_term_or_object_of_cic_term_or_object ?eta_fix ()) 
