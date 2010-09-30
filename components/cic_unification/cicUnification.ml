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

open Printf

exception UnificationFailure of string Lazy.t;;
exception Uncertain of string Lazy.t;;
exception AssertFailure of string Lazy.t;;

let verbose = false;;
let debug_print = fun _ -> () 

let profiler_toa = HExtlib.profile "fo_unif_subst.type_of_aux'"
let profiler_beta_expand = HExtlib.profile "fo_unif_subst.beta_expand"
let profiler_deref = HExtlib.profile "fo_unif_subst.deref'"
let profiler_are_convertible = HExtlib.profile "fo_unif_subst.are_convertible"

let profile = HExtlib.profile "U/CicTypeChecker.type_of_aux'"

let type_of_aux' metasenv subst context term ugraph =
let foo () =
  try 
    profile.HExtlib.profile
      (CicTypeChecker.type_of_aux' ~subst metasenv context term) ugraph 
  with
      CicTypeChecker.TypeCheckerFailure msg ->
        let msg =
         lazy
          (sprintf
           "Kernel Type checking error: 
%s\n%s\ncontext=\n%s\nmetasenv=\n%s\nsubstitution=\n%s\nException:\n%s.\nToo bad."
             (CicMetaSubst.ppterm ~metasenv subst term)
             (CicMetaSubst.ppterm ~metasenv [] term)
             (CicMetaSubst.ppcontext ~metasenv subst context)
             (CicMetaSubst.ppmetasenv subst metasenv) 
             (CicMetaSubst.ppsubst ~metasenv subst) (Lazy.force msg)) in
        raise (AssertFailure msg)
    | CicTypeChecker.AssertFailure msg ->
        let msg = lazy
         (sprintf
           "Kernel Type checking assertion failure: 
%s\n%s\ncontext=\n%s\nmetasenv=\n%s\nsubstitution=\n%s\nException:\n%s.\nToo bad."
             (CicMetaSubst.ppterm ~metasenv subst term)
             (CicMetaSubst.ppterm ~metasenv [] term)
             (CicMetaSubst.ppcontext ~metasenv subst context)
             (CicMetaSubst.ppmetasenv subst metasenv) 
             (CicMetaSubst.ppsubst ~metasenv subst) (Lazy.force msg)) in
        raise (AssertFailure msg)
in profiler_toa.HExtlib.profile foo ()
;;

let exists_a_meta l = 
  List.exists 
    (function 
       | Cic.Meta _  
       | Cic.Appl (Cic.Meta _::_) -> true
       | _ -> false) l

let rec deref subst t =
  let snd (_,a,_) = a in
  match t with
      Cic.Meta(n,l) -> 
        (try 
           deref subst
             (CicSubstitution.subst_meta 
                l (snd (CicUtil.lookup_subst n subst))) 
         with 
             CicUtil.Subst_not_found _ -> t)
    | Cic.Appl(Cic.Meta(n,l)::args) ->
        (match deref subst (Cic.Meta(n,l)) with
           | Cic.Lambda _ as t -> 
               deref subst (CicReduction.head_beta_reduce (Cic.Appl(t::args)))
           | r -> Cic.Appl(r::args))
    | Cic.Appl(((Cic.Lambda _) as t)::args) ->
           deref subst (CicReduction.head_beta_reduce (Cic.Appl(t::args)))
    | t -> t
;; 

let deref subst t =
 let foo () = deref subst t
 in profiler_deref.HExtlib.profile foo ()

exception WrongShape;;
let eta_reduce after_beta_expansion after_beta_expansion_body
     before_beta_expansion
 =
 try
  match before_beta_expansion,after_beta_expansion_body with
     Cic.Appl l, Cic.Appl l' ->
      let rec all_but_last check_last =
       function
          [] -> assert false
        | [Cic.Rel 1] -> []
        | [_] -> if check_last then raise WrongShape else []
        | he::tl -> he::(all_but_last check_last tl)
      in
       let all_but_last check_last l =
        match all_but_last check_last l with
           [] -> assert false
         | [he] -> he
         | l -> Cic.Appl l
       in
       let t = CicSubstitution.subst (Cic.Rel (-1)) (all_but_last true l') in
       let all_but_last = all_but_last false l in
        (* here we should test alpha-equivalence; however we know by
           construction that here alpha_equivalence is equivalent to = *)
        if t = all_but_last then
         all_but_last
        else
         after_beta_expansion
   | _,_ -> after_beta_expansion
 with
  WrongShape -> after_beta_expansion

let rec beta_expand num test_equality_only metasenv subst context t arg ugraph =
 let module S = CicSubstitution in
 let module C = Cic in
let foo () =
  let rec aux metasenv subst n context t' ugraph =
   try

    let subst,metasenv,ugraph1 =
     fo_unif_subst test_equality_only subst context metasenv 
      (CicSubstitution.lift n arg) t' ugraph

    in
     subst,metasenv,C.Rel (1 + n),ugraph1
   with
      Uncertain _
    | UnificationFailure _ ->
       match t' with
        | C.Rel m  -> subst,metasenv, 
           (if m <= n then C.Rel m else C.Rel (m+1)),ugraph
        | C.Var (uri,exp_named_subst) ->
           let subst,metasenv,exp_named_subst',ugraph1 =
            aux_exp_named_subst metasenv subst n context exp_named_subst ugraph
           in
            subst,metasenv,C.Var (uri,exp_named_subst'),ugraph1
        | C.Meta (i,l) ->
            (* andrea: in general, beta_expand can create badly typed
             terms. This happens quite seldom in practice, UNLESS we
             iterate on the local context. For this reason, we renounce
             to iterate and just lift *)
            let l = 
              List.map 
                (function
                     Some t -> Some (CicSubstitution.lift 1 t)
                   | None -> None) l in
            subst, metasenv, C.Meta (i,l), ugraph
        | C.Sort _
        | C.Implicit _ as t -> subst,metasenv,t,ugraph
        | C.Cast (te,ty) ->
            let subst,metasenv,te',ugraph1 = 
              aux metasenv subst n context te ugraph in
            let subst,metasenv,ty',ugraph2 = 
              aux metasenv subst n context ty ugraph1 in 
            (* TASSI: sure this is in serial? *)
            subst,metasenv,(C.Cast (te', ty')),ugraph2
        | C.Prod (nn,s,t) ->
           let subst,metasenv,s',ugraph1 = 
             aux metasenv subst n context s ugraph in
           let subst,metasenv,t',ugraph2 =
             aux metasenv subst (n+1) ((Some (nn, C.Decl s))::context) t 
               ugraph1
           in
           (* TASSI: sure this is in serial? *)
           subst,metasenv,(C.Prod (nn, s', t')),ugraph2
        | C.Lambda (nn,s,t) ->
           let subst,metasenv,s',ugraph1 = 
             aux metasenv subst n context s ugraph in
           let subst,metasenv,t',ugraph2 =
            aux metasenv subst (n+1) ((Some (nn, C.Decl s))::context) t ugraph1
           in
           (* TASSI: sure this is in serial? *)
            subst,metasenv,(C.Lambda (nn, s', t')),ugraph2
        | C.LetIn (nn,s,ty,t) ->
           let subst,metasenv,s',ugraph1 = 
             aux metasenv subst n context s ugraph in
           let subst,metasenv,ty',ugraph1 = 
             aux metasenv subst n context ty ugraph in
           let subst,metasenv,t',ugraph2 =
            aux metasenv subst (n+1) ((Some (nn, C.Def (s,ty)))::context) t
              ugraph1
           in
           (* TASSI: sure this is in serial? *)
            subst,metasenv,(C.LetIn (nn, s', ty', t')),ugraph2
        | C.Appl l ->
           let subst,metasenv,revl',ugraph1 =
            List.fold_left
             (fun (subst,metasenv,appl,ugraph) t ->
               let subst,metasenv,t',ugraph1 = 
                 aux metasenv subst n context t ugraph in
                subst,metasenv,(t'::appl),ugraph1
             ) (subst,metasenv,[],ugraph) l
           in
            subst,metasenv,(C.Appl (List.rev revl')),ugraph1
        | C.Const (uri,exp_named_subst) ->
           let subst,metasenv,exp_named_subst',ugraph1 =
            aux_exp_named_subst metasenv subst n context exp_named_subst ugraph
           in
            subst,metasenv,(C.Const (uri,exp_named_subst')),ugraph1
        | C.MutInd (uri,i,exp_named_subst) ->
           let subst,metasenv,exp_named_subst',ugraph1 =
            aux_exp_named_subst metasenv subst n context exp_named_subst ugraph
           in
            subst,metasenv,(C.MutInd (uri,i,exp_named_subst')),ugraph1
        | C.MutConstruct (uri,i,j,exp_named_subst) ->
           let subst,metasenv,exp_named_subst',ugraph1 =
            aux_exp_named_subst metasenv subst n context exp_named_subst ugraph
           in
            subst,metasenv,(C.MutConstruct (uri,i,j,exp_named_subst')),ugraph1
        | C.MutCase (sp,i,outt,t,pl) ->
           let subst,metasenv,outt',ugraph1 = 
             aux metasenv subst n context outt ugraph in
           let subst,metasenv,t',ugraph2 = 
             aux metasenv subst n context t ugraph1 in
           let subst,metasenv,revpl',ugraph3 =
            List.fold_left
             (fun (subst,metasenv,pl,ugraph) t ->
               let subst,metasenv,t',ugraph1 = 
                 aux metasenv subst n context t ugraph in
               subst,metasenv,(t'::pl),ugraph1
             ) (subst,metasenv,[],ugraph2) pl
           in
           subst,metasenv,(C.MutCase (sp,i,outt', t', List.rev revpl')),ugraph3
           (* TASSI: not sure this is serial *)
        | C.Fix (i,fl) ->
(*CSC: not implemented
           let tylen = List.length fl in
            let substitutedfl =
             List.map
              (fun (name,i,ty,bo) -> (name, i, aux n ty, aux (n+tylen) bo))
               fl
            in
             C.Fix (i, substitutedfl)
*)
            subst,metasenv,(CicSubstitution.lift 1 t' ),ugraph
        | C.CoFix (i,fl) ->
(*CSC: not implemented
           let tylen = List.length fl in
            let substitutedfl =
             List.map
              (fun (name,ty,bo) -> (name, aux n ty, aux (n+tylen) bo))
               fl
            in
             C.CoFix (i, substitutedfl)

*) 
            subst,metasenv,(CicSubstitution.lift 1 t'), ugraph

  and aux_exp_named_subst metasenv subst n context ens ugraph =
   List.fold_right
    (fun (uri,t) (subst,metasenv,l,ugraph) ->
      let subst,metasenv,t',ugraph1 = aux metasenv subst n context t ugraph in
       subst,metasenv,((uri,t')::l),ugraph1) ens (subst,metasenv,[],ugraph)
  in
  let argty,ugraph1 = type_of_aux' metasenv subst context arg ugraph in
  let fresh_name =
   FreshNamesGenerator.mk_fresh_name ~subst
    metasenv context (Cic.Name ("Hbeta" ^ string_of_int num)) ~typ:argty
  in
   let subst,metasenv,t',ugraph2 = aux metasenv subst 0 context t ugraph1 in
   let t'' = eta_reduce (C.Lambda (fresh_name,argty,t')) t' t in
   subst, metasenv, t'', ugraph2
in profiler_beta_expand.HExtlib.profile foo ()


and beta_expand_many test_equality_only metasenv subst context t args ugraph =
  let _,subst,metasenv,hd,ugraph =
    List.fold_right
      (fun arg (num,subst,metasenv,t,ugraph) ->
         let subst,metasenv,t,ugraph1 =
           beta_expand num test_equality_only 
             metasenv subst context t arg ugraph 
         in
           num+1,subst,metasenv,t,ugraph1 
      ) args (1,subst,metasenv,t,ugraph) 
  in
    subst,metasenv,hd,ugraph

and warn_if_not_unique xxx car1 car2 =
  let unopt = 
    function 
    | Some (_,Cic.Appl(Cic.Const(u,_)::_)) -> UriManager.string_of_uri u 
    | Some (_,t) -> CicPp.ppterm t 
    | None -> "id"
  in
  match xxx with
  | [] -> ()
  | _ -> 
     HLog.warn 
       ("There are "^string_of_int (List.length xxx + 1)^
        " minimal joins of "^ CoercDb.string_of_carr car1^" and "^
       CoercDb.string_of_carr car2^": " ^
     String.concat " and "
       (List.map 
          (fun (m2,_,c2,c2') ->
          " via "^CoercDb.string_of_carr m2^" via "^unopt c2^" + "^unopt c2')
          xxx))

(* NUOVA UNIFICAZIONE *)
(* A substitution is a (int * Cic.term) list that associates a
   metavariable i with its body.
   A metaenv is a (int * Cic.term) list that associate a metavariable
   i with is type. 
   fo_unif_new takes a metasenv, a context, two terms t1 and t2 and gives back
   a new substitution which is _NOT_ unwinded. It must be unwinded before
   applying it. *)

and fo_unif_subst test_equality_only subst context metasenv t1 t2 ugraph =  
 let module C = Cic in
 let module R = CicReduction in
 let module S = CicSubstitution in
 let t1 = deref subst t1 in
 let t2 = deref subst t2 in
 let (&&&) a b = (a && b) || ((not a) && (not b)) in
(* let bef = Sys.time () in *)
 let b,ugraph =
  if not (CicUtil.is_meta_closed (CicMetaSubst.apply_subst subst t1) &&& CicUtil.is_meta_closed (CicMetaSubst.apply_subst subst t2)) then
   false,ugraph
  else
let foo () =
   R.are_convertible ~subst ~metasenv context t1 t2 ugraph 
in profiler_are_convertible.HExtlib.profile foo ()
 in
(* let aft = Sys.time () in
if (aft -. bef > 2.0) then prerr_endline ("LEEEENTO: " ^
CicMetaSubst.ppterm_in_context subst ~metasenv t1 context ^ " <===> " ^
CicMetaSubst.ppterm_in_context subst ~metasenv t2 context); *)
   if b then
     subst, metasenv, ugraph 
   else
   match (t1, t2) with
     | (C.Meta (n,ln), C.Meta (m,lm)) when n=m ->
         let _,subst,metasenv,ugraph1 =
           (try
              List.fold_left2
                (fun (j,subst,metasenv,ugraph) t1 t2 ->
                   match t1,t2 with
                       None,_
                     | _,None -> j+1,subst,metasenv,ugraph
                     | Some t1', Some t2' ->
                         (* First possibility:  restriction    *)
                         (* Second possibility: unification    *)
                         (* Third possibility:  convertibility *)
                         let b, ugraph1 = 
                         R.are_convertible 
                           ~subst ~metasenv context t1' t2' ugraph
                         in
                         if b then
                           j+1,subst,metasenv, ugraph1 
                         else
                           (try
                              let subst,metasenv,ugraph2 =
                                fo_unif_subst 
                                  test_equality_only 
                                  subst context metasenv t1' t2' ugraph
                              in
                                j+1,subst,metasenv,ugraph2
                            with
                                Uncertain _
                              | UnificationFailure _ ->
debug_print (lazy ("restringo Meta n." ^ (string_of_int n) ^ "on variable n." ^ (string_of_int j))); 
                                  let metasenv, subst = 
                                    CicMetaSubst.restrict 
                                      subst [(n,j)] metasenv in
                                    j+1,subst,metasenv,ugraph1)
                ) (1,subst,metasenv,ugraph) ln lm
            with
                Exit ->
                  raise 
                    (UnificationFailure (lazy "1"))
                    (*
                    (sprintf
                      "Error trying to unify %s with %s: the algorithm tried to check whether the two substitutions are convertible; if they are not, it tried to unify the two substitutions. No restriction was attempted."
                      (CicMetaSubst.ppterm ~metasenv subst t1) 
                      (CicMetaSubst.ppterm ~metasenv subst t2))) *)
              | Invalid_argument _ ->
                  raise 
                    (UnificationFailure (lazy "2")))
                    (*
                    (sprintf
                      "Error trying to unify %s with %s: the lengths of the two local contexts do not match." 
                      (CicMetaSubst.ppterm ~metasenv subst t1) 
                      (CicMetaSubst.ppterm ~metasenv subst t2)))) *)
         in subst,metasenv,ugraph1
     | (C.Meta (n,_), C.Meta (m,_)) when n>m ->
         fo_unif_subst test_equality_only subst context metasenv t2 t1 ugraph
     | (C.Meta (n,l), t)   
     | (t, C.Meta (n,l)) ->
         let swap =
           match t1,t2 with
               C.Meta (n,_), C.Meta (m,_) when n < m -> false
             | _, C.Meta _ -> false
             | _,_ -> true
         in
         let lower = fun x y -> if swap then y else x in
         let upper = fun x y -> if swap then x else y in
         let fo_unif_subst_ordered 
             test_equality_only subst context metasenv m1 m2 ugraph =
           fo_unif_subst test_equality_only subst context metasenv 
             (lower m1 m2) (upper m1 m2) ugraph
         in
         begin
         let subst,metasenv,ugraph1 = 
           let (_,_,meta_type) =  CicUtil.lookup_meta n metasenv in
           (try
              let tyt,ugraph1 = 
                type_of_aux' metasenv subst context t ugraph 
              in
                fo_unif_subst 
                  test_equality_only 
                  subst context metasenv tyt (S.subst_meta l meta_type) ugraph1
            with 
                UnificationFailure _ as e -> raise e
              | Uncertain msg -> raise (UnificationFailure msg)
              | AssertFailure _ ->
                  debug_print (lazy "siamo allo huge hack");
                  (* TODO huge hack!!!!
                   * we keep on unifying/refining in the hope that 
                   * the problem will be eventually solved. 
                   * In the meantime we're breaking a big invariant:
                   * the terms that we are unifying are no longer well 
                   * typed in the current context (in the worst case 
                   * we could even diverge) *)
                  (subst, metasenv,ugraph)) in
         let t',metasenv,subst =
           try 
             CicMetaSubst.delift n subst context metasenv l t
           with
               (CicMetaSubst.MetaSubstFailure msg)-> 
                 raise (UnificationFailure msg)
             | (CicMetaSubst.Uncertain msg) -> raise (Uncertain msg)
         in
         let t'',ugraph2 =
           match t' with
               C.Sort (C.Type u) when not test_equality_only ->
                 let u' = CicUniv.fresh () in
                 let s = C.Sort (C.Type u') in
                  (try
                    let ugraph2 =   
                     CicUniv.add_ge (upper u u') (lower u u') ugraph1
                    in
                     s,ugraph2
                   with
                    CicUniv.UniverseInconsistency msg ->
                     raise (UnificationFailure msg))
             | _ -> t',ugraph1
         in
         (* Unifying the types may have already instantiated n. Let's check *)
         try
           let (_, oldt,_) = CicUtil.lookup_subst n subst in
           let lifted_oldt = S.subst_meta l oldt in
             fo_unif_subst_ordered 
               test_equality_only subst context metasenv t lifted_oldt ugraph2
         with
             CicUtil.Subst_not_found _ -> 
               let (_, context, ty) = CicUtil.lookup_meta n metasenv in
               let subst = (n, (context, t'',ty)) :: subst in
               let metasenv =
                 List.filter (fun (m,_,_) -> not (n = m)) metasenv in
               subst, metasenv, ugraph2
         end
   | (C.Var (uri1,exp_named_subst1),C.Var (uri2,exp_named_subst2))
   | (C.Const (uri1,exp_named_subst1),C.Const (uri2,exp_named_subst2)) ->
      if UriManager.eq uri1 uri2 then
       fo_unif_subst_exp_named_subst test_equality_only subst context metasenv
        exp_named_subst1 exp_named_subst2 ugraph
      else
       raise (UnificationFailure (lazy 
          (sprintf
            "Can't unify %s with %s due to different constants"
            (CicMetaSubst.ppterm ~metasenv subst t1) 
            (CicMetaSubst.ppterm ~metasenv subst t2))))
   | C.MutInd (uri1,i1,exp_named_subst1),C.MutInd (uri2,i2,exp_named_subst2) ->
       if UriManager.eq uri1 uri2 && i1 = i2 then
         fo_unif_subst_exp_named_subst 
           test_equality_only 
           subst context metasenv exp_named_subst1 exp_named_subst2 ugraph
       else
         raise (UnificationFailure
           (lazy
            (sprintf
             "Can't unify %s with %s due to different inductive principles"
             (CicMetaSubst.ppterm ~metasenv subst t1) 
             (CicMetaSubst.ppterm ~metasenv subst t2))))
   | C.MutConstruct (uri1,i1,j1,exp_named_subst1),
       C.MutConstruct (uri2,i2,j2,exp_named_subst2) ->
       if UriManager.eq uri1 uri2 && i1 = i2 && j1 = j2 then
         fo_unif_subst_exp_named_subst
           test_equality_only 
           subst context metasenv exp_named_subst1 exp_named_subst2 ugraph
       else
         raise (UnificationFailure
          (lazy
            (sprintf
              "Can't unify %s with %s due to different inductive constructors"
              (CicMetaSubst.ppterm ~metasenv subst t1) 
              (CicMetaSubst.ppterm ~metasenv subst t2))))
   | (C.Implicit _, _) | (_, C.Implicit _) ->  assert false
   | (C.Cast (te,ty), t2) -> fo_unif_subst test_equality_only 
                              subst context metasenv te t2 ugraph
   | (t1, C.Cast (te,ty)) -> fo_unif_subst test_equality_only 
                              subst context metasenv t1 te ugraph
   | (C.Lambda (n1,s1,t1), C.Lambda (_,s2,t2)) -> 
       let subst',metasenv',ugraph1 = 
         fo_unif_subst test_equality_only subst context metasenv s1 s2 ugraph 
       in
         fo_unif_subst test_equality_only 
           subst' ((Some (n1,(C.Decl s1)))::context) metasenv' t1 t2 ugraph1
   | (C.LetIn (_,s1,ty1,t1), t2)  
   | (t2, C.LetIn (_,s1,ty1,t1)) -> 
       fo_unif_subst 
        test_equality_only subst context metasenv t2 (S.subst s1 t1) ugraph
   | (C.Appl l1, C.Appl l2) -> 
       (* andrea: this case should be probably rewritten in the 
          spirit of deref *)
       (match l1,l2 with
          | C.Meta (i,_)::args1, C.Meta (j,_)::args2 when i = j ->
              (try 
                 List.fold_left2 
                   (fun (subst,metasenv,ugraph) t1 t2 ->
                      fo_unif_subst 
                        test_equality_only subst context metasenv t1 t2 ugraph)
                   (subst,metasenv,ugraph) l1 l2 
               with (Invalid_argument msg) -> 
                 raise (UnificationFailure (lazy msg)))
          | C.Meta (i,l)::args, _ when not(exists_a_meta args) ->
              (* we verify that none of the args is a Meta, 
                since beta expanding with respoect to a metavariable 
                makes no sense  *)
 (*
              (try 
                 let (_,t,_) = CicUtil.lookup_subst i subst in
                 let lifted = S.subst_meta l t in
                 let reduced = CicReduction.head_beta_reduce (Cic.Appl (lifted::args)) in
                   fo_unif_subst 
                    test_equality_only 
                     subst context metasenv reduced t2 ugraph
               with CicUtil.Subst_not_found _ -> *)
              let subst,metasenv,beta_expanded,ugraph1 =
                beta_expand_many 
                  test_equality_only metasenv subst context t2 args ugraph 
              in
                fo_unif_subst test_equality_only subst context metasenv 
                  (C.Meta (i,l)) beta_expanded ugraph1
          | _, C.Meta (i,l)::args when not(exists_a_meta args)  ->
              (* (try 
                 let (_,t,_) = CicUtil.lookup_subst i subst in
                 let lifted = S.subst_meta l t in
                 let reduced = CicReduction.head_beta_reduce (Cic.Appl (lifted::args)) in
                   fo_unif_subst 
                     test_equality_only 
                     subst context metasenv t1 reduced ugraph
               with CicUtil.Subst_not_found _ -> *)
                 let subst,metasenv,beta_expanded,ugraph1 =
                   beta_expand_many 
                     test_equality_only 
                     metasenv subst context t1 args ugraph 
                 in
                   fo_unif_subst test_equality_only subst context metasenv 
                     (C.Meta (i,l)) beta_expanded ugraph1
          | _,_ ->
              let lr1 = List.rev l1 in
              let lr2 = List.rev l2 in
              let rec 
                  fo_unif_l test_equality_only subst metasenv (l1,l2) ugraph =
                match (l1,l2) with
                    [],_
                  | _,[] -> assert false
                  | ([h1],[h2]) ->
                      fo_unif_subst 
                        test_equality_only subst context metasenv h1 h2 ugraph
                  | ([h],l) 
                  | (l,[h]) ->
                      fo_unif_subst test_equality_only subst context metasenv
                        h (C.Appl (List.rev l)) ugraph
                  | ((h1::l1),(h2::l2)) -> 
                      let subst', metasenv',ugraph1 = 
                        fo_unif_subst 
                          test_equality_only 
                          subst context metasenv h1 h2 ugraph
                      in 
                        fo_unif_l 
                          test_equality_only subst' metasenv' (l1,l2) ugraph1
              in
              (try 
                fo_unif_l 
                  test_equality_only subst metasenv (lr1, lr2)  ugraph
              with 
              | UnificationFailure s
              | Uncertain s as exn -> 
                  (match l1, l2 with
                            (* {{{ pullback *)
                  | (((Cic.Const (uri1, ens1)) as cc1) :: tl1), 
                     (((Cic.Const (uri2, ens2)) as cc2) :: tl2) when
                    CoercDb.is_a_coercion cc1 <> None && 
                    CoercDb.is_a_coercion cc2 <> None &&
                    not (UriManager.eq uri1 uri2) ->
(*DEBUGGING ONLY:
prerr_endline ("<<<< " ^ CicMetaSubst.ppterm_in_context ~metasenv subst (C.Appl l1) context ^ " <==> " ^ CicMetaSubst.ppterm_in_context ~metasenv subst (C.Appl l2) context);
*)
                     let inner_coerced ?(skip_non_c=false) t =
                      let t = CicMetaSubst.apply_subst subst t in
                      let rec aux c x t =
                        match t with
                        | Cic.Appl l -> 
                            (match CoercGraph.coerced_arg l with
                            | None when skip_non_c -> 
                                aux c (HExtlib.list_last l)            
                                 (HExtlib.list_last l)            
                            | None -> c, x
                            | Some (t,_) -> aux (List.hd l) t t)
                        | _ ->  c, x
                      in
                      aux (Cic.Implicit None) (Cic.Implicit None) t
                     in
                      let c1,last_tl1 = inner_coerced (Cic.Appl l1) in 
                      let c2,last_tl2 = inner_coerced (Cic.Appl l2) in
                      let car1, car2 =
                        match 
                          CoercDb.is_a_coercion c1, CoercDb.is_a_coercion c2
                        with
                        | Some (s1,_,_,_,_), Some (s2,_,_,_,_) -> s1, s2
                        | _ -> assert false
                      in
                      let head1_c, head2_c =
                        match 
                          CoercDb.is_a_coercion cc1, CoercDb.is_a_coercion cc2
                        with
                        | Some (_,t1,_,_,_), Some (_,t2,_,_,_) -> t1, t2
                        | _ -> assert false
                      in
                      let unfold uri ens args =
                        let o, _ = 
                          CicEnvironment.get_obj CicUniv.oblivion_ugraph uri 
                        in
                        assert (ens = []);
                        match o with
                        | Cic.Constant (_,Some bo,_,_,_) -> 
                            CicReduction.head_beta_reduce ~delta:false
                              (Cic.Appl (bo::args))
                        | _ -> assert false
                      in
                      let conclude subst metasenv ugraph last_tl1' last_tl2' =
                       let subst',metasenv,ugraph =
(*DEBUGGING ONLY:
prerr_endline 
  ("conclude: " ^ CicMetaSubst.ppterm_in_context ~metasenv subst last_tl1' context ^ 
   " <==> " ^ CicMetaSubst.ppterm_in_context ~metasenv subst last_tl2' context);
*)
                        fo_unif_subst test_equality_only subst context
                         metasenv last_tl1' last_tl2' ugraph
                       in
                       if subst = subst' then raise exn 
                       else
(*DEBUGGING ONLY: 
let subst,metasenv,ugrph as res = 
*)
                        fo_unif_subst test_equality_only subst' context
                         metasenv (C.Appl l1) (C.Appl l2) ugraph
(*DEBUGGING ONLY: 
in
(prerr_endline 
  ("OK: "^CicMetaSubst.ppterm_in_context ~metasenv subst (C.Appl l1) context ^
   " <==> "^CicMetaSubst.ppterm_in_context ~metasenv subst (C.Appl l2) context);
res)
*)
                      in
(*DEBUGGING ONLY: 
prerr_endline (Printf.sprintf 
"Pullback problem\nterm1: %s\nterm2: %s\ncar1: %s\ncar2: %s\nlast_tl1: %s
last_tl2: %s\nhead1_c: %s\nhead2_c: %s\n"
(CicMetaSubst.ppterm_in_context ~metasenv subst (C.Appl l1) context)
(CicMetaSubst.ppterm_in_context ~metasenv subst (C.Appl l2) context)
(CoercDb.string_of_carr car1)
(CoercDb.string_of_carr car2)
(CicMetaSubst.ppterm_in_context ~metasenv subst last_tl1 context)
(CicMetaSubst.ppterm_in_context ~metasenv subst last_tl2 context)
(CoercDb.string_of_carr head1_c)
(CoercDb.string_of_carr head2_c)
);
*)
                      if CoercDb.eq_carr car1 car2 then
                         match last_tl1,last_tl2 with
                         | C.Meta (i1,_),C.Meta(i2,_) when i1 = i2 -> raise exn
                         | _, C.Meta _
                         | C.Meta _, _ ->
                           let subst,metasenv,ugraph =
                            fo_unif_subst test_equality_only subst context
                             metasenv last_tl1 last_tl2 ugraph
                           in
                            fo_unif_subst test_equality_only subst context
                             metasenv (Cic.Appl l1) (Cic.Appl l2) ugraph
                         | _ when CoercDb.eq_carr head1_c head2_c ->
                             (* composite VS composition + metas avoiding
                              * coercions not only in coerced position    *)
                             if c1 <> cc1 && c2 <> cc2 then
                               conclude subst metasenv ugraph
                                last_tl1 last_tl2
                             else
                              let l1, l2 = 
                               if c1 = cc1 then 
                                 unfold uri1 ens1 tl1, Cic.Appl (cc2::tl2)
                               else
                                 Cic.Appl (cc1::tl1), unfold uri2 ens2 tl2
                              in
                               fo_unif_subst test_equality_only subst context
                                metasenv l1 l2 ugraph
                         | _ -> raise exn
                      else
                      let grow1 =
                        match last_tl1 with Cic.Meta _ -> true | _ -> false in
                      let grow2 =
                        match last_tl2 with Cic.Meta _ -> true | _ -> false in
                      if not (grow1 || grow2) then
                        let _,last_tl1 = 
                          inner_coerced ~skip_non_c:true (Cic.Appl l1) in 
                        let _,last_tl2 = 
                          inner_coerced ~skip_non_c:true  (Cic.Appl l2) in
                        conclude subst metasenv ugraph last_tl1 last_tl2
                      else
                        let meets = 
                           CoercGraph.meets 
                            metasenv subst context (grow1,car1) (grow2,car2)
                        in
                        (match
                        HExtlib.list_findopt
                          (fun (carr,metasenv,to1,to2) meet_no ->
                             try
                           let last_tl1',(subst,metasenv,ugraph) =
                            match grow1,to1 with
                             | true,Some (last,coerced) -> 
                                 last,
                                  fo_unif_subst test_equality_only subst context
                                  metasenv coerced last_tl1 ugraph
                             | _ -> last_tl1,(subst,metasenv,ugraph)
                           in
                           let last_tl2',(subst,metasenv,ugraph) =
                            match grow2,to2 with
                             | true,Some (last,coerced) -> 
                                 last,
                                  fo_unif_subst test_equality_only subst context
                                  metasenv coerced last_tl2 ugraph
                             | _ -> last_tl2,(subst,metasenv,ugraph)
                           in
                           if meet_no > 0 then
                             HLog.warn ("Using pullback number " ^ string_of_int
                               meet_no);
                           Some 
                            (conclude subst metasenv ugraph last_tl1' last_tl2')
                             with
                             | UnificationFailure _ 
                             | Uncertain _ -> None)
                          meets
                        with
                        | Some x -> x
                        | None -> raise exn)
                        (* }}} pullback *)
                  (* {{{ CSC: This is necessary because of the "elim H" tactic
                         where the type of H is only reducible to an
                         inductive type. This could be extended from inductive
                         types to any rigid term. However, the code is
                         duplicated in two places: inside applications and
                         outside them. Probably it would be better to
                         work with lambda-bar terms instead. *)
                  | (Cic.MutInd _::_, Cic.MutInd _::_) -> raise exn
                  | (_, Cic.MutInd _::_) ->
                     let t1' = R.whd ~subst context t1 in
                     (match t1' with
                          C.Appl (C.MutInd _::_) -> 
                            fo_unif_subst test_equality_only 
                              subst context metasenv t1' t2 ugraph         
                        | _ -> raise (UnificationFailure (lazy "88")))
                  | (Cic.MutInd _::_,_) ->
                     let t2' = R.whd ~subst context t2 in
                     (match t2' with
                          C.Appl (C.MutInd _::_) -> 
                            fo_unif_subst test_equality_only 
                              subst context metasenv t1 t2' ugraph         
                        | _ -> raise 
			    (UnificationFailure 
			       (lazy ("not a mutind :"^
                                CicMetaSubst.ppterm ~metasenv subst t2 ))))
                     (* }}} elim H *)
                  | _ -> raise exn)))
   | (C.MutCase (_,_,outt1,t1',pl1), C.MutCase (_,_,outt2,t2',pl2))->
       let subst', metasenv',ugraph1 = 
        fo_unif_subst test_equality_only subst context metasenv outt1 outt2
          ugraph in
       let subst'',metasenv'',ugraph2 = 
        fo_unif_subst test_equality_only subst' context metasenv' t1' t2'
          ugraph1 in
       (try
         List.fold_left2 
          (fun (subst,metasenv,ugraph) t1 t2 ->
            fo_unif_subst 
             test_equality_only subst context metasenv t1 t2 ugraph
          ) (subst'',metasenv'',ugraph2) pl1 pl2 
        with
         Invalid_argument _ ->
          raise (UnificationFailure (lazy "6.1")))
           (* (sprintf
              "Error trying to unify %s with %s: the number of branches is not the same." 
              (CicMetaSubst.ppterm ~metasenv subst t1) 
              (CicMetaSubst.ppterm ~metasenv subst t2)))) *)
   | (C.Rel _, _) | (_,  C.Rel _) ->
       if t1 = t2 then
         subst, metasenv,ugraph
       else
        raise (UnificationFailure (lazy 
           (sprintf
             "Can't unify %s with %s because they are not convertible"
             (CicMetaSubst.ppterm ~metasenv subst t1) 
             (CicMetaSubst.ppterm ~metasenv subst t2))))
   | (C.Appl (C.Meta(i,l)::args),t2) when not(exists_a_meta args) ->
       let subst,metasenv,beta_expanded,ugraph1 =
         beta_expand_many 
           test_equality_only metasenv subst context t2 args ugraph 
       in
         fo_unif_subst test_equality_only subst context metasenv 
           (C.Meta (i,l)) beta_expanded ugraph1
   | (t1,C.Appl (C.Meta(i,l)::args)) when not(exists_a_meta args) ->
       let subst,metasenv,beta_expanded,ugraph1 =
         beta_expand_many 
           test_equality_only metasenv subst context t1 args ugraph 
       in
         fo_unif_subst test_equality_only subst context metasenv 
           beta_expanded (C.Meta (i,l)) ugraph1
(* Works iff there are no arguments applied to it; similar to the
   case below
   | (_, C.MutInd _) ->
       let t1' = R.whd ~subst context t1 in
       (match t1' with
            C.MutInd _ -> 
              fo_unif_subst test_equality_only 
                subst context metasenv t1' t2 ugraph         
          | _ -> raise (UnificationFailure (lazy "8")))
*)
   | (C.Prod (n1,s1,t1), C.Prod (_,s2,t2)) -> 
       let subst',metasenv',ugraph1 = 
         fo_unif_subst true subst context metasenv s1 s2 ugraph 
       in
         fo_unif_subst test_equality_only 
           subst' ((Some (n1,(C.Decl s1)))::context) metasenv' t1 t2 ugraph1
   | (C.Prod _, _) ->
       (match CicReduction.whd ~subst context t2 with
        | C.Prod _ as t2 -> 
            fo_unif_subst test_equality_only subst context metasenv t1 t2 ugraph
        | _ -> raise (UnificationFailure (lazy (CicMetaSubst.ppterm ~metasenv subst t2^"Not a product"))))
   | (_, C.Prod _) ->
       (match CicReduction.whd ~subst context t1 with
        | C.Prod _ as t1 -> 
            fo_unif_subst test_equality_only subst context metasenv t1 t2 ugraph
        | _ -> raise (UnificationFailure (lazy (CicMetaSubst.ppterm ~metasenv subst t1^"Not a product"))))
   | (_,_) ->
     (* delta-beta reduction should almost never be a problem for
        unification since:
         1. long computations require iota reduction
         2. it is extremely rare that a close term t1 (that could be unified
            to t2) beta-delta reduces to t1' while t2 does not beta-delta
            reduces in the same way. This happens only if one meta of t2
            occurs in head position during beta reduction. In this unluky
            case too much reduction will be performed on t1 and unification
            will surely fail. *)
     let t1' = CicReduction.head_beta_reduce ~delta:true t1 in
     let t2' = CicReduction.head_beta_reduce ~delta:true t2 in
      if t1 = t1' && t2 = t2' then
       raise (UnificationFailure
        (lazy 
          (sprintf
            "Can't unify %s with %s because they are not convertible"
            (CicMetaSubst.ppterm ~metasenv subst t1) 
            (CicMetaSubst.ppterm ~metasenv subst t2))))
      else
       try
        fo_unif_subst test_equality_only subst context metasenv t1' t2' ugraph
       with
          UnificationFailure _
        | Uncertain _ ->
           raise (UnificationFailure
            (lazy 
              (sprintf
                "Can't unify %s with %s because they are not convertible"
                (CicMetaSubst.ppterm ~metasenv subst t1) 
                (CicMetaSubst.ppterm ~metasenv subst t2))))

and fo_unif_subst_exp_named_subst test_equality_only subst context metasenv
 exp_named_subst1 exp_named_subst2 ugraph
=
 try
  List.fold_left2
   (fun (subst,metasenv,ugraph) (uri1,t1) (uri2,t2) ->
     assert (uri1=uri2) ;
     fo_unif_subst test_equality_only subst context metasenv t1 t2 ugraph
   ) (subst,metasenv,ugraph) exp_named_subst1 exp_named_subst2
 with
  Invalid_argument _ ->
   let print_ens ens =
    String.concat " ; "
     (List.map
       (fun (uri,t) ->
         UriManager.string_of_uri uri ^ " := " ^ (CicMetaSubst.ppterm ~metasenv subst t)
       ) ens) 
   in
    raise (UnificationFailure (lazy (sprintf
     "Error trying to unify the two explicit named substitutions (local contexts) %s and %s: their lengths is different." (print_ens exp_named_subst1) (print_ens exp_named_subst2))))

(* A substitution is a (int * Cic.term) list that associates a               *)
(* metavariable i with its body.                                             *)
(* metasenv is of type Cic.metasenv                                          *)
(* fo_unif takes a metasenv, a context, two terms t1 and t2 and gives back   *)
(* a new substitution which is already unwinded and ready to be applied and  *)
(* a new metasenv in which some hypothesis in the contexts of the            *)
(* metavariables may have been restricted.                                   *)
let fo_unif metasenv context t1 t2 ugraph = 
 fo_unif_subst false [] context metasenv t1 t2 ugraph ;;

let enrich_msg msg subst context metasenv t1 t2 ugraph =
 lazy (
  if verbose then
   sprintf "[Verbose] Unification error unifying %s of type %s with %s of type %s in context\n%s\nand metasenv\n%s\nand substitution\n%s\nbecause %s"
    (CicMetaSubst.ppterm ~metasenv subst t1)
    (try
      let ty_t1,_ = type_of_aux' metasenv subst context t1 ugraph in
      CicPp.ppterm ty_t1
    with 
    | UnificationFailure s
    | Uncertain s
    | AssertFailure s -> sprintf "MALFORMED(t1): \n<BEGIN>%s\n<END>" (Lazy.force s))
    (CicMetaSubst.ppterm ~metasenv subst t2)
    (try
      let ty_t2,_ = type_of_aux' metasenv subst context t2 ugraph in
      CicPp.ppterm ty_t2
    with
    | UnificationFailure s
    | Uncertain s
    | AssertFailure s -> sprintf "MALFORMED(t2): \n<BEGIN>%s\n<END>" (Lazy.force s))
    (CicMetaSubst.ppcontext ~metasenv subst context)
    (CicMetaSubst.ppmetasenv subst metasenv)
    (CicMetaSubst.ppsubst ~metasenv subst) (Lazy.force msg)
 else
   sprintf "Unification error unifying %s of type %s with %s of type %s in context\n%s\nand metasenv\n%s\nbecause %s"
    (CicMetaSubst.ppterm_in_context ~metasenv subst t1 context)
    (try
      let ty_t1,_ = type_of_aux' metasenv subst context t1 ugraph in
      CicMetaSubst.ppterm_in_context ~metasenv subst ty_t1 context
    with 
    | UnificationFailure s
    | Uncertain s
    | AssertFailure s -> sprintf "MALFORMED(t1): \n<BEGIN>%s\n<END>" (Lazy.force s))
    (CicMetaSubst.ppterm_in_context ~metasenv subst t2 context)
    (try
      let ty_t2,_ = type_of_aux' metasenv subst context t2 ugraph in
      CicMetaSubst.ppterm_in_context ~metasenv subst ty_t2 context
    with
    | UnificationFailure s
    | Uncertain s
    | AssertFailure s -> sprintf "MALFORMED(t2): \n<BEGIN>%s\n<END>" (Lazy.force s))
    (CicMetaSubst.ppcontext ~metasenv subst context)
    ("OMITTED" (*CicMetaSubst.ppmetasenv subst metasenv*))
    (Lazy.force msg)
 )

let fo_unif_subst subst context metasenv t1 t2 ugraph =
  try
    fo_unif_subst false subst context metasenv t1 t2 ugraph
  with
  | AssertFailure msg ->
     raise (AssertFailure (enrich_msg msg subst context metasenv t1 t2 ugraph))
  | UnificationFailure msg ->
     raise (UnificationFailure (enrich_msg msg subst context metasenv t1 t2 ugraph))
;;
