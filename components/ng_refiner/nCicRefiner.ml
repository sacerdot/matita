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

(* $Id$ *)

exception RefineFailure of (Stdpp.location * string) Lazy.t;;
exception Uncertain of (Stdpp.location * string) Lazy.t;;
exception AssertFailure of string Lazy.t;;

module C = NCic
module Ref = NReference

let debug = ref false;;
let indent = ref "";;
let times = ref [];;
let pp s =
 if !debug then
  prerr_endline (Printf.sprintf "%-20s" !indent ^ " " ^ Lazy.force s)
;;
let inside c =
 if !debug then
  begin
   let time1 = Unix.gettimeofday () in
   indent := !indent ^ String.make 1 c;
   times := time1 :: !times;
   prerr_endline ("{{{" ^ !indent ^ " ")
  end
;;
let outside ok =
 if !debug then
  begin
   let time2 = Unix.gettimeofday () in
   let time1 =
    match !times with time1::tl -> times := tl; time1 | [] -> assert false in
   prerr_endline ("}}} " ^ string_of_float (time2 -. time1));
   if not ok then prerr_endline "exception raised!";
   try
    indent := String.sub !indent 0 (String.length !indent -1)
   with
    Invalid_argument _ -> indent := "??"; ()
 end
;;


let wrap_exc msg = function
  | NCicUnification.Uncertain _ -> Uncertain msg
  | NCicUnification.UnificationFailure _ -> RefineFailure msg
  | NCicTypeChecker.TypeCheckerFailure _ -> RefineFailure msg
  | e -> raise e
;;

let exp_implicit rdb ~localise metasenv subst context with_type t =
 function      
  | `Closed ->
      let metasenv,subst,expty =
       match with_type with
          None -> metasenv,subst,None
        | Some typ ->
           let (metasenv,subst),typ =
            try
             NCicMetaSubst.delift
              ~unify:(fun m s c t1 t2 ->
                try Some (NCicUnification.unify rdb m s c t1 t2)
                with NCicUnification.UnificationFailure _ | NCicUnification.Uncertain _ -> None)
              metasenv subst context 0 (0,NCic.Irl 0) typ
            with
              NCicMetaSubst.MetaSubstFailure _
            | NCicMetaSubst.Uncertain _ ->
               raise (RefineFailure (lazy (localise t,"Trying to create a closed meta with a non closed type: " ^ NCicPp.ppterm ~metasenv ~subst ~context typ)))

           in
            metasenv,subst,Some typ
      in
       NCicMetaSubst.mk_meta metasenv [] ?with_type:expty `IsTerm,subst
  | `Type -> NCicMetaSubst.mk_meta metasenv context ?with_type `IsType,subst
  | `Term -> NCicMetaSubst.mk_meta metasenv context ?with_type `IsTerm,subst
  | `Tagged s ->
      NCicMetaSubst.mk_meta 
        ~attrs:[`Name s] metasenv context ?with_type `IsTerm,subst
  | `Vector ->
      raise (RefineFailure (lazy (localise t, "A vector of implicit terms " ^
       "can only be used in argument position")))
  | _ -> assert false
;;

let check_allowed_sort_elimination rdb localise r orig =
   let mkapp he arg =
     match he with
     | C.Appl l -> C.Appl (l @ [arg])
     | t -> C.Appl [t;arg] in
   (* ctx, ind_type @ lefts, sort_of_ind_ty@lefts, outsort *)
   let rec aux metasenv subst context ind arity1 arity2 =
     (*D*)inside 'S'; try let rc = 
     let arity1 = NCicReduction.whd ~subst context arity1 in
     pp (lazy(NCicPp.ppterm ~subst ~metasenv ~context arity1 ^ "   elimsto   " ^
        NCicPp.ppterm ~subst ~metasenv ~context arity2 ^ "\nMENV:\n"^
        NCicPp.ppmetasenv ~subst metasenv));
     match arity1 with
     | C.Prod (name,so1,de1) (* , t ==?== C.Prod _ *) ->
        let metasenv, _, meta, _ = 
          NCicMetaSubst.mk_meta metasenv ((name,C.Decl so1)::context) `IsType 
        in
        let metasenv, subst = 
          try NCicUnification.unify rdb metasenv subst context 
                arity2 (C.Prod (name, so1, meta)) 
          with exc -> raise (wrap_exc (lazy (localise orig, Printf.sprintf
            "expected %s, found %s" (* XXX localizzare meglio *)
            (NCicPp.ppterm ~subst ~metasenv ~context (C.Prod (name, so1, meta)))
            (NCicPp.ppterm ~subst ~metasenv ~context arity2))) exc)
        in
        aux metasenv subst ((name, C.Decl so1)::context)
         (mkapp (NCicSubstitution.lift 1 ind) (C.Rel 1)) de1 meta
     | C.Sort _ (* , t ==?== C.Prod _ *) ->
        let metasenv, _, meta, _ = NCicMetaSubst.mk_meta metasenv [] `IsSort in
        let metasenv, subst = 
          try NCicUnification.unify rdb metasenv subst context 
                arity2 (C.Prod ("_", ind, meta)) 
          with exc -> raise (wrap_exc (lazy (localise orig, Printf.sprintf
            "expected %s, found %s" (* XXX localizzare meglio *)
            (NCicPp.ppterm ~subst ~metasenv ~context (C.Prod ("_", ind, meta)))
            (NCicPp.ppterm ~subst ~metasenv ~context arity2))) exc)
        in
        (try NCicTypeChecker.check_allowed_sort_elimination
            ~metasenv ~subst r context ind arity1 arity2; 
            metasenv, subst
        with exc -> raise (wrap_exc (lazy (localise orig, 
          "Sort elimination not allowed ")) exc))
     | _ -> assert false
     (*D*)in outside true; rc with exc -> outside false; raise exc
   in
    aux
;;

let rec typeof rdb 
  ?(localise=fun _ -> Stdpp.dummy_loc) 
  metasenv subst context term expty 
=
  let force_ty skip_lambda skip_appl metasenv subst context orig t infty expty =
    (*D*)inside 'F'; try let rc = 
    match expty with
    | Some expty ->
       (match t with
       | C.Implicit _ -> assert false
       | C.Lambda _ when skip_lambda -> metasenv, subst, t, expty
       | C.Appl _ when skip_appl -> metasenv, subst, t, expty
       | _ ->
          pp (lazy ("forcing infty=expty: "^
          (NCicPp.ppterm ~metasenv ~subst ~context infty) ^  " === " ^
          (NCicPp.ppterm ~metasenv ~subst:[] ~context expty)));
           try 
             let metasenv, subst =
    (*D*)inside 'U'; try let rc = 
               NCicUnification.unify rdb metasenv subst context infty expty 
    (*D*)in outside true; rc with exc -> outside false; raise exc
             in
             metasenv, subst, t, expty
           with 
           | NCicUnification.Uncertain _ 
           | NCicUnification.UnificationFailure _ as exc -> 
             try_coercions rdb ~localise 
               metasenv subst context t orig infty expty true exc)
    | None -> metasenv, subst, t, infty
    (*D*)in outside true; rc with exc -> outside false; raise exc
  in
  let rec typeof_aux metasenv subst context expty = 
    fun t as orig -> 
    (*D*)inside 'R'; try let rc = 
    pp (lazy (NCicPp.ppterm ~metasenv ~subst ~context t ^ " ::exp:: " ^
       match expty with None -> "None" | Some e -> 
       NCicPp.ppterm ~metasenv ~subst ~context e));
    let metasenv, subst, t, infty = 
    match t with
    | C.Rel n ->
        let infty = 
         (try
           match List.nth context (n - 1) with
           | (_,C.Decl ty) -> NCicSubstitution.lift n ty
           | (_,C.Def (_,ty)) -> NCicSubstitution.lift n ty
         with Failure _ -> 
           raise (RefineFailure (lazy (localise t,"unbound variable"))))
        in
        metasenv, subst, t, infty
    | C.Sort s -> 
         (try metasenv, subst, t, C.Sort (NCicEnvironment.typeof_sort s)
         with 
         | NCicEnvironment.UntypableSort msg -> 
              raise (RefineFailure (lazy (localise t, Lazy.force msg)))
         | NCicEnvironment.AssertFailure msg -> raise (AssertFailure msg))
    | C.Implicit infos -> 
         let (metasenv,_,t,ty),subst =
           exp_implicit rdb ~localise metasenv subst context expty t infos
         in
         if expty = None then
          typeof_aux metasenv subst context None t
         else
          metasenv, subst, t, ty 
    | C.Meta (n,l) as t -> 
       let metasenv, ty =
        try
         let _,_,_,ty = NCicUtils.lookup_subst n subst in metasenv, ty 
        with NCicUtils.Subst_not_found _ ->
         NCicMetaSubst.extend_meta metasenv n
       in
       metasenv, subst, t, NCicSubstitution.subst_meta l ty
    | C.Const _ -> 
       metasenv, subst, t, NCicTypeChecker.typeof ~subst ~metasenv context t
    | C.Prod (name,(s as orig_s),(t as orig_t)) ->
       let metasenv, subst, s, s1 = typeof_aux metasenv subst context None s in
       let metasenv, subst, s, s1 = 
         force_to_sort rdb 
           metasenv subst context s orig_s localise s1 in
       let context1 = (name,(C.Decl s))::context in
       let metasenv, subst, t, s2 = typeof_aux metasenv subst context1 None t in
       let metasenv, subst, t, s2 = 
         force_to_sort rdb 
           metasenv subst context1 t orig_t localise s2 in
       let metasenv, subst, s, t, ty = 
         sort_of_prod localise metasenv subst 
           context orig_s orig_t (name,s) t (s1,s2)
       in
       metasenv, subst, NCic.Prod(name,s,t), ty
    | C.Lambda (n,(s as orig_s),t) as orig ->
       let exp_s, exp_ty_t, force_after =
         match expty with
         | None -> None, None, false
         | Some expty -> 
             match NCicReduction.whd ~subst context expty with
             | C.Prod (_,s,t) -> Some s, Some t, false
             | _ -> None, None, true 
       in
       let (metasenv,subst), s = 
         match exp_s with 
         | Some exp_s ->
             (* optimized case: implicit and implicitly typed meta
              * the optimization prevents proliferation of metas  *)
             (match s with
              | C.Implicit _ -> (metasenv,subst),exp_s
              | _ ->
                  let metasenv, subst, s = match s with 
                    | C.Meta (n,_) 
                        when (try (match NCicUtils.lookup_meta n metasenv with
                              | _,_,C.Implicit (`Typeof _) -> true
                              | _ -> false)
                        with 
                          | _ -> false) -> metasenv, subst, s
                    | _ ->  check_type rdb ~localise metasenv subst context s in
                  (try 
                    pp(lazy("Force source to: "^NCicPp.ppterm ~metasenv ~subst
                       ~context exp_s));
                    NCicUnification.unify ~test_eq_only:true rdb metasenv subst context s exp_s,s
                  with exc -> raise (wrap_exc (lazy (localise orig_s, Printf.sprintf
                    "Source type %s was expected to be %s" (NCicPp.ppterm ~metasenv
                    ~subst ~context s) (NCicPp.ppterm ~metasenv ~subst ~context
                    exp_s))) exc)))
         | None -> 
             let metasenv, subst, s = 
               check_type rdb ~localise metasenv subst context s in
             (metasenv, subst), s
       in
       let context_for_t = (n,C.Decl s) :: context in
       let metasenv, subst, t, ty_t = 
         typeof_aux metasenv subst context_for_t exp_ty_t t 
       in
       if force_after then
         force_ty false true metasenv subst context orig 
           (C.Lambda(n,s,t)) (C.Prod (n,s,ty_t)) expty
       else 
         metasenv, subst, C.Lambda(n,s,t), C.Prod (n,s,ty_t)
    | C.LetIn (n,ty,t,bo) ->
       let metasenv, subst, ty = 
         check_type rdb ~localise metasenv subst context ty in
       let metasenv, subst, t, _ = 
         typeof_aux metasenv subst context (Some ty) t in
       let context1 = (n, C.Def (t,ty)) :: context in
       let metasenv, subst, expty1 = 
         match expty with 
         | None -> metasenv, subst, None 
         | Some x -> 
             let m, s, x = 
               NCicUnification.delift_type_wrt_terms 
                rdb metasenv subst context1 (NCicSubstitution.lift 1 x)
                [NCicSubstitution.lift 1 t]
             in
               m, s, Some x
       in
       let metasenv, subst, bo, bo_ty = 
         typeof_aux metasenv subst context1 expty1 bo 
       in
       let bo_ty = NCicSubstitution.subst ~avoid_beta_redexes:true t bo_ty in
       metasenv, subst, C.LetIn (n, ty, t, bo), bo_ty
    | C.Appl ((he as orig_he)::(_::_ as args)) ->
       let upto = match orig_he with C.Meta _ -> List.length args | _ -> 0 in
       let hbr t = 
         if upto > 0 then NCicReduction.head_beta_reduce ~upto t else t 
       in
       let refine_appl metasenv subst args =
         let metasenv, subst, he, ty_he = 
            typeof_aux metasenv subst context None he in
         let metasenv, subst, t, ty = 
           eat_prods rdb ~localise force_ty metasenv subst context expty t
            orig_he he ty_he args in
         metasenv, subst, hbr t, ty
       in
       if args = [C.Implicit `Vector] && expty <> None then
         (* we try here to expand the vector a 0 implicits, but we use
          * the expected type *)
         try
           let metasenv, subst, he, ty_he = 
              typeof_aux metasenv subst context expty he in
           metasenv, subst, hbr he, ty_he
         with Uncertain _ | RefineFailure _ -> refine_appl metasenv subst args
       else
        (* CSC: whd can be useful on he too... *)
        (match he with
            C.Const (Ref.Ref (uri1,Ref.Con _)) -> (
             match
              HExtlib.map_option (NCicReduction.whd ~subst context) expty
             with
                Some (C.Appl(C.Const(Ref.Ref (uri2,Ref.Ind _) as ref)::expargs))
                when NUri.eq uri1 uri2 ->
                (try
                 let _,leftno,_,_,_ = NCicEnvironment.get_checked_indtys ref in
                 let leftexpargs,_ = HExtlib.split_nth leftno expargs in
                  let rec instantiate metasenv subst revargs args =
                   function
                     [] ->
                      (* some checks are re-done here, but it would be complex
                         to avoid them (e.g. we did not check yet that the
                         constructor is a constructor for that inductive type)*)
                      refine_appl metasenv subst ((List.rev revargs)@args)
                   | (exparg::expargs) as allexpargs ->
                      match args with
                         [] -> raise (Failure "Not enough args")
                       | (C.Implicit `Vector::args) as allargs ->
                          (try
                            instantiate metasenv subst revargs args allexpargs
                           with
                              Sys.Break as exn -> raise exn
                            | _ ->
                             instantiate metasenv subst revargs
                              (C.Implicit `Term :: allargs) allexpargs)
                       | arg::args ->
                          let metasenv,subst,arg,_ =
                           typeof_aux metasenv subst context None arg in
                          let metasenv,subst =
                           NCicUnification.unify rdb metasenv subst context
                            arg exparg
                          in
                           instantiate metasenv subst(arg::revargs) args expargs
                  in
                   instantiate metasenv subst [] args leftexpargs 
                with
                 | Sys.Break as exn -> raise exn
                 | _ ->
                    refine_appl metasenv subst args (* to try coercions *))
              | _ -> refine_appl metasenv subst args)
          | _ -> refine_appl metasenv subst args)
   | C.Appl _ -> raise (AssertFailure (lazy "Appl of length < 2"))
   | C.Match (Ref.Ref (_,Ref.Ind (_,tyno,_)) as r,
          outtype,(term as orig_term),pl) as orig ->
      let _, leftno, itl, _, _ = NCicEnvironment.get_checked_indtys r in
      let _, _, arity, cl = List.nth itl tyno in
      let constructorsno = List.length cl in
      let _, metasenv, args = 
        NCicMetaSubst.saturate metasenv subst context arity 0 in
      let ind = if args = [] then C.Const r else C.Appl (C.Const r::args) in
      let metasenv, subst, term, _ = 
        typeof_aux metasenv subst context (Some ind) term in
      let parameters, arguments = HExtlib.split_nth leftno args in
      let outtype =  
        match outtype with
        | C.Implicit _ as ot -> 
             let rec aux = function
               | [] -> NCic.Lambda ("_",NCic.Implicit `Type,ot)
               | _::tl -> NCic.Lambda ("_",NCic.Implicit `Type,aux tl)
             in
               aux arguments
        | _ -> outtype
      in 
      let metasenv, subst, outtype, outsort = 
        typeof_aux metasenv subst context None outtype in

      (* next lines are to do a subst-expansion of the outtype, so
         that when it becomes a beta-abstraction, the beta-redex is
         fired during substitution *)
      let _,fresh_metanoouttype,newouttype,_ =
       NCicMetaSubst.mk_meta metasenv context `IsTerm in
      let subst =
       (fresh_metanoouttype,([`Name "outtype"],context,outtype,outsort))
         ::subst in
      let outtype = newouttype in

      (* let's control if the sort elimination is allowed: [(I q1 ... qr)|B] *)
      let ind =
        if parameters = [] then C.Const r
        else C.Appl ((C.Const r)::parameters) in
      let metasenv, subst, ind, ind_ty = 
        typeof_aux metasenv subst context None ind in
      let metasenv, subst = 
         check_allowed_sort_elimination rdb localise r orig_term metasenv subst 
           context ind ind_ty outsort 
      in
      (* let's check if the type of branches are right *)
      if List.length pl <> constructorsno then
       raise (RefineFailure (lazy (localise orig, 
         "Wrong number of cases in a match")));
(*
      let metasenv, subst =
        match expty with
        | None -> metasenv, subst
        | Some expty -> 
           NCicUnification.unify rdb metasenv subst context resty expty 
      in
*)
      let _, metasenv, subst, pl =
        List.fold_right
          (fun p (j, metasenv, subst, branches) ->
              let cons = 
                let cons = Ref.mk_constructor j r in
                if parameters = [] then C.Const cons
                else C.Appl (C.Const cons::parameters)
              in
              let metasenv, subst, cons, ty_cons = 
                typeof_aux metasenv subst context None cons in
              let ty_branch = 
                NCicTypeChecker.type_of_branch 
                  ~subst context leftno outtype cons ty_cons in
              pp (lazy ("TYPEOFBRANCH: " ^
               NCicPp.ppterm ~metasenv ~subst ~context p ^ " ::inf:: " ^
               NCicPp.ppterm ~metasenv ~subst ~context ty_branch ));
              let metasenv, subst, p, _ = 
                typeof_aux metasenv subst context (Some ty_branch) p in
              j-1, metasenv, subst, p :: branches)
          pl (List.length pl, metasenv, subst, [])
      in
      let resty = C.Appl (outtype::arguments@[term]) in
      let resty = NCicReduction.head_beta_reduce ~subst resty in
      metasenv, subst, C.Match (r, outtype, term, pl),resty
    | C.Match _ -> assert false
    in
    pp (lazy (NCicPp.ppterm ~metasenv ~subst ~context t ^ " ::inf:: "^
         NCicPp.ppterm ~metasenv ~subst ~context infty ));
      force_ty true true metasenv subst context orig t infty expty
    (*D*)in outside true; rc with exc -> outside false; raise exc
  in
    typeof_aux metasenv subst context expty term

and check_type rdb ~localise metasenv subst context (ty as orig_ty) =
  let metasenv, subst, ty, sort = 
    typeof rdb ~localise metasenv subst context ty None
  in
  let metasenv, subst, ty, _ = 
    force_to_sort rdb metasenv subst context ty orig_ty localise sort
  in
    metasenv, subst, ty

and try_coercions rdb 
  ~localise 
  metasenv subst context t orig_t infty expty perform_unification exc 
=
  let cs_subst = NCicSubstitution.subst ~avoid_beta_redexes:true in
  try 
    pp (lazy "WWW: trying coercions -- preliminary unification");
    let metasenv, subst = 
      NCicUnification.unify rdb metasenv subst context infty expty
    in metasenv, subst, t, expty
  with
  | exn ->
  (* we try with a coercion *)
  let rec first exc = function
  | [] ->   
      pp (lazy "WWW: no more coercions!");      
      raise (wrap_exc (lazy (localise orig_t, Printf.sprintf
        "The term\n%s\nhas type\n%s\nbut is here used with type\n%s"
        (NCicPp.ppterm ~metasenv ~subst ~context t)
        (NCicPp.ppterm ~metasenv ~subst ~context infty)
        (NCicPp.ppterm ~metasenv ~subst ~context expty))) exc)
  | (_,metasenv, newterm, newtype, meta)::tl ->
      try 
          pp (lazy("K=" ^ NCicPp.ppterm ~metasenv ~subst ~context newterm));
          pp (lazy ( "UNIFICATION in CTX:\n"^ 
            NCicPp.ppcontext ~metasenv ~subst context
            ^ "\nMENV: " ^
            NCicPp.ppmetasenv metasenv ~subst
            ^ "\nOF: " ^
            NCicPp.ppterm ~metasenv ~subst ~context t ^  " === " ^
            NCicPp.ppterm ~metasenv ~subst ~context meta ^ "\n"));
        let metasenv, subst = 
          NCicUnification.unify rdb metasenv subst context t meta
        in
          pp (lazy ( "UNIFICATION in CTX:\n"^ 
            NCicPp.ppcontext ~metasenv ~subst context
            ^ "\nMENV: " ^
            NCicPp.ppmetasenv metasenv ~subst
            ^ "\nOF: " ^
            NCicPp.ppterm ~metasenv ~subst ~context newtype ^  " === " ^
            NCicPp.ppterm ~metasenv ~subst ~context expty ^ "\n"));
        let metasenv, subst = 
          if perform_unification then
            NCicUnification.unify rdb metasenv subst context newtype expty
          else metasenv, subst
        in
        metasenv, subst, newterm, newtype
      with 
      | NCicUnification.UnificationFailure _ -> first exc tl
      | NCicUnification.Uncertain _ as exc -> first exc tl
  in
  
  try 
    pp (lazy "WWW: trying coercions -- inner check");
    match infty, expty, t with
    | _,_, NCic.Match (Ref.Ref (_,Ref.Ind (_,tyno,leftno)) as r,outty,m,pl) ->
        (*{{{*) pp (lazy "CASE");
        (* {{{ helper functions *)
        let get_cl_and_left_p refit outty =
          match refit with
          | NReference.Ref (uri, NReference.Ind (_,tyno,leftno)) ->
             let _, leftno, itl, _, _ = NCicEnvironment.get_checked_indtys r in
             let _, _, ty, cl = List.nth itl tyno in
             let constructorsno = List.length cl in
              let count_pis t =
                let rec aux ctx t = 
                  match NCicReduction.whd ~subst ~delta:max_int ctx t with
                  | NCic.Prod (name,src,tgt) ->
                      let ctx = (name, (NCic.Decl src)) :: ctx in
                      1 + aux ctx tgt
                  | _ -> 0
                in
                  aux [] t
              in
              let rec skip_lambda_delifting t n =
                match t,n with
                | _,0 -> t
                | NCic.Lambda (_,_,t),n ->
                    pp (lazy ("WWW: failing term? "^ NCicPp.ppterm ~subst:[] ~metasenv:[] ~context:[] t)); 
                    skip_lambda_delifting
                      (* substitute dangling indices with a dummy *)
                      (NCicSubstitution.subst (NCic.Sort NCic.Prop) t) (n - 1)
                | _ -> assert false
              in
              let get_l_r_p n = function
                | NCic.Lambda (_,NCic.Const (Ref.Ref (_,Ref.Ind (_,_,_))),_) -> [],[]
                | NCic.Lambda (_,NCic.Appl 
                    (NCic.Const (Ref.Ref (_,Ref.Ind (_,_,_))) :: args),_) ->
                    HExtlib.split_nth n args
                | _ -> assert false
              in
              let pis = count_pis ty in
              let rno = pis - leftno in
              let t = skip_lambda_delifting outty rno in
              let left_p, _ = get_l_r_p leftno t in
              let instantiate_with_left cl =
                List.map 
                  (fun ty -> 
                    List.fold_left 
                      (fun t p -> match t with
                        | NCic.Prod (_,_,t) ->
                            cs_subst p t
                        | _-> assert false)
                      ty left_p) 
                  cl 
              in
              let cl = instantiate_with_left (List.map (fun (_,_,x) -> x) cl) in
              cl, left_p, leftno, rno
          | _ -> raise exn
        in
        let rec keep_lambdas_and_put_expty ctx t bo right_p matched n =
          match t,n with
          | _,0 ->
            let rec mkr n = function 
              | [] -> [] | _::tl -> NCic.Rel n :: mkr (n+1) tl
            in
            pp (lazy ("input replace: " ^ NCicPp.ppterm ~context:ctx ~metasenv:[] ~subst:[] bo));
            let bo =
            NCicRefineUtil.replace_lifting
              ~equality:(fun _ -> NCicRefineUtil.alpha_equivalence)
              ~context:ctx
              ~what:(matched::right_p)
              ~with_what:(NCic.Rel 1::List.rev (mkr 2 right_p))
              ~where:bo
            in
            pp (lazy ("output replace: " ^ NCicPp.ppterm ~context:ctx ~metasenv:[] ~subst:[] bo));
            bo
          | NCic.Lambda (name, src, tgt),_ ->
              NCic.Lambda (name, src,
               keep_lambdas_and_put_expty 
                ((name, NCic.Decl src)::ctx) tgt (NCicSubstitution.lift 1 bo)
                (List.map (NCicSubstitution.lift 1) right_p) (NCicSubstitution.lift 1 matched) (n-1))
          | _ -> assert false
        in
        (*let eq = NCic.Const (NReference.reference_of_string ("cic:/matita/ng/Plogic/equality/eq.ind(1,0,2)")) in
        let eq_refl = NCic.Const (NReference.reference_of_string ("cic:/matita/ng/Plogic/equality/eq.con(0,1,2)")) in*)
        let eq = NCic.Const (NReference.reference_of_string ("cic:/matita/ng/Plogic/jmeq/jmeq.ind(1,0,2)")) in
        let eq_refl = NCic.Const (NReference.reference_of_string ("cic:/matita/ng/Plogic/jmeq/jmeq.con(0,1,2)")) in
        let add_params 
          metasenv subst context cty outty mty m i 
        =
          let rec aux context outty par j mty m = function
            | NCic.Prod (name, src, tgt) ->
                let t,k = 
                  aux 
                    ((name, NCic.Decl src) :: context)
                    (NCicSubstitution.lift 1 outty) (NCic.Rel j::par) (j+1) 
                    (NCicSubstitution.lift 1 mty) (NCicSubstitution.lift 1 m) tgt
                in
                NCic.Prod (name, src, t), k
            | NCic.Const (Ref.Ref (_,Ref.Ind (_,_,leftno)) as r) ->
                let k = 
                  let k = NCic.Const(Ref.mk_constructor i r) in
                  NCicUntrusted.mk_appl k par
                in
                (* the type has no parameters, so kty = mty
                let kty = 
                  try NCicTypechecker.typeof ~subst ~metasenv context k
                  with NCicTypeChecker.TypeCheckerFailure _ -> assert false
                in *)
                NCic.Prod ("p", 
                 NCic.Appl [eq; mty; m; mty; k],
                 (NCicSubstitution.lift 1
                  (NCicReduction.head_beta_reduce ~delta:max_int 
                   (NCicUntrusted.mk_appl outty [k])))),[mty,m,mty,k]
            | NCic.Appl (NCic.Const (Ref.Ref (_,Ref.Ind (_,_,leftno)) as r)::pl) ->
                let left_p,right_p = HExtlib.split_nth leftno pl in
                let has_rights = right_p <> [] in
                let k = 
                  let k = NCic.Const(Ref.mk_constructor i r) in
                  NCicUntrusted.mk_appl k (left_p@par)
                in
                let right_p = 
                  try match 
                    NCicTypeChecker.typeof ~subst ~metasenv context k
                  with
                  | NCic.Appl (NCic.Const (Ref.Ref (_,Ref.Ind (_,_,_)))::args) ->
                      snd (HExtlib.split_nth leftno args)
                  | _ -> assert false
                  with NCicTypeChecker.TypeCheckerFailure _-> assert false
                in
                let orig_right_p =
                  match mty with
                  | NCic.Appl (NCic.Const (Ref.Ref (_,Ref.Ind (_,_,_)))::args) ->
                      snd (HExtlib.split_nth leftno args)
                  | _ -> assert false
                in
                List.fold_right2 
                  (fun x y (tacc,pacc) ->
                    let xty = 
          	    try NCicTypeChecker.typeof ~subst ~metasenv context x
                      with NCicTypeChecker.TypeCheckerFailure _ -> assert false
                    in
                    let yty = 
          	    try NCicTypeChecker.typeof ~subst ~metasenv context y
                      with NCicTypeChecker.TypeCheckerFailure _ -> assert false
                    in
                    NCic.Prod ("_", NCic.Appl [eq;xty;x;yty;y],
                     NCicSubstitution.lift 1 tacc), (xty,x,yty,y)::pacc) 
                  (orig_right_p @ [m]) (right_p @ [k]) 
                  (NCicReduction.head_beta_reduce ~delta:max_int
                      (NCicUntrusted.mk_appl outty (right_p@[k])), [])  

  (*              if has_rights then
                  NCicReduction.head_beta_reduce ~delta:max_int
                    (NCic.Appl (outty ::right_p @ [k])),k
                else
                  NCic.Prod ("p", 
                   NCic.Appl [eq; mty; m; k],
                   (NCicSubstitution.lift 1
                    (NCicReduction.head_beta_reduce ~delta:max_int 
                     (NCic.Appl (outty ::right_p @ [k]))))),k*)
            | _ -> assert false
          in
            aux context outty [] 1 mty m cty
        in
        let add_lambda_for_refl_m pbo eqs cty =
          (* k lives in the right context *)
          (* if rno <> 0 then pbo else *)
          let rec aux = function 
            | NCic.Lambda (name,src,bo), NCic.Prod (_,_,ty) ->
                NCic.Lambda (name,src,
                (aux (bo,ty)))
            | t,_ -> snd (List.fold_right
                (fun (xty,x,yty,y) (n,acc) -> n+1, NCic.Lambda ("p" ^ string_of_int n,
                  NCic.Appl [eq; xty; x; yty; y],
                  NCicSubstitution.lift 1 acc)) eqs (1,t))
                (*NCic.Lambda ("p",
                  NCic.Appl [eq; mty; m; k],NCicSubstitution.lift 1 t)*)
          in
          aux (pbo,cty)
        in
        let add_pi_for_refl_m context new_outty mty m lno rno =
          (*if rno <> 0 then new_outty else*)
            let rec aux context mty m = function
              | NCic.Lambda (name, src, tgt) ->
                  let context = (name, NCic.Decl src)::context in
                  NCic.Lambda (name, src, aux context (NCicSubstitution.lift 1 mty) (NCicSubstitution.lift 1 m) tgt)
              | t -> 
                  let lhs =
                    match mty with
                    | NCic.Appl (_::params) -> (snd (HExtlib.split_nth lno params))@[m]
                    | _ -> [m]
                  in
                  let rhs = 
                    List.map (fun x -> NCic.Rel x) 
                      (List.rev (HExtlib.list_seq 1 (rno+2))) in
                  List.fold_right2
                    (fun x y acc ->
                      let xty = 
    		    try NCicTypeChecker.typeof ~subst ~metasenv context x
                        with NCicTypeChecker.TypeCheckerFailure _ -> assert false
                      in
                      let yty = 
    		    try NCicTypeChecker.typeof ~subst ~metasenv context y
                        with NCicTypeChecker.TypeCheckerFailure _ -> assert false
                      in
                      NCic.Prod
                      ("_", NCic.Appl [eq;xty;x;yty;y],
                       (NCicSubstitution.lift 1 acc)))
                    lhs rhs t
  (*                NCic.Prod 
                    ("_", NCic.Appl [eq;mty;m;NCic.Rel 1],
                    NCicSubstitution.lift 1 t)*)
            in
              aux context mty m new_outty
        in (* }}} end helper functions *)
        (* constructors types with left params already instantiated *)
        let outty = NCicUntrusted.apply_subst subst context outty in
        let cl, left_p, leftno,rno = 
          get_cl_and_left_p r outty
        in
        let right_p, mty = 
          try
            match 
              NCicTypeChecker.typeof ~subst ~metasenv context m
            with
            | (NCic.Const (Ref.Ref (_,Ref.Ind (_,_,_))) | NCic.Meta _) as mty -> [], mty
            | NCic.Appl ((NCic.Const (Ref.Ref (_,Ref.Ind (_,_,_)))|NCic.Meta _)::args) as mty ->
                snd (HExtlib.split_nth leftno args), mty
            | _ -> assert false
          with NCicTypeChecker.TypeCheckerFailure _ -> 
             raise (AssertFailure(lazy "already ill-typed matched term"))
        in
        let mty = NCicUntrusted.apply_subst subst context mty in
        let outty = NCicUntrusted.apply_subst subst context outty in
        let expty = NCicUntrusted.apply_subst subst context expty in
        let new_outty =
         keep_lambdas_and_put_expty context outty expty right_p m (rno+1)
        in
        pp 
          (lazy ("CASE: new_outty: " ^ NCicPp.ppterm 
           ~context ~metasenv ~subst new_outty));
        let _,pl,subst,metasenv = 
          List.fold_right2
            (fun cty pbo (i, acc, s, menv) -> 
               pp (lazy ("begin iteration"));
              (* Pi k_par, (Pi H:m=(K_i left_par k_par)), 
               *   (new_)outty right_par (K_i left_par k_par) *)
               let infty_pbo, _ = 
                 add_params menv s context cty outty mty m i in
               pp 
                (lazy ("CASE: infty_pbo: "^ NCicPp.ppterm
                 ~context ~metasenv ~subst infty_pbo));
               let expty_pbo, eqs = (* k is (K_i left_par k_par) *)
                 add_params menv s context cty new_outty mty m i in
               pp 
                (lazy ("CASE: expty_pbo: "^ NCicPp.ppterm
                 ~context ~metasenv ~subst expty_pbo));
               let pbo = add_lambda_for_refl_m pbo eqs cty in
               pp 
                 (lazy ("CASE: pbo: " ^ NCicPp.ppterm
                 ~context ~metasenv ~subst pbo));
               let metasenv, subst, pbo, _ =
                 try_coercions rdb ~localise menv s context pbo 
          	 orig_t (*??*) infty_pbo expty_pbo perform_unification exc
               in
               pp 
                 (lazy ("CASE: pbo2: " ^ NCicPp.ppterm 
                 ~context ~metasenv ~subst pbo));
               (i-1, pbo::acc, subst, metasenv))
            cl pl (List.length pl, [], subst, metasenv)
        in
        (*let metasenv, subst = 
          try 
            NCicUnification.unify rdb metasenv subst context outty new_outty 
          with _ -> raise (RefineFailure (lazy (localise orig_t, "try_coercions")))
        in*)
        let new_outty = add_pi_for_refl_m context new_outty mty m leftno rno in
        pp (lazy ("CASE: new_outty: " ^ (NCicPp.ppterm 
           ~metasenv ~subst ~context new_outty)));
        let right_tys = 
          List.map 
            (fun t -> NCicTypeChecker.typeof ~subst ~metasenv context t) right_p in
        let eqs = 
          List.map2 (fun x y -> NCic.Appl[eq_refl;x;y]) (right_tys@[mty]) 
            (right_p@[m]) in
        let t = NCic.Appl (NCic.Match(r,new_outty,m,pl) :: eqs) 
        in
        metasenv, subst, t, expty (*}}}*)
    | NCic.Prod (nameprod, src, ty),NCic.Prod (_, src2, ty2), _ -> 
        let rec mk_fresh_name ctx firstch n =
          let candidate = (String.make 1 firstch) ^ (string_of_int n) in
          if (List.for_all (fun (s,_) -> s <> candidate) ctx) then candidate
          else mk_fresh_name ctx firstch (n+1)
        in
        (*{{{*) pp (lazy "LAM");
        pp (lazy ("LAM: t = " ^ NCicPp.ppterm ~metasenv ~subst ~context t));
        let name_con = mk_fresh_name context 'c' 0
          (*FreshNamesGenerator.mk_fresh_name 
            ~subst metasenv context ~typ:src2 Cic.Anonymous*)
        in
        let context_src2 = ((name_con, NCic.Decl src2) :: context) in
        (* contravariant part: the argument of f:src->ty *)
        let metasenv, subst, rel1, _ = 
          try_coercions rdb ~localise metasenv subst context_src2
           (NCic.Rel 1) orig_t (NCicSubstitution.lift 1 src2) 
           (NCicSubstitution.lift 1 src) perform_unification exc
        in
        (* covariant part: the result of f(c x); x:src2; (c x):src *)
        let name_t, bo = 
          match t with
          | NCic.Lambda (n,_,bo) -> n, cs_subst rel1 (NCicSubstitution.lift_from 2 1 bo)
          | _ -> name_con, NCicUntrusted.mk_appl (NCicSubstitution.lift 1 t) [rel1]
        in
        (* we fix the possible dependency problem in the source ty *)
        let ty = cs_subst rel1 (NCicSubstitution.lift_from 2 1 ty) in
        let metasenv, subst, bo, _ = 
          try_coercions rdb ~localise metasenv subst context_src2
            bo orig_t ty ty2 perform_unification exc
        in
        let coerced = NCic.Lambda (name_t,src2, bo) in
        pp (lazy ("LAM: coerced = " ^ NCicPp.ppterm ~metasenv ~subst ~context coerced));
        metasenv, subst, coerced, expty (*}}}*)
    | _ -> raise exc
  with exc2 ->    
  pp(lazy("try_coercion " ^ 
    NCicPp.ppterm ~metasenv ~subst ~context infty ^ " |---> " ^
    NCicPp.ppterm ~metasenv ~subst ~context expty));
    first exc
      (NCicCoercion.look_for_coercion 
        rdb metasenv subst context infty expty)

and force_to_sort rdb metasenv subst context t orig_t localise ty =
  try 
    let metasenv, subst, ty = 
      NCicUnification.sortfy (Failure "sortfy") metasenv subst context ty in
      metasenv, subst, t, ty
  with
      Failure _ -> 
        let ty = NCicReduction.whd ~subst context ty in
          try_coercions rdb ~localise metasenv subst context
            t orig_t ty (NCic.Sort (NCic.Type 
              (match NCicEnvironment.get_universes () with
               | x::_ -> x 
               | _ -> assert false))) false 
             (Uncertain (lazy (localise orig_t, 
             "The type of " ^ NCicPp.ppterm ~metasenv ~subst ~context t ^
             " is not a sort: " ^ NCicPp.ppterm ~metasenv ~subst ~context ty)))

and sort_of_prod 
  localise metasenv subst context orig_s orig_t (name,s) t (t1, t2) 
=
   (* force to sort is done in the Prod case in typeof *)
   match t1, t2 with
   | C.Sort _, C.Sort C.Prop -> metasenv, subst, s, t, t2
   | C.Sort (C.Type u1), C.Sort (C.Type u2) ->
        metasenv, subst, s, t, C.Sort (C.Type (NCicEnvironment.max u1 u2)) 
   | C.Sort C.Prop,C.Sort (C.Type _) -> metasenv, subst, s, t, t2
   | C.Meta _, C.Sort _ 
   | C.Meta _, C.Meta (_,(_,_))
   | C.Sort _, C.Meta (_,(_,_)) -> metasenv, subst, s, t, t2 
   | x, (C.Sort _ | C.Meta _) | _, x -> 
      let y, context, orig = 
        if x == t1 then s, context, orig_s 
        else t, ((name,C.Decl s)::context), orig_t
      in
      raise (RefineFailure (lazy (localise orig,Printf.sprintf
        "%s is expected to be a type, but its type is %s that is not a sort" 
         (NCicPp.ppterm ~subst ~metasenv ~context y) 
         (NCicPp.ppterm ~subst ~metasenv ~context x))))

and guess_name subst ctx ty = 
  let aux initial = "#" ^ String.make 1 initial in
  match ty with
  | C.Const (NReference.Ref (u,_))
  | C.Appl (C.Const (NReference.Ref (u,_)) :: _) ->
      aux (String.sub (NUri.name_of_uri u) 0 1).[0] 
  | C.Prod _ -> aux 'f' 
  | C.Meta (n,lc) -> 
      (try
         let _,_,t,_ = NCicUtils.lookup_subst n subst in
         guess_name subst ctx (NCicSubstitution.subst_meta lc t)
      with NCicUtils.Subst_not_found _ -> aux 'M')
  | _ -> aux 'H' 

and eat_prods rdb ~localise force_ty metasenv subst context expty orig_t orig_he he ty_he args =
  (*D*)inside 'E'; try let rc = 
  let rec aux metasenv subst args_so_far he ty_he xxx =
  (*D*)inside 'V'; try let rc = 
   match xxx with
  | [] ->
     let res = NCicUntrusted.mk_appl he (List.rev args_so_far) in
     pp(lazy("FORCE FINAL APPL: " ^ 
       NCicPp.ppterm ~metasenv ~subst ~context res ^
       " of type " ^ NCicPp.ppterm ~metasenv ~subst ~context ty_he
       ^ " to type " ^ match expty with None -> "None" | Some x -> 
       NCicPp.ppterm ~metasenv ~subst ~context x));
     (* whatever the term is, we force the type. in case of ((Lambda..) ?...)
      * the application may also be a lambda! *)
     force_ty false false metasenv subst context orig_t res ty_he expty
  | NCic.Implicit `Vector::tl ->
      let has_some_more_pis x =
        match NCicReduction.whd ~subst context x with
        |  NCic.Meta _ | NCic.Appl (NCic.Meta _::_) -> false
        | _ -> true
      in
     (try
       aux metasenv subst args_so_far he ty_he tl
      with
      | Uncertain _
      | RefineFailure _ as exc when has_some_more_pis ty_he ->
          (try
           aux metasenv subst args_so_far he ty_he
            (NCic.Implicit `Term :: NCic.Implicit `Vector :: tl)
          with
           Uncertain msg | RefineFailure msg -> raise (wrap_exc msg exc))
     | RefineFailure msg when not (has_some_more_pis ty_he) ->
        (* instantiating the head could change the has_some_more_pis flag *)
        raise (Uncertain msg))
  | arg::tl ->
      match NCicReduction.whd ~subst context ty_he with 
      | C.Prod (_,s,t) ->
          let metasenv, subst, arg, _ = 
            typeof rdb ~localise metasenv subst context arg (Some s) in
          let t = NCicSubstitution.subst ~avoid_beta_redexes:true arg t in
          aux metasenv subst (arg :: args_so_far) he t tl
      | C.Meta _
      | C.Appl (C.Meta _ :: _) as t ->
          let metasenv, subst, arg, ty_arg = 
            typeof rdb ~localise metasenv subst context arg None in
          let name = guess_name subst context ty_arg in
          let metasenv, _, meta, _ = 
            NCicMetaSubst.mk_meta metasenv 
              ((name,C.Decl ty_arg) :: context) `IsType
          in
          let flex_prod = C.Prod (name, ty_arg, meta) in
          (* next line grants that ty_args is a type *)
          let metasenv,subst, flex_prod, _ =
           typeof rdb ~localise metasenv subst context flex_prod None in
(*
          pp (lazy ( "UNIFICATION in CTX:\n"^ 
            NCicPp.ppcontext ~metasenv ~subst context
            ^ "\nOF: " ^
            NCicPp.ppterm ~metasenv ~subst ~context t ^  " === " ^
            NCicPp.ppterm ~metasenv ~subst ~context flex_prod ^ "\n"));
*)
          let metasenv, subst =
             try NCicUnification.unify rdb metasenv subst context t flex_prod 
             with exc -> raise (wrap_exc (lazy (localise orig_he, Printf.sprintf
              ("The term %s has an inferred type %s, but is applied to the" ^^
               " argument %s of type %s")
              (NCicPp.ppterm ~metasenv ~subst ~context he)
              (NCicPp.ppterm ~metasenv ~subst ~context t)
              (NCicPp.ppterm ~metasenv ~subst ~context arg)
              (NCicPp.ppterm ~metasenv ~subst ~context ty_arg))) 
                 (match exc with
                 | NCicUnification.UnificationFailure m -> 
                     NCicUnification.Uncertain m
                 | x -> x))
              (* XXX coerce to funclass *)
          in
          let meta = NCicSubstitution.subst ~avoid_beta_redexes:true arg meta in
          aux metasenv subst (arg :: args_so_far) he meta tl
      | C.Match (_,_,C.Meta _,_) 
      | C.Match (_,_,C.Appl (C.Meta _ :: _),_) 
      | C.Appl (C.Const (NReference.Ref (_, NReference.Fix _)) :: _) ->
          raise (Uncertain (lazy (localise orig_he, Printf.sprintf
            ("The term %s is here applied to %d arguments but expects " ^^
            "only %d arguments") (NCicPp.ppterm ~metasenv ~subst ~context he)
            (List.length args) (List.length args_so_far))))
      | ty ->
          let metasenv, subst, newhead, newheadty = 
            try_coercions rdb ~localise metasenv subst context
              (NCicUntrusted.mk_appl he (List.rev args_so_far)) orig_he ty
              (NCic.Prod ("_",NCic.Implicit `Term,NCic.Implicit `Term))
              false
              (RefineFailure (lazy (localise orig_he, Printf.sprintf
               ("The term %s is here applied to %d arguments but expects " ^^
               "only %d arguments") (NCicPp.ppterm ~metasenv ~subst ~context he)
               (List.length args) (List.length args_so_far))))
          in
           aux metasenv subst [] newhead newheadty (arg :: tl)
  (*D*)in outside true; rc with exc -> outside false; raise exc
  in
   (* We need to reverse the order of the new created metas since they
      are pushed on top of the metasenv in the wrong order *)
   let highest_meta = NCicMetaSubst.maxmeta () in
   let metasenv, subst, newhead, newheadty = 
    aux metasenv subst [] he ty_he args in
   let metasenv_old,metasenv_new =
    List.partition (fun (i,_) -> i <= highest_meta) metasenv
   in
    (List.rev metasenv_new) @ metasenv_old, subst, newhead, newheadty
  (*D*)in outside true; rc with exc -> outside false; raise exc
;;

let rec first f l1 l2 =
  match l1,l2 with
  | x1::tl1, x2::tl2 -> 
      (try f x1 x2 with Not_found -> first f tl1 tl2)
  | _ -> raise Not_found
;;

let rec find add dt t =
  if dt == add then t
  else
    let dl, l = 
      match dt, t with
      | C.Meta (_,(_,C.Ctx dl)), C.Meta (_,(_,C.Ctx l))
      | C.Appl dl,C.Appl l -> dl,l
      | C.Lambda (_,ds,dt), C.Lambda (_,s,t) 
      | C.Prod (_,ds,dt), C.Prod (_,s,t) -> [ds;dt],[s;t]
      | C.LetIn (_,ds,db,dt), C.LetIn (_,s,b,t) -> [ds;db;dt],[s;b;t] 
      | C.Match (_,dot,dt,dl),  C.Match (_,ot,t,l) -> (dot::dt::dl),(ot::t::l)
      | _ -> raise Not_found
    in
      first (find add) dl l
;;

let relocalise old_localise dt t add = 
  old_localise 
    (try find add dt t with Not_found -> assert false)
;;

let undebruijnate inductive ref t rev_fl =
  let len = List.length rev_fl in 
  NCicSubstitution.psubst (fun x -> x) 
   (HExtlib.list_mapi 
      (fun (_,_,rno,_,_,_) i -> 
         let i = len - i - 1 in
         NCic.Const 
           (if inductive then NReference.mk_fix i rno ref
            else NReference.mk_cofix i ref))
      rev_fl)
    t
;; 


let typeof_obj 
  rdb ?(localise=fun _ -> Stdpp.dummy_loc) (uri,height,metasenv,subst,obj)
= 
  match obj with 
  | C.Constant (relevance, name, bo, ty, attr) ->
       let metasenv, subst, ty = 
         check_type rdb ~localise metasenv subst [] ty in
       let metasenv, subst, bo, ty, height = 
         match bo with
         | Some bo ->
             let metasenv, subst, bo, ty = 
               typeof rdb ~localise metasenv subst [] bo (Some ty) in
             let height = (* XXX recalculate *) height in
               metasenv, subst, Some bo, ty, height
         | None -> metasenv, subst, None, ty, 0
       in
       uri, height, metasenv, subst, 
         C.Constant (relevance, name, bo, ty, attr)
  | C.Fixpoint (inductive, fl, attr) -> 
      let len = List.length fl in
      let types, metasenv, subst, rev_fl =
        List.fold_left
         (fun (types, metasenv, subst, fl) (relevance,name,k,ty,bo) ->
           let metasenv, subst, ty = 
             check_type rdb ~localise metasenv subst [] ty in
           let dbo = NCicTypeChecker.debruijn uri len [] ~subst bo in
           let localise = relocalise localise dbo bo in
            (name,C.Decl ty)::types,
              metasenv, subst, (relevance,name,k,ty,dbo,localise)::fl
         ) ([], metasenv, subst, []) fl (* XXX kl rimosso nel nucleo *)
      in
      let metasenv, subst, fl = 
        List.fold_left 
          (fun (metasenv,subst,fl) (relevance,name,k,ty,dbo,localise) ->
            let metasenv, subst, dbo, ty = 
              typeof rdb ~localise metasenv subst types dbo (Some ty)
            in
            metasenv, subst, (relevance,name,k,ty,dbo)::fl)
          (metasenv, subst, []) rev_fl
      in
      let height = (* XXX recalculate *) height in
      let fl =
        List.map 
          (fun (relevance,name,k,ty,dbo) ->
            let bo = 
              undebruijnate inductive 
               (NReference.reference_of_spec uri 
                 (if inductive then NReference.Fix (0,k,0) 
                  else NReference.CoFix 0)) dbo rev_fl
            in
              relevance,name,k,ty,bo)
          fl
      in
       uri, height, metasenv, subst, 
         C.Fixpoint (inductive, fl, attr)
  | C.Inductive (ind, leftno, itl, attr) ->
     let len = List.length itl in
     let metasenv,subst,rev_itl,tys =
      List.fold_left
       (fun (metasenv,subst,res,ctx) (relevance,n,ty,cl) ->
          let metasenv, subst, ty = 
            check_type rdb ~localise metasenv subst [] ty in
          metasenv,subst,(relevance,n,ty,cl)::res,(n,NCic.Decl ty)::ctx
       ) (metasenv,subst,[],[]) itl in
     let metasenv,subst,itl,_ =
      List.fold_left
       (fun (metasenv,subst,res,i) (it_relev,n,ty,cl) ->
         let context,ty_sort = NCicReduction.split_prods ~subst [] ~-1 ty in
         let sx_context_ty_rev,_= HExtlib.split_nth leftno (List.rev context) in
         let metasenv,subst,cl =
          List.fold_right
           (fun (k_relev,n,te) (metasenv,subst,res) ->
	     let k_relev =
              try snd (HExtlib.split_nth leftno k_relev)
              with Failure _ -> k_relev in
             let te = NCicTypeChecker.debruijn uri len [] ~subst te in
             let metasenv, subst, te = 
               check_type rdb ~localise metasenv subst tys te in
             let context,te = NCicReduction.split_prods ~subst tys leftno te in
             let _,chopped_context_rev =
              HExtlib.split_nth (List.length tys) (List.rev context) in
             let sx_context_te_rev,_ =
              HExtlib.split_nth leftno chopped_context_rev in
             let metasenv,subst,_ =
              try
               List.fold_left2
                (fun (metasenv,subst,context) item1 item2 ->
                  let (metasenv,subst),convertible =
                   try
                    match item1,item2 with
                      (n1,C.Decl ty1),(n2,C.Decl ty2) ->
                        if n1 = n2 then
                         NCicUnification.unify rdb ~test_eq_only:true metasenv
                          subst context ty1 ty2,true
                        else
                         (metasenv,subst),false
                    | (n1,C.Def (bo1,ty1)),(n2,C.Def (bo2,ty2)) ->
                        if n1 = n2 then
                         let metasenv,subst =
                          NCicUnification.unify rdb ~test_eq_only:true metasenv
                           subst context ty1 ty2
                         in
                          NCicUnification.unify rdb ~test_eq_only:true metasenv
                           subst context bo1 bo2,true
                        else
                         (metasenv,subst),false
                    | _,_ -> (metasenv,subst),false
                   with
                   | NCicUnification.Uncertain _
                   | NCicUnification.UnificationFailure _ ->
                      (metasenv,subst),false
                  in
                   let term2 =
                    match item2 with
                       _,C.Decl t -> t
                     | _,C.Def (b,_) -> b in
                   if not convertible then
                    raise (RefineFailure (lazy (localise term2,
                     ("Mismatch between the left parameters of the constructor " ^
                      "and those of its inductive type"))))
                   else
                    metasenv,subst,item1::context
                ) (metasenv,subst,tys) sx_context_ty_rev sx_context_te_rev
              with Invalid_argument "List.fold_left2" -> assert false in
             let metasenv, subst =
                let rec aux context (metasenv,subst) = function
                  | NCic.Meta _ -> metasenv, subst
                  | NCic.Implicit _ -> metasenv, subst
                  | NCic.Appl (NCic.Rel i :: args) as t
                      when i > List.length context - len ->
                      let lefts, _ = HExtlib.split_nth leftno args in
                      let ctxlen = List.length context in
                      let (metasenv, subst), _ = 
                        List.fold_left
                        (fun ((metasenv, subst),l) arg ->
                          NCicUnification.unify rdb 
                           ~test_eq_only:true metasenv subst context arg 
                             (NCic.Rel (ctxlen - len - l)), l+1
                          )
                        ((metasenv, subst), 0) lefts
                      in
                      metasenv, subst
                  | t -> NCicUtils.fold (fun e c -> e::c) context aux
                  (metasenv,subst) t
                in
               aux context (metasenv,subst) te
             in
             let con_sort= NCicTypeChecker.typeof ~subst ~metasenv context te in
              (match
                NCicReduction.whd ~subst context con_sort,
                NCicReduction.whd ~subst [] ty_sort
               with
                  (C.Sort (C.Type u1) as s1), (C.Sort (C.Type u2) as s2) ->
                   if not (NCicEnvironment.universe_leq u1 u2) then
                    raise
                     (RefineFailure
                       (lazy(localise te, "The type " ^
                         NCicPp.ppterm ~metasenv ~subst ~context s1 ^
                         " of the constructor is not included in the inductive"^
                         " type sort " ^
                         NCicPp.ppterm ~metasenv ~subst ~context s2)))
                | C.Sort _, C.Sort C.Prop
                | C.Sort _, C.Sort C.Type _ -> ()
                | _, _ ->
                   raise
                    (RefineFailure
                      (lazy (localise te,
                        "Wrong constructor or inductive arity shape"))));
              (* let's check also the positivity conditions *)
              if 
               not
               (NCicTypeChecker.are_all_occurrences_positive
                 ~subst context uri leftno (i+leftno) leftno (len+leftno) te) 
              then
                raise
                  (RefineFailure
                    (lazy (localise te,
                      "Non positive occurence in " ^
                        NCicPp.ppterm ~metasenv ~subst ~context te)))
              else
               let relsno = List.length itl + leftno in
               let te = 
                 NCicSubstitution.psubst 
                  (fun i ->
                    if i <= leftno  then
                     NCic.Rel i
                    else
                     NCic.Const (NReference.reference_of_spec uri
                      (NReference.Ind (ind,relsno - i,leftno))))
                  (HExtlib.list_seq 1 (relsno+1))
                   te in
               let te =
                List.fold_right
                 (fun (name,decl) te ->
                   match decl with
                      NCic.Decl ty -> NCic.Prod (name,ty,te)
                    | NCic.Def (bo,ty) -> NCic.LetIn (name,ty,bo,te)
                 ) sx_context_te_rev te
               in
                metasenv,subst,(k_relev,n,te)::res
              ) cl (metasenv,subst,[])
         in
          metasenv,subst,(it_relev,n,ty,cl)::res,i+1
       ) (metasenv,subst,[],1) rev_itl
     in
      uri, height, metasenv, subst, C.Inductive (ind, leftno, itl, attr)
;;

(* vim:set foldmethod=marker: *)
