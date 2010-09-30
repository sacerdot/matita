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

module Ref = NReference

let nuri_of_ouri o = NUri.uri_of_string (UriManager.string_of_uri o);;

let mk_type n = 
 [`Type, NUri.uri_of_string ("cic:/matita/pts/Type"^string_of_int n^".univ")]
;;

let mk_cprop n = 
 [`CProp, NUri.uri_of_string ("cic:/matita/pts/Type"^string_of_int n^".univ")]
;;

let is_proof_irrelevant context ty =
  match
    CicReduction.whd context
     (fst (CicTypeChecker.type_of_aux' [] context ty CicUniv.oblivion_ugraph))
  with
     Cic.Sort Cic.Prop -> true
   | Cic.Sort _ -> false
   | _ -> assert false
;;

exception InProp;;

let get_relevance ty =
 let rec aux context ty =
  match CicReduction.whd context ty with
      Cic.Prod (n,s,t) ->
        not (is_proof_irrelevant context s)::aux (Some (n,Cic.Decl s)::context) t
    | _ -> []
 in aux [] ty
(*    | ty -> if is_proof_irrelevant context ty then raise InProp else []
 in
   try aux [] ty
   with InProp -> []*)
;;

(* porcatissima *)
type reference = Ref of NUri.uri * NReference.spec
let reference_of_ouri u indinfo =
  let u = nuri_of_ouri u in
  NReference.reference_of_string
   (NReference.string_of_reference (Obj.magic (Ref (u,indinfo))))
;;

type ctx = 
  | Ce of (NCic.hypothesis * NCic.obj list) Lazy.t
  | Fix of (Ref.reference * string * NCic.term) Lazy.t

let strictify =
 function
    Ce l -> `Ce (Lazy.force l)
  | Fix l -> `Fix (Lazy.force l)
;;

let count_vars vars =
 List.length 
  (List.filter (fun v -> 
     match fst (CicEnvironment.get_obj CicUniv.oblivion_ugraph v) with
        Cic.Variable (_,Some _,_,_,_) -> false
      | Cic.Variable (_,None,_,_,_) -> true
      | _ -> assert false) vars)
;;


(***** A function to restrict the context of a term getting rid of unsed
       variables *******)

let restrict octx ctx ot =
 let odummy = Cic.Implicit None in
 let dummy = NCic.Meta (~-1,(0,NCic.Irl 0)) in
 let rec aux m acc ot t =
  function
     [],[] -> (ot,t),acc
   | ohe::otl as octx,he::tl ->
      if CicTypeChecker.does_not_occur octx 0 1 ot then
       aux (m+1) acc (CicSubstitution.subst odummy ot)
        (NCicSubstitution.subst dummy t) (otl,tl)
      else
       (match ohe,strictify he with
           None,_ -> assert false
         | Some (name,Cic.Decl oty),`Ce ((name', NCic.Decl ty),objs) ->
            aux (m+1) ((m+1,objs,None)::acc) (Cic.Lambda (name,oty,ot))
             (NCic.Lambda (name',ty,t)) (otl,tl)
         | Some (name,Cic.Decl oty),`Fix (ref,name',ty) ->
            aux (m+1) ((m+1,[],Some ref)::acc) (Cic.Lambda (name,oty,ot))
             (NCic.Lambda (name',ty,t)) (otl,tl)
         | Some (name,Cic.Def (obo,oty)),`Ce ((name', NCic.Def (bo,ty)),objs) ->
            aux (m+1) ((m+1,objs,None)::acc) (Cic.LetIn (name,obo,oty,ot))
             (NCic.LetIn (name',bo,ty,t)) (otl,tl)
         | _,_ -> assert false)
   | _,_ -> assert false in
 let rec split_lambdas_and_letins octx ctx infos (ote,te) =
  match infos, ote, te with
     ([], _, _) -> octx,ctx,ote
   | ((_,objs,None)::tl, Cic.Lambda(name,oso,ota), NCic.Lambda(name',so,ta)) ->
       split_lambdas_and_letins ((Some(name,(Cic.Decl oso)))::octx)
        (Ce (lazy ((name',NCic.Decl so),objs))::ctx) tl (ota,ta)
   | ((_,_,Some r)::tl,Cic.Lambda(name,oso,ota),NCic.Lambda(name',so,ta)) ->
       split_lambdas_and_letins ((Some(name,(Cic.Decl oso)))::octx)
        (Fix (lazy (r,name',so))::ctx) tl (ota,ta)
   | ((_,objs,None)::tl,Cic.LetIn(name,obo,oty,ota),NCic.LetIn(nam',bo,ty,ta))->
       split_lambdas_and_letins ((Some (name,(Cic.Def (obo,oty))))::octx)
        (Ce (lazy ((nam',NCic.Def (bo,ty)),objs))::ctx) tl (ota,ta)
   | (_, _, _) -> assert false
 in
  let long_t,infos = aux 0 [] ot dummy (octx,ctx) in
  let clean_octx,clean_ctx,clean_ot= split_lambdas_and_letins [] [] infos long_t
  in
(*prerr_endline ("RESTRICT PRIMA: " ^ CicPp.pp ot (List.map (function None -> None | Some (name,_) -> Some name) octx));
prerr_endline ("RESTRICT DOPO: " ^ CicPp.pp clean_ot (List.map (function None -> None | Some (name,_) -> Some name) clean_octx));
*)
   clean_octx,clean_ctx,clean_ot, List.map (fun (rel,_,_) -> rel) infos
;;


(**** The translation itself ****)

let cn_to_s = function
  | Cic.Anonymous -> "_"
  | Cic.Name s -> s
;;

let splat mk_pi ctx t =
  List.fold_left
    (fun (t,l) c -> 
      match strictify c with
      | `Ce ((name, NCic.Def (bo,ty)),l') -> NCic.LetIn (name, ty, bo, t),l@l'
      | `Ce ((name, NCic.Decl ty),l') when mk_pi -> NCic.Prod (name, ty, t),l@l'
      | `Ce ((name, NCic.Decl ty),l') -> NCic.Lambda (name, ty, t),l@l'
      | `Fix (_,name,ty) when mk_pi -> NCic.Prod (name, ty, t),l
      | `Fix (_,name,ty) -> NCic.Lambda (name,ty,t),l)
    (t,[]) ctx
;;

let osplat mk_pi ctx t =
  List.fold_left
    (fun t c -> 
      match c with
      | Some (name, Cic.Def (bo,ty)) -> Cic.LetIn (name, ty, bo, t)
      | Some (name, Cic.Decl ty) when mk_pi -> Cic.Prod (name, ty, t)
      | Some (name, Cic.Decl ty) -> Cic.Lambda (name, ty, t)
      | None -> assert false)
    t ctx
;;

let context_tassonomy ctx = 
    let rec split inner acc acc1 = function 
      | Ce _ :: tl when inner -> split inner (acc+1) (acc1+1) tl
      | Fix _ ::tl -> split false acc (acc1+1) tl
      | _ as l ->
        let only_decl () =
         List.filter
          (function
              Ce _ as ce ->
               (match strictify ce with
                   `Ce ((_, NCic.Decl _),_) -> true
                 | _ -> false)
            | Fix _ -> true) l
        in
         acc, List.length l, lazy (List.length (only_decl ())), acc1
    in
      split true 0 1 ctx
;;

let splat_args_for_rel ctx t ?rels n_fix =
  let rels =
   match rels with
      Some rels -> rels
    | None ->
       let rec mk_irl = function 0 -> [] | n -> n::mk_irl (n - 1) in
        mk_irl (List.length ctx)
  in
  let bound, free, _, primo_ce_dopo_fix = context_tassonomy ctx in
  if free = 0 then t 
  else
    let rec aux = function
      | n,_ when n = bound + n_fix -> []
      | n,he::tl -> 
         (match strictify (List.nth ctx (n-1)) with
          | `Fix (refe, _, _) when n < primo_ce_dopo_fix ->
             NCic.Const refe :: aux (n-1,tl)
          | `Fix _ | `Ce ((_, NCic.Decl _),_) ->
              NCic.Rel (he - n_fix)::aux(n-1,tl)
          | `Ce ((_, NCic.Def _),_) -> aux (n-1,tl))
      | _,_ -> assert false
    in
   let args = aux (List.length ctx,rels) in
    match args with
       [] -> t
     | _::_ -> NCic.Appl (t::args)
;;

let splat_args ctx t n_fix rels =
  let bound, _, _, primo_ce_dopo_fix = context_tassonomy ctx in
  if ctx = [] then t
  else
   let rec aux = function
     | 0,[] -> []
     | n,he::tl -> 
        (match strictify (List.nth ctx (n-1)) with
         | `Ce ((_, NCic.Decl _),_) when n <= bound ->
             NCic.Rel he:: aux (n-1,tl)
         | `Fix (refe, _, _) when n < primo_ce_dopo_fix ->
            splat_args_for_rel ctx (NCic.Const refe) ~rels n_fix :: aux (n-1,tl)
         | `Fix _ | `Ce((_, NCic.Decl _),_)-> NCic.Rel (he - n_fix)::aux(n-1,tl)
         | `Ce ((_, NCic.Def _),_) -> aux (n - 1,tl)
        ) 
     | _,_ -> assert false
   in
   let args = aux  (List.length ctx,rels) in
    match args with
       [] -> t
     | _::_ -> NCic.Appl (t::args)
;;

exception Nothing_to_do;;

let fix_outty curi tyno t context outty =
 let leftno,rightno =
  match fst (CicEnvironment.get_obj CicUniv.oblivion_ugraph curi) with
     Cic.InductiveDefinition (tyl,_,leftno,_) ->
      let _,_,arity,_ = List.nth tyl tyno in
      let rec count_prods leftno context arity =
       match leftno, CicReduction.whd context arity with
          0, Cic.Sort _ -> 0
        | 0, Cic.Prod (name,so,ty) ->
           1 + count_prods 0 (Some (name, Cic.Decl so)::context) ty
        | _, Cic.Prod (name,so,ty) ->
           count_prods (leftno - 1) (Some (name, Cic.Decl so)::context) ty
        | _,_ -> assert false
      in
(*prerr_endline (UriManager.string_of_uri curi);
prerr_endline ("LEFTNO: " ^ string_of_int leftno ^ "  " ^ CicPp.ppterm arity);*)
       leftno, count_prods leftno [] arity
   | _ -> assert false in
 let ens,args =
  let tty,_= CicTypeChecker.type_of_aux' [] context t CicUniv.oblivion_ugraph in
  match CicReduction.whd context tty with
     Cic.MutInd (_,_,ens) -> ens,[]
   | Cic.Appl (Cic.MutInd (_,_,ens)::args) ->
      ens,fst (HExtlib.split_nth leftno args)
   | _ -> assert false
 in
  let rec aux n irl context outsort =
   match n, CicReduction.whd context outsort with
      0, Cic.Prod _ -> raise Nothing_to_do
    | 0, _ ->
       let irl = List.rev irl in
       let ty = CicSubstitution.lift rightno (Cic.MutInd (curi,tyno,ens)) in
       let ty =
        if args = [] && irl = [] then ty
        else
         Cic.Appl (ty::(List.map (CicSubstitution.lift rightno) args)@irl) in
       let he = CicSubstitution.lift (rightno + 1) outty in
       let t =
        if irl = [] then he
        else Cic.Appl (he::List.map (CicSubstitution.lift 1) irl)
       in
        Cic.Lambda (Cic.Anonymous, ty, t)
    | n, Cic.Prod (name,so,ty) ->
       let ty' =
        aux (n - 1) (Cic.Rel n::irl) (Some (name, Cic.Decl so)::context) ty
       in
        Cic.Lambda (name,so,ty')
    | _,_ -> assert false
  in
(*prerr_endline ("RIGHTNO = " ^ string_of_int rightno ^ " OUTTY = " ^ CicPp.ppterm outty);*)
   let outsort =
    fst (CicTypeChecker.type_of_aux' [] context outty CicUniv.oblivion_ugraph)
   in
    try aux rightno [] context outsort
    with Nothing_to_do -> outty
(*prerr_endline (CicPp.ppterm outty ^ " <==> " ^ CicPp.ppterm outty');*)
;;

let fix_outtype t =
 let module C = Cic in
 let rec aux context =
  function
     C.Rel _ as t -> t
   | C.Var (uri,exp_named_subst) ->
      let exp_named_subst' =
       List.map (function i,t -> i, (aux context t)) exp_named_subst in
        C.Var (uri,exp_named_subst')
   | C.Implicit _
   | C.Meta _ -> assert false
   | C.Sort _ as t -> t
   | C.Cast (v,t) -> C.Cast (aux context v, aux context t)
   | C.Prod (n,s,t) ->
        C.Prod (n, aux context s, aux ((Some (n, C.Decl s))::context) t)
   | C.Lambda (n,s,t) ->
       C.Lambda (n, aux context s, aux ((Some (n, C.Decl s))::context) t)
   | C.LetIn (n,s,ty,t) ->
      C.LetIn
       (n, aux context s, aux context ty,
        aux ((Some (n, C.Def(s,ty)))::context) t)
   | C.Appl l -> C.Appl (List.map (aux context) l)
   | C.Const (uri,exp_named_subst) ->
      let exp_named_subst' =
       List.map (function i,t -> i, (aux context t)) exp_named_subst
      in
       C.Const (uri,exp_named_subst')
   | C.MutInd (uri,tyno,exp_named_subst) ->
      let exp_named_subst' =
       List.map (function i,t -> i, (aux context t)) exp_named_subst
      in
       C.MutInd (uri, tyno, exp_named_subst')
   | C.MutConstruct (uri,tyno,consno,exp_named_subst) ->
      let exp_named_subst' =
       List.map (function i,t -> i, (aux context t)) exp_named_subst
      in
       C.MutConstruct (uri, tyno, consno, exp_named_subst')
   | C.MutCase (uri, tyno, outty, term, patterns) ->
      let outty = fix_outty uri tyno term context outty in
       C.MutCase (uri, tyno, aux context outty,
        aux context term, List.map (aux context) patterns)
   | C.Fix (funno, funs) ->
      let tys,_ =
        List.fold_left
          (fun (types,len) (n,_,ty,_) ->
            ((Some (C.Name n,(C.Decl (CicSubstitution.lift len ty)))))::types,
              len+1
	  ) ([],0) funs
      in
       C.Fix (funno,
        List.map
         (fun (name, indidx, ty, bo) ->
           (name, indidx, aux context ty, aux (tys@context) bo)
         ) funs
      )
   | C.CoFix (funno, funs) ->
      let tys,_ =
        List.fold_left
          (fun (types,len) (n,ty,_) ->
            ((Some (C.Name n,(C.Decl (CicSubstitution.lift len ty)))))::types,
              len+1
	  ) ([],0) funs
      in
       C.CoFix (funno,
        List.map
         (fun (name, ty, bo) ->
           (name, aux context ty, aux (tys@context) bo)
         ) funs
       )
 in
  aux [] t
;;

let get_fresh,reset_seed =
 let seed = ref 0 in
  (function () ->
   incr seed;
   string_of_int !seed),
  (function () -> seed := 0)
;;

exception NotSimilar 
let alpha t1 t2 ref ref' =
  let rec aux t1 t2 = match t1,t2 with
    | NCic.Rel n, NCic.Rel m when n=m -> ()
    | NCic.Appl l1, NCic.Appl l2 -> List.iter2 aux l1 l2
    | NCic.Lambda (_,s1,t1), NCic.Lambda (_,s2,t2) 
    | NCic.Prod (_,s1,t1), NCic.Prod (_,s2,t2) -> aux s1 s2; aux t1 t2
    | NCic.LetIn (_,s1,ty1,t1), NCic.LetIn (_,s2,ty2,t2) -> 
         aux s1 s2; aux ty1 ty2; aux t1 t2
    | NCic.Const (NReference.Ref (uu1,xp1)), 
      NCic.Const (NReference.Ref (uu2,xp2))  when 
         let NReference.Ref (u1,_) = ref in
         let NReference.Ref (u2,_) = ref' in
           NUri.eq uu1 u1 && NUri.eq uu2 u2 && xp1 = xp2
      -> ()
    | NCic.Const r1, NCic.Const r2 when NReference.eq r1 r2 -> ()
    | NCic.Meta _,NCic.Meta _ -> ()
    | NCic.Implicit _,NCic.Implicit _ -> ()
    | NCic.Sort x,NCic.Sort y when x=y -> ()
    | NCic.Match (_,t1,t11,tl1), NCic.Match (_,t2,t22,tl2) -> 
         aux t1 t2;aux t11 t22;List.iter2 aux tl1 tl2 
    | _-> raise NotSimilar
  in
  try aux t1 t2; true  with NotSimilar -> false
;;

exception Found of NReference.reference;;
let cache = Hashtbl.create 313;; 
let same_obj ref ref' =
 function
  | (_,_,_,_,NCic.Fixpoint (b1,l1,_)), (_,_,_,_,NCic.Fixpoint (b2,l2,_))
    when List.for_all2 (fun (_,_,_,ty1,bo1) (_,_,_,ty2,bo2) -> 
       alpha ty1 ty2 ref ref' && alpha bo1 bo2 ref ref') l1 l2 && b1=b2->
     true
  | _ -> false
;;
let find_in_cache name obj ref =
 try
  List.iter
   (function (ref',obj') ->
     let recno, fixno =
      match ref with
         NReference.Ref (_,NReference.Fix (fixno,recno,_)) -> recno,fixno
       | NReference.Ref (_,NReference.CoFix (fixno)) -> ~-1,fixno
       | _ -> assert false in
     let recno',fixno' =
      match ref' with
         NReference.Ref (_,NReference.Fix (fixno',recno,_)) -> recno,fixno'
       | NReference.Ref (_,NReference.CoFix (fixno')) -> ~-1,fixno'
       | _ -> assert false in
     if recno = recno' && fixno = fixno' && same_obj ref ref' (obj,obj') then (
(*
prerr_endline ("!!!!!!!!!!! CACHE HIT !!!!!!!!!!\n" ^
NReference.string_of_reference ref ^ "\n" ^
NReference.string_of_reference ref' ^ "\n"); 
 *)
       raise (Found ref'));
(*
prerr_endline ("CACHE SAME NAME: " ^ NReference.string_of_reference ref ^ " <==> " ^ NReference.string_of_reference ref');
 *)
  ) (Hashtbl.find_all cache name);
(*   prerr_endline "<<< CACHE MISS >>>";   *)
  begin
    match obj, ref with 
    | (_,_,_,_,NCic.Fixpoint (true,fl,_)) , 
      NReference.Ref (_,NReference.Fix _) ->
       ignore(List.fold_left (fun i (_,name,rno,_,_) ->
         let ref = NReference.mk_fix i rno ref in
         Hashtbl.add cache name (ref,obj);
         i+1
       ) 0 fl)
    | (_,_,_,_,NCic.Fixpoint (false,fl,_)) , 
      NReference.Ref (_,NReference.CoFix _) ->
       ignore(List.fold_left (fun i (_,name,_,_,_) ->
         let ref = NReference.mk_cofix i ref in
         Hashtbl.add cache name (ref,obj);
         i+1
       ) 0 fl)
    | _ -> assert false
  end;
  None
 with Found ref -> Some ref
;;

let cache1 = UriManager.UriHashtbl.create 313;;
let rec get_height =
   function u ->
     try
       UriManager.UriHashtbl.find cache1 u
     with
      Not_found ->
        let h = ref 0 in
         let res =
          match fst (CicEnvironment.get_obj CicUniv.oblivion_ugraph u) with
             Cic.Constant (_,Some bo,ty,params,_)
           | Cic.Variable (_,Some bo,ty,params,_) ->
               ignore (height_of_term ~h bo);
               ignore (height_of_term ~h ty);
               List.iter (function uri -> h := max !h (get_height uri)) params;
               1 + !h
           | _ -> 0
         in
           UriManager.UriHashtbl.add cache1 u res;
           res
and height_of_term ?(h=ref 0) t =
 let rec aux =
  function
   Cic.Rel _
 | Cic.Sort _ -> ()
 | Cic.Implicit _ -> assert false
 | Cic.Var (uri,exp_named_subst)
 | Cic.Const (uri,exp_named_subst)
 | Cic.MutInd (uri,_,exp_named_subst)
 | Cic.MutConstruct (uri,_,_,exp_named_subst) ->
    h := max !h (get_height uri);
    List.iter (function (_,t) -> aux t) exp_named_subst
 | Cic.Meta (_,l) -> List.iter (function None -> () | Some t -> aux t) l
 | Cic.Cast (t1,t2)
 | Cic.Prod (_,t1,t2)
 | Cic.Lambda (_,t1,t2) -> aux t1; aux t2
 | Cic.LetIn (_,s,ty,t) -> aux s; aux ty; aux t
 | Cic.Appl l -> List.iter aux l
 | Cic.MutCase (_,_,outty,t,pl) -> aux outty; aux t; List.iter aux pl
 | Cic.Fix (_, fl) -> List.iter (fun (_, _, ty, bo) ->  aux ty; aux bo) fl; incr h
 | Cic.CoFix (_, fl) -> List.iter (fun (_, ty, bo) ->  aux ty; aux bo) fl; incr h
 in
   aux t;
   1 + !h
;;

  (* k=true if we are converting a term to be pushed in a ctx or if we are
            converting the type of a fix;
     k=false if we are converting a term to be put in the body of a fix;
     in the latter case, we must permute Rels since the Fix abstraction will
     preceed its lefts parameters; in the former case, there is nothing to
     permute *)
  let rec aux k octx (ctx : ctx list) n_fix uri = function
    | Cic.CoFix _ as cofix ->
        let octx,ctx,fix,rels = restrict octx ctx cofix in
        let cofixno,fl =
         match fix with Cic.CoFix (cofixno,fl)->cofixno,fl | _-> assert false in
        let buri = 
          UriManager.uri_of_string 
           (UriManager.buri_of_uri uri^"/"^
            UriManager.name_of_uri uri ^ "___" ^ get_fresh () ^ ".con")
        in
        let bctx, fixpoints_tys, tys, _ = 
          List.fold_right 
            (fun (name,ty,_) (bctx, fixpoints, tys, idx) -> 
              let ty, fixpoints_ty = aux true octx ctx n_fix uri ty in
              let r = reference_of_ouri buri(Ref.CoFix idx) in
              bctx @ [Fix (lazy (r,name,ty))],
               fixpoints_ty @ fixpoints,ty::tys,idx-1)
            fl ([], [], [], List.length fl-1)
        in
        let bctx = bctx @ ctx in
        let n_fl = List.length fl in
        let boctx,_ =
         List.fold_left
          (fun (types,len) (n,ty,_) ->
             (Some (Cic.Name n,(Cic.Decl (CicSubstitution.lift len ty)))::types,
              len+1)) (octx,0) fl
        in
        let fl, fixpoints =
          List.fold_right2 
            (fun (name,_,bo) ty  (l,fixpoints) -> 
               let bo, fixpoints_bo = aux false boctx bctx n_fl buri bo in
               let splty,fixpoints_splty = splat true ctx ty in
               let splbo,fixpoints_splbo = splat false ctx bo in
               (([],name,~-1,splty,splbo)::l),
               fixpoints_bo @ fixpoints_splty @ fixpoints_splbo @ fixpoints)
            fl tys ([],fixpoints_tys)
        in
        let obj = 
          nuri_of_ouri buri,0,[],[],
            NCic.Fixpoint (false, fl, (`Generated, `Definition, `Regular))
        in
        let r = reference_of_ouri buri (Ref.CoFix cofixno) in
        let obj,r =
         let _,name,_,_,_ = List.nth fl cofixno in
         match find_in_cache name obj r with
            Some r' -> [],r'
          | None -> [obj],r
        in
        splat_args ctx (NCic.Const r) n_fix rels, fixpoints @ obj
    | Cic.Fix _ as fix ->
        let octx,ctx,fix,rels = restrict octx ctx fix in
        let fixno,fl =
         match fix with Cic.Fix (fixno,fl) -> fixno,fl | _ -> assert false in
        let buri = 
          UriManager.uri_of_string 
           (UriManager.buri_of_uri uri^"/"^
            UriManager.name_of_uri uri ^ "___" ^ get_fresh () ^ ".con") in
        let height = height_of_term fix - 1 in
        let bad_bctx, fixpoints_tys, tys, _ = 
          List.fold_right 
            (fun (name,recno,ty,_) (bctx, fixpoints, tys, idx) -> 
              let ty, fixpoints_ty = aux true octx ctx n_fix uri ty in
              let r =  (* recno is dummy here, must be lifted by the ctx len *)
                reference_of_ouri buri (Ref.Fix (idx,recno,height)) 
              in
              bctx @ [Fix (lazy (r,name,ty))],
               fixpoints_ty@fixpoints,ty::tys,idx-1)
            fl ([], [], [], List.length fl-1)
        in
        let _, _, free_decls, _ = context_tassonomy (bad_bctx @ ctx) in
        let free_decls = Lazy.force free_decls in
        let bctx = 
          List.map (function ce -> match strictify ce with
            | `Fix (Ref.Ref (_,Ref.Fix (idx, recno,height)),name, ty) ->
              Fix (lazy (reference_of_ouri buri
                    (Ref.Fix (idx,recno+free_decls,height)),name,ty))
            | _ -> assert false) bad_bctx @ ctx
        in
        let n_fl = List.length fl in
        let boctx,_ =
         List.fold_left
          (fun (types,len) (n,_,ty,_) ->
             (Some (Cic.Name n,(Cic.Decl (CicSubstitution.lift len ty)))::types,
              len+1)) (octx,0) fl
        in
        let rno_fixno = ref 0 in
        let fl, fixpoints,_ =
          List.fold_right2 
            (fun (name,rno,oty,bo) ty (l,fixpoints,idx) -> 
               let bo, fixpoints_bo = aux false boctx bctx n_fl buri bo in
               let splty,fixpoints_splty = splat true ctx ty in
               let splbo,fixpoints_splbo = splat false ctx bo in
               let rno = rno + free_decls in
               if idx = fixno then rno_fixno := rno;
               ((get_relevance (osplat true octx oty),name,rno,splty,splbo)::l),
               fixpoints_bo@fixpoints_splty@fixpoints_splbo@fixpoints,idx+1)
            fl tys ([],fixpoints_tys,0)
        in
        let obj = 
          nuri_of_ouri buri,height,[],[],
            NCic.Fixpoint (true, fl, (`Generated, `Definition, `Regular)) in
(*prerr_endline ("H(" ^ UriManager.string_of_uri buri ^ ") = " ^ string_of_int * height);*)
        let r = reference_of_ouri buri (Ref.Fix (fixno,!rno_fixno,height)) in
        let obj,r =
         let _,name,_,_,_ = List.nth fl fixno in
         match find_in_cache name obj r with
            Some r' -> [],r'
          | None -> [obj],r
        in
        splat_args ctx (NCic.Const r) n_fix rels, fixpoints @ obj
    | Cic.Rel n ->
        let bound, _, _, primo_ce_dopo_fix = context_tassonomy ctx in
        (match List.nth ctx (n-1) with
        | Fix l when n < primo_ce_dopo_fix -> 
           let r,_,_ = Lazy.force l in
            splat_args_for_rel ctx (NCic.Const r) n_fix, []
        | Ce _ when n <= bound -> NCic.Rel n, []
        | Fix _ when n <= bound -> assert false
        | Fix _ | Ce _ when k = true -> NCic.Rel n, []
        | Fix _ | Ce _ -> NCic.Rel (n-n_fix), [])
    | Cic.Lambda (name, (s as old_s), t) ->
        let s, fixpoints_s = aux k octx ctx n_fix uri s in
        let s'_and_fixpoints_s' = lazy (aux true octx ctx n_fix uri old_s) in
        let ctx =
         Ce (lazy
          let s',fixpoints_s' = Lazy.force s'_and_fixpoints_s' in
           ((cn_to_s name, NCic.Decl s'),fixpoints_s'))::ctx in
        let octx = Some (name, Cic.Decl old_s) :: octx in
        let t, fixpoints_t = aux k octx ctx n_fix uri t in
        NCic.Lambda (cn_to_s name, s, t), fixpoints_s @ fixpoints_t
    | Cic.Prod (name, (s as old_s), t) ->
        let s, fixpoints_s = aux k octx ctx n_fix uri s in
        let s'_and_fixpoints_s' = lazy (aux true octx ctx n_fix uri old_s) in
        let ctx =
         Ce (lazy
          let s',fixpoints_s' = Lazy.force s'_and_fixpoints_s' in
           ((cn_to_s name, NCic.Decl s'),fixpoints_s'))::ctx in
        let octx = Some (name, Cic.Decl old_s) :: octx in
        let t, fixpoints_t = aux k octx ctx n_fix uri t in
        NCic.Prod (cn_to_s name, s, t), fixpoints_s @ fixpoints_t
    | Cic.LetIn (name, (te as old_te), (ty as old_ty), t) ->
        let te, fixpoints_s = aux k octx ctx n_fix uri te in
        let te_and_fixpoints_s' = lazy (aux true octx ctx n_fix uri old_te) in
        let ty, fixpoints_ty = aux k octx ctx n_fix uri ty in
        let ty_and_fixpoints_ty' = lazy (aux true octx ctx n_fix uri old_ty) in
        let ctx =
         Ce (lazy
          let te',fixpoints_s' = Lazy.force te_and_fixpoints_s' in
          let ty',fixpoints_ty' = Lazy.force ty_and_fixpoints_ty' in
          let fixpoints' = fixpoints_s' @ fixpoints_ty' in
           ((cn_to_s name, NCic.Def (te', ty')),fixpoints'))::ctx in
        let octx = Some (name, Cic.Def (old_te, old_ty)) :: octx in
        let t, fixpoints_t = aux k octx ctx n_fix uri t in
        NCic.LetIn (cn_to_s name, ty, te, t), 
        fixpoints_s @ fixpoints_t @ fixpoints_ty
    | Cic.Cast (t,ty) ->
        let t, fixpoints_t = aux k octx ctx n_fix uri t in
        let ty, fixpoints_ty = aux k octx ctx n_fix uri ty in
        NCic.LetIn ("cast", ty, t, NCic.Rel 1), fixpoints_t @ fixpoints_ty
    | Cic.Sort Cic.Prop -> NCic.Sort NCic.Prop,[]
    | Cic.Sort (Cic.CProp u) -> 
          NCic.Sort (NCic.Type (mk_cprop (CicUniv.get_rank u))),[]
    | Cic.Sort (Cic.Type u) -> 
          NCic.Sort (NCic.Type (mk_type (CicUniv.get_rank u))),[] 
    | Cic.Sort Cic.Set -> NCic.Sort (NCic.Type (mk_type 0)),[] 
       (* calculate depth in the univ_graph*)
    | Cic.Appl l -> 
        let l, fixpoints =
          List.fold_right 
             (fun t (l,acc) -> 
               let t, fixpoints = aux k octx ctx n_fix uri t in 
               (t::l,fixpoints@acc))
             l ([],[])
        in
        (match l with
        | (NCic.Appl l1)::l2 -> NCic.Appl (l1@l2), fixpoints
        | _ -> NCic.Appl l, fixpoints)
    | Cic.Const (curi, ens) -> 
       aux_ens k curi octx ctx n_fix uri ens
        (match fst(CicEnvironment.get_obj CicUniv.oblivion_ugraph curi) with
        | Cic.Constant (_,Some _,_,_,_) ->
               NCic.Const (reference_of_ouri curi (Ref.Def (get_height curi)))
        | Cic.Constant (_,None,_,_,_) ->
               NCic.Const (reference_of_ouri curi Ref.Decl)
        | _ -> assert false)
    | Cic.MutInd (curi, tyno, ens) -> 
       let is_inductive, lno =
        match fst (CicEnvironment.get_obj CicUniv.oblivion_ugraph curi) with
           Cic.InductiveDefinition ([],vars,lno,_) -> true, lno + count_vars vars
         | Cic.InductiveDefinition ((_,b,_,_)::_,vars,lno,_) -> b, lno + count_vars vars
         | _ -> assert false
       in
        aux_ens k curi octx ctx n_fix uri ens
         (NCic.Const (reference_of_ouri curi (Ref.Ind (is_inductive,tyno,lno))))
    | Cic.MutConstruct (curi, tyno, consno, ens) -> 
       let lno =
        match fst (CicEnvironment.get_obj CicUniv.oblivion_ugraph curi) with
           Cic.InductiveDefinition (_,vars,lno,_) -> lno + count_vars vars
         | _ -> assert false
       in
       aux_ens k curi octx ctx n_fix uri ens
        (NCic.Const (reference_of_ouri curi (Ref.Con (tyno,consno,lno))))
    | Cic.Var (curi, ens) ->
       (match fst (CicEnvironment.get_obj CicUniv.oblivion_ugraph curi) with
           Cic.Variable (_,Some bo,_,_,_) ->
            aux k octx ctx n_fix uri (CicSubstitution.subst_vars ens bo)
         | _ -> assert false)
    | Cic.MutCase (curi, tyno, outty, t, branches) ->
        let is_inductive,lno =
         match fst (CicEnvironment.get_obj CicUniv.oblivion_ugraph curi) with
            Cic.InductiveDefinition ([],vars,lno,_) -> true, lno + count_vars vars
          | Cic.InductiveDefinition ((_,b,_,_)::_,vars,lno,_) -> b, lno + count_vars vars
          | _ -> assert false in
        let r = reference_of_ouri curi (Ref.Ind (is_inductive,tyno,lno)) in
        let outty, fixpoints_outty = aux k octx ctx n_fix uri outty in
        let t, fixpoints_t = aux k octx ctx n_fix uri t in
        let branches, fixpoints =
          List.fold_right 
             (fun t (l,acc) -> 
               let t, fixpoints = aux k octx ctx n_fix uri t in 
               (t::l,fixpoints@acc))
             branches ([],[])
        in
        NCic.Match (r,outty,t,branches), fixpoints_outty@fixpoints_t@fixpoints
    | Cic.Implicit _ | Cic.Meta _ -> assert false
  and aux_ens k curi octx ctx n_fix uri ens he =
   match ens with
      [] -> he,[]
    | _::_ ->
      let params =
       match fst (CicEnvironment.get_obj CicUniv.oblivion_ugraph curi) with
          Cic.Constant (_,_,_,params,_)
        | Cic.InductiveDefinition (_,params,_,_) -> params
        | Cic.Variable _
        | Cic.CurrentProof _ -> assert false
      in
      let ens,objs =
       List.fold_right
        (fun luri (l,objs) ->
          match fst (CicEnvironment.get_obj CicUniv.oblivion_ugraph luri) with
             Cic.Variable (_,Some _,_,_,_) -> l, objs
           | Cic.Variable (_,None,_,_,_) ->
              let t = List.assoc luri ens in
              let t,o = aux k octx ctx n_fix uri t in
               t::l, o@objs
           | _ -> assert false
        ) params ([],[])
      in
       match ens with
          [] -> he,objs
        | _::_ -> NCic.Appl (he::ens),objs
;;

(* we are lambda-lifting also variables that do not occur *)
(* ctx does not distinguish successive blocks of cofix, since there may be no
 *   lambda separating them *)
let convert_term uri t = 
   aux false [] [] 0 uri t
;;

let cook mode vars t =
 let t = fix_outtype t in
 let varsno = List.length vars in
 let t = CicSubstitution.lift varsno t in
 let rec aux n acc l =
  let subst =
   snd(List.fold_left (fun (i,res) uri -> i+1,(uri,Cic.Rel i)::res) (1,[]) acc)
  in
  match l with
     [] -> CicSubstitution.subst_vars subst t
   | uri::uris ->
    let bo,ty =
     match fst (CicEnvironment.get_obj CicUniv.oblivion_ugraph uri) with
        Cic.Variable (_,bo,ty,_,_) ->
         HExtlib.map_option fix_outtype bo, fix_outtype ty
      | _ -> assert false in
    let ty = CicSubstitution.subst_vars subst ty in
    let bo = HExtlib.map_option (CicSubstitution.subst_vars subst) bo in
    let id = Cic.Name (UriManager.name_of_uri uri) in
    let t = aux (n-1) (uri::acc) uris in
     match bo,ty,mode with
        None,ty,`Lambda -> Cic.Lambda (id,ty,t)
      | None,ty,`Pi -> Cic.Prod (id,ty,t)
      | Some bo,ty,_ -> Cic.LetIn (id,bo,ty,t)
 in
  aux varsno [] vars
;;

let convert_obj_aux uri = function
 | Cic.Constant (name, None, ty, vars, _) ->
     let ty = cook `Pi vars ty in
     let nty, fixpoints = convert_term uri ty in
     assert(fixpoints = []);
     NCic.Constant (get_relevance ty, name, None, nty, (`Provided,`Theorem,`Regular)),
     fixpoints
 | Cic.Constant (name, Some bo, ty, vars, _) ->
     let bo = cook `Lambda vars bo in
     let ty = cook `Pi vars ty in
     let nbo, fixpoints_bo = convert_term uri bo in
     let nty, fixpoints_ty = convert_term uri ty in
     assert(fixpoints_ty = []);
     NCic.Constant (get_relevance ty, name, Some nbo, nty, (`Provided,`Theorem,`Regular)),
     fixpoints_bo @ fixpoints_ty
 | Cic.InductiveDefinition (itl,vars,leftno,_) -> 
     let ind = let _,x,_,_ = List.hd itl in x in
     let itl, fix_itl = 
       List.fold_right
         (fun (name, _, ty, cl) (itl,acc) ->
            let ty = cook `Pi vars ty in
            let nty, fix_ty = convert_term uri ty in
            let cl, fix_cl = 
              List.fold_right
               (fun (name, ty) (cl,acc) -> 
                 let ty = cook `Pi vars ty in
                 let nty, fix_ty = convert_term uri ty in
                 (get_relevance ty, name, nty)::cl, acc @ fix_ty)
               cl ([],[])
            in
            (get_relevance ty, name, nty, cl)::itl, fix_ty @ fix_cl @ acc)
         itl ([],[])
     in
     NCic.Inductive(ind, leftno + count_vars vars, itl, (`Provided, `Regular)),
     fix_itl
 | Cic.Variable _ 
 | Cic.CurrentProof _ -> assert false
;;

let convert_obj uri obj = 
  reset_seed ();
  let o, fixpoints = convert_obj_aux uri obj in
  let obj = nuri_of_ouri uri,get_height uri, [], [], o in
(*prerr_endline ("H(" ^ UriManager.string_of_uri uri ^ ") = " ^ string_of_int * (get_height uri));*)
  fixpoints @ [obj]
;;

let clear () =
  Hashtbl.clear cache;
  UriManager.UriHashtbl.clear cache1
;;

(*
let convert_context uri =
  let name_of = function Cic.Name s -> s | _ -> "_" in
  List.fold_right
    (function 
    | (Some (s, Cic.Decl t) as e) -> fun (nc,auxc,oc) ->
       let t, _ = aux true oc auxc 0 uri t in
       (name_of s, NCic.Decl t) :: nc, 
       Ce (lazy ((name_of s, NCic.Decl t),[])) :: auxc,  e :: oc
    | (Some (Cic.Name s, Cic.Def (t,ty)) as e) -> fun (nc,auxc,oc) ->
       let t, _ = aux true oc auxc 0 uri t in
       let t, _ = aux true oc auxc 0 uri ty in
       (name_of s, NCic.Def (t,ty)) :: nc, 
       Ce (lazy ((name_of s, NCic.Def (t,ty)),[])) :: auxc,  e :: oc
    | None -> nc, , e :: oc
;;

let convert_term uri ctx t = 
   aux false [] [] 0 uri t
;;
*)

let reference_of_oxuri u =
 let t = CicUtil.term_of_uri u in
 let t',l = convert_term (UriManager.uri_of_string "cic:/dummy/dummy.con") t in
  match t',l with
     NCic.Const nref, [] -> nref
   | _,_ -> assert false
;;

NCicCoercion.set_convert_term convert_term;;
Ncic2astMatcher.set_reference_of_oxuri reference_of_oxuri;;
NCicDisambiguate.set_reference_of_oxuri reference_of_oxuri;;
(* Why should we set them here? 
NCicBlob.set_reference_of_oxuri reference_of_oxuri;;
NCicProof.set_reference_of_oxuri reference_of_oxuri;;
*)
