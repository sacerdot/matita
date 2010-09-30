(* Copyright (C) 2003, HELM Team.
 * 
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

(* PROFILING *)
(*
let deref_counter = ref 0
let apply_subst_context_counter = ref 0
let apply_subst_metasenv_counter = ref 0
let lift_counter = ref 0
let subst_counter = ref 0
let whd_counter = ref 0
let are_convertible_counter = ref 0
let metasenv_length = ref 0
let context_length = ref 0
let reset_counters () =
 apply_subst_counter := 0;
 apply_subst_context_counter := 0;
 apply_subst_metasenv_counter := 0;
 lift_counter := 0;
 subst_counter := 0;
 whd_counter := 0;
 are_convertible_counter := 0;
 metasenv_length := 0;
 context_length := 0
let print_counters () =
  debug_print (lazy (Printf.sprintf
"apply_subst: %d
apply_subst_context: %d
apply_subst_metasenv: %d
lift: %d
subst: %d
whd: %d
are_convertible: %d
metasenv length: %d (avg = %.2f)
context length: %d (avg = %.2f)
"
  !apply_subst_counter !apply_subst_context_counter
  !apply_subst_metasenv_counter !lift_counter !subst_counter !whd_counter
  !are_convertible_counter !metasenv_length
  ((float !metasenv_length) /. (float !apply_subst_metasenv_counter))
  !context_length
  ((float !context_length) /. (float !apply_subst_context_counter))
  ))*)



exception MetaSubstFailure of string Lazy.t
exception Uncertain of string Lazy.t
exception AssertFailure of string Lazy.t
exception DeliftingARelWouldCaptureAFreeVariable;;

let debug_print = fun _ -> ()

type substitution = (int * (Cic.context * Cic.term)) list

(* 
let rec deref subst =
  let third _,_,a = a in
  function
      Cic.Meta(n,l) as t -> 
	(try 
	   deref subst
	     (CicSubstitution.subst_meta 
		l (third (CicUtil.lookup_subst n subst))) 
	 with 
	   CicUtil.Subst_not_found _ -> t)
    | t -> t
;;
*)

let lookup_subst = CicUtil.lookup_subst
;;

(* clean_up_meta take a metasenv and a term and make every local context
of each occurrence of a metavariable consistent with its canonical context, 
with respect to the hidden hipothesis *)

(*
let clean_up_meta subst metasenv t =
  let module C = Cic in
  let rec aux t =
  match t with
      C.Rel _
    | C.Sort _  -> t
    | C.Implicit _ -> assert false
    | C.Meta (n,l) as t ->
        let cc =
	  (try
	     let (cc,_) = lookup_subst n subst in cc
	   with CicUtil.Subst_not_found _ ->
	     try
	       let (_,cc,_) = CicUtil.lookup_meta n metasenv in cc
             with CicUtil.Meta_not_found _ -> assert false) in
	let l' = 
          (try 
	     List.map2
	       (fun t1 t2 ->
		  match t1,t2 with 
		      None , _ -> None
		    | _ , t -> t) cc l
	   with 
	       Invalid_argument _ -> assert false) in
        C.Meta (n, l')
    | C.Cast (te,ty) -> C.Cast (aux te, aux ty)
    | C.Prod (name,so,dest) -> C.Prod (name, aux so, aux dest)
    | C.Lambda (name,so,dest) -> C.Lambda (name, aux so, aux dest)
    | C.LetIn (name,so,dest) -> C.LetIn (name, aux so, aux dest)
    | C.Appl l -> C.Appl (List.map aux l)
    | C.Var (uri,exp_named_subst) ->
        let exp_named_subst' =
          List.map (fun (uri,t) -> (uri, aux t)) exp_named_subst
        in
        C.Var (uri, exp_named_subst')
    | C.Const (uri, exp_named_subst) ->
        let exp_named_subst' =
          List.map (fun (uri,t) -> (uri, aux t)) exp_named_subst
        in
        C.Const (uri, exp_named_subst')
    | C.MutInd (uri,tyno,exp_named_subst) ->
        let exp_named_subst' =
          List.map (fun (uri,t) -> (uri, aux t)) exp_named_subst
        in
        C.MutInd (uri, tyno, exp_named_subst')
    | C.MutConstruct (uri,tyno,consno,exp_named_subst) ->
        let exp_named_subst' =
          List.map (fun (uri,t) -> (uri, aux t)) exp_named_subst
        in
        C.MutConstruct (uri, tyno, consno, exp_named_subst')
    | C.MutCase (uri,tyno,out,te,pl) ->
        C.MutCase (uri, tyno, aux out, aux te, List.map aux pl)
    | C.Fix (i,fl) ->
       let fl' =
         List.map
          (fun (name,j,ty,bo) -> (name, j, aux ty, aux bo)) fl
       in
       C.Fix (i, fl')
    | C.CoFix (i,fl) ->
       let fl' =
         List.map
          (fun (name,ty,bo) -> (name, aux ty, aux bo)) fl
       in
       C.CoFix (i, fl')
 in
 aux t *)

(*** Functions to apply a substitution ***)

let apply_subst_gen ~appl_fun subst term =
 let rec um_aux =
  let module C = Cic in
  let module S = CicSubstitution in 
   function
      C.Rel _ as t -> t
    | C.Var (uri,exp_named_subst) ->
       let exp_named_subst' =
         List.map (fun (uri, t) -> (uri, um_aux t)) exp_named_subst
       in
       C.Var (uri, exp_named_subst')
    | C.Meta (i, l) -> 
        (try
          let (_, t,_) = lookup_subst i subst in
          um_aux (S.subst_meta l t)
        with CicUtil.Subst_not_found _ -> 
	  (* unconstrained variable, i.e. free in subst*)
          let l' =
            List.map (function None -> None | Some t -> Some (um_aux t)) l
          in
           C.Meta (i,l'))
    | C.Sort _
    | C.Implicit _ as t -> t
    | C.Cast (te,ty) -> C.Cast (um_aux te, um_aux ty)
    | C.Prod (n,s,t) -> C.Prod (n, um_aux s, um_aux t)
    | C.Lambda (n,s,t) -> C.Lambda (n, um_aux s, um_aux t)
    | C.LetIn (n,s,ty,t) -> C.LetIn (n, um_aux s, um_aux ty, um_aux t)
    | C.Appl (hd :: tl) -> appl_fun um_aux hd tl
    | C.Appl _ -> assert false
    | C.Const (uri,exp_named_subst) ->
       let exp_named_subst' =
         List.map (fun (uri, t) -> (uri, um_aux t)) exp_named_subst
       in
       C.Const (uri, exp_named_subst')
    | C.MutInd (uri,typeno,exp_named_subst) ->
       let exp_named_subst' =
         List.map (fun (uri, t) -> (uri, um_aux t)) exp_named_subst
       in
       C.MutInd (uri,typeno,exp_named_subst')
    | C.MutConstruct (uri,typeno,consno,exp_named_subst) ->
       let exp_named_subst' =
         List.map (fun (uri, t) -> (uri, um_aux t)) exp_named_subst
       in
       C.MutConstruct (uri,typeno,consno,exp_named_subst')
    | C.MutCase (sp,i,outty,t,pl) ->
       let pl' = List.map um_aux pl in
       C.MutCase (sp, i, um_aux outty, um_aux t, pl')
    | C.Fix (i, fl) ->
       let fl' =
         List.map (fun (name, i, ty, bo) -> (name, i, um_aux ty, um_aux bo)) fl
       in
       C.Fix (i, fl')
    | C.CoFix (i, fl) ->
       let fl' =
         List.map (fun (name, ty, bo) -> (name, um_aux ty, um_aux bo)) fl
       in
       C.CoFix (i, fl')
 in
  um_aux term
;;

let apply_subst =
  let appl_fun um_aux he tl =
    let tl' = List.map um_aux tl in
    let t' =
     match um_aux he with
        Cic.Appl l -> Cic.Appl (l@tl')
      | he' -> Cic.Appl (he'::tl')
    in
     begin
      match he with
         Cic.Meta (m,_) -> CicReduction.head_beta_reduce t'
       | _ -> t'
     end
  in
  fun subst t ->
(*     incr apply_subst_counter; *)
match subst with
   [] -> t
 | _ -> apply_subst_gen ~appl_fun subst t
;;

let profiler = HExtlib.profile "U/CicMetaSubst.apply_subst"
let apply_subst s t = 
  profiler.HExtlib.profile (apply_subst s) t


let apply_subst_context subst context =
 match subst with
    [] -> context
  | _ ->
(*
  incr apply_subst_context_counter;
  context_length := !context_length + List.length context;
*)
  List.fold_right
    (fun item context ->
      match item with
      | Some (n, Cic.Decl t) ->
          let t' = apply_subst subst t in
          Some (n, Cic.Decl t') :: context
      | Some (n, Cic.Def (t, ty)) ->
          let ty' = apply_subst subst ty in
          let t' = apply_subst subst t in
          Some (n, Cic.Def (t', ty')) :: context
      | None -> None :: context)
    context []

let apply_subst_metasenv subst metasenv =
(*
  incr apply_subst_metasenv_counter;
  metasenv_length := !metasenv_length + List.length metasenv;
*)
match subst with
   [] -> metasenv
 | _ ->
  List.map
    (fun (n, context, ty) ->
      (n, apply_subst_context subst context, apply_subst subst ty))
    (List.filter
      (fun (i, _, _) -> not (List.mem_assoc i subst))
      metasenv)

(***** Pretty printing functions ******)

let ppterm ~metasenv subst term =
 CicPp.ppterm ~metasenv (apply_subst subst term)

let ppterm_in_context ~metasenv subst term context =
 let name_context =
  List.map (function None -> None | Some (n,_) -> Some n) context
 in
  CicPp.pp ~metasenv (apply_subst subst term) name_context

let ppterm_in_context_ref = ref ppterm_in_context
let set_ppterm_in_context f =
 ppterm_in_context_ref := f
let use_low_level_ppterm_in_context = ref false

let ppterm_in_context ~metasenv subst term context =
 if !use_low_level_ppterm_in_context then
  ppterm_in_context ~metasenv subst term context
 else
  !ppterm_in_context_ref ~metasenv subst term context

let ppcontext' ~metasenv ?(sep = "\n") subst context =
 let separate s = if s = "" then "" else s ^ sep in
  List.fold_right 
   (fun context_entry (i,context) ->
     match context_entry with
        Some (n,Cic.Decl t) ->
         sprintf "%s%s : %s" (separate i) (CicPp.ppname n)
          (ppterm_in_context ~metasenv subst t context),
          context_entry::context
      | Some (n,Cic.Def (bo,ty)) ->
         sprintf "%s%s : %s := %s" (separate i) (CicPp.ppname n)
          (ppterm_in_context ~metasenv subst ty context)
          (ppterm_in_context ~metasenv subst bo context),
          context_entry::context
       | None ->
          sprintf "%s_ :? _" (separate i), context_entry::context
    ) context ("",[])

let ppsubst_unfolded ~metasenv subst =
  String.concat "\n"
    (List.map
      (fun (idx, (c, t,ty)) ->
        let scontext,context = ppcontext' ~metasenv ~sep:"; " subst c in
         sprintf "%s |- ?%d : %s := %s" scontext idx
(ppterm_in_context ~metasenv [] ty context)
          (ppterm_in_context ~metasenv subst t context))
       subst)
(* 
        Printf.sprintf "?%d := %s" idx (CicPp.ppterm term))
      subst) *)
;;

let ppsubst ~metasenv subst =
  String.concat "\n"
    (List.map
      (fun (idx, (c, t, ty)) ->
        let scontext,context = ppcontext' ~metasenv ~sep:"; " [] c in
         sprintf "%s |- ?%d : %s := %s" scontext idx (ppterm_in_context ~metasenv [] ty context)
          (ppterm_in_context ~metasenv [] t context))
       subst)
;;

let ppcontext ~metasenv ?sep subst context =
 fst (ppcontext' ~metasenv ?sep subst context)

let ppmetasenv ?(sep = "\n") subst metasenv =
  String.concat sep
    (List.map
      (fun (i, c, t) ->
        let scontext,context = ppcontext' ~metasenv ~sep:"; " subst c in
         sprintf "%s |- ?%d: %s" scontext i
          (ppterm_in_context ~metasenv subst t context))
      (List.filter
        (fun (i, _, _) -> not (List.mem_assoc i subst))
        metasenv))

let tempi_type_of_aux_subst = ref 0.0;;
let tempi_subst = ref 0.0;;
let tempi_type_of_aux = ref 0.0;;

(**** DELIFT ****)
(* the delift function takes in input a metavariable index, an ordered list of
 * optional terms [t1,...,tn] and a term t, and substitutes every tk = Some
 * (rel(nk)) with rel(k).  Typically, the list of optional terms is the explicit
 * substitution that is applied to a metavariable occurrence and the result of
 * the delift function is a term the implicit variable can be substituted with
 * to make the term [t] unifiable with the metavariable occurrence.  In general,
 * the problem is undecidable if we consider equivalence in place of alpha
 * convertibility. Our implementation, though, is even weaker than alpha
 * convertibility, since it replace the term [tk] if and only if [tk] is a Rel
 * (missing all the other cases). Does this matter in practice?
 * The metavariable index is the index of the metavariable that must not occur
 * in the term (for occur check).
 *)

exception NotInTheList;;

let position n =
  let rec aux k =
   function 
       [] -> raise NotInTheList
     | (Some (Cic.Rel m))::_ when m=n -> k
     | _::tl -> aux (k+1) tl in
  aux 1
;;

exception Occur;;

let rec force_does_not_occur subst to_be_restricted t =
 let module C = Cic in
 let more_to_be_restricted = ref [] in
 let rec aux k = function
      C.Rel r when List.mem (r - k) to_be_restricted -> raise Occur
    | C.Rel _
    | C.Sort _ as t -> t
    | C.Implicit _ -> assert false
    | C.Meta (n, l) ->
       (* we do not retrieve the term associated to ?n in subst since *)
       (* in this way we can restrict if something goes wrong         *)
       let l' =
         let i = ref 0 in
         List.map
           (function t ->
             incr i ;
             match t with
                None -> None
              | Some t ->
                 try
                   Some (aux k t)
                 with Occur ->
                   more_to_be_restricted := (n,!i) :: !more_to_be_restricted;
                   None)
           l
       in
        C.Meta (n, l')
    | C.Cast (te,ty) -> C.Cast (aux k te, aux k ty)
    | C.Prod (name,so,dest) -> C.Prod (name, aux k so, aux (k+1) dest)
    | C.Lambda (name,so,dest) -> C.Lambda (name, aux k so, aux (k+1) dest)
    | C.LetIn (name,so,ty,dest) ->
       C.LetIn (name, aux k so, aux k ty, aux (k+1) dest)
    | C.Appl l -> C.Appl (List.map (aux k) l)
    | C.Var (uri,exp_named_subst) ->
        let exp_named_subst' =
          List.map (fun (uri,t) -> (uri, aux k t)) exp_named_subst
        in
        C.Var (uri, exp_named_subst')
    | C.Const (uri, exp_named_subst) ->
        let exp_named_subst' =
          List.map (fun (uri,t) -> (uri, aux k t)) exp_named_subst
        in
        C.Const (uri, exp_named_subst')
    | C.MutInd (uri,tyno,exp_named_subst) ->
        let exp_named_subst' =
          List.map (fun (uri,t) -> (uri, aux k t)) exp_named_subst
        in
        C.MutInd (uri, tyno, exp_named_subst')
    | C.MutConstruct (uri,tyno,consno,exp_named_subst) ->
        let exp_named_subst' =
          List.map (fun (uri,t) -> (uri, aux k t)) exp_named_subst
        in
        C.MutConstruct (uri, tyno, consno, exp_named_subst')
    | C.MutCase (uri,tyno,out,te,pl) ->
        C.MutCase (uri, tyno, aux k out, aux k te, List.map (aux k) pl)
    | C.Fix (i,fl) ->
       let len = List.length fl in
       let k_plus_len = k + len in
       let fl' =
         List.map
          (fun (name,j,ty,bo) -> (name, j, aux k ty, aux k_plus_len bo)) fl
       in
       C.Fix (i, fl')
    | C.CoFix (i,fl) ->
       let len = List.length fl in
       let k_plus_len = k + len in
       let fl' =
         List.map
          (fun (name,ty,bo) -> (name, aux k ty, aux k_plus_len bo)) fl
       in
       C.CoFix (i, fl')
 in
 let res = aux 0 t in
 (!more_to_be_restricted, res)
 
let rec restrict subst to_be_restricted metasenv =
 match to_be_restricted with
 | [] -> metasenv, subst
 | _ ->
  let names_of_context_indexes context indexes =
    String.concat ", "
      (List.map
        (fun i ->
          try
           match List.nth context (i-1) with
           | None -> assert false
           | Some (n, _) -> CicPp.ppname n
          with
           Failure _ -> assert false
        ) indexes)
  in
  let force_does_not_occur_in_context to_be_restricted = function
    | None -> [], None
    | Some (name, Cic.Decl t) ->
        let (more_to_be_restricted, t') =
          force_does_not_occur subst to_be_restricted t
        in
        more_to_be_restricted, Some (name, Cic.Decl t')
    | Some (name, Cic.Def (bo, ty)) ->
        let (more_to_be_restricted, bo') =
          force_does_not_occur subst to_be_restricted bo
        in
        let more_to_be_restricted, ty' =
         let more_to_be_restricted', ty' =
           force_does_not_occur subst to_be_restricted ty
         in
         more_to_be_restricted @ more_to_be_restricted',
         ty'
        in
        more_to_be_restricted, Some (name, Cic.Def (bo', ty'))
  in
  let rec erase i to_be_restricted n = function
    | [] -> [], to_be_restricted, []
    | hd::tl ->
        let more_to_be_restricted,restricted,tl' =
          erase (i+1) to_be_restricted n tl
        in
        let restrict_me = List.mem i restricted in
        if restrict_me then
          more_to_be_restricted, restricted, None:: tl'
        else
          (try
            let more_to_be_restricted', hd' =
              let delifted_restricted =
               let rec aux =
                function
                   [] -> []
                 | j::tl when j > i -> (j - i)::aux tl
                 | _::tl -> aux tl
               in
                aux restricted
              in
               force_does_not_occur_in_context delifted_restricted hd
            in
             more_to_be_restricted @ more_to_be_restricted',
             restricted, hd' :: tl'
          with Occur ->
            more_to_be_restricted, (i :: restricted), None :: tl')
  in
  let (more_to_be_restricted, metasenv) =  (* restrict metasenv *)
    List.fold_right
      (fun (n, context, t) (more, metasenv) ->
        let to_be_restricted =
          List.map snd (List.filter (fun (m, _) -> m = n) to_be_restricted)
        in
        let (more_to_be_restricted, restricted, context') =
         (* just an optimization *)
         if to_be_restricted = [] then
          [],[],context
         else
          erase 1 to_be_restricted n context
        in
        try
          let more_to_be_restricted', t' =
            force_does_not_occur subst restricted t
          in
          let metasenv' = (n, context', t') :: metasenv in
          (more @ more_to_be_restricted @ more_to_be_restricted',
          metasenv')
        with Occur ->
          raise (MetaSubstFailure (lazy (sprintf
            "Cannot restrict the context of the metavariable ?%d over the hypotheses %s since metavariable's type depends on at least one of them"
	    n (names_of_context_indexes context to_be_restricted)))))
      metasenv ([], [])
  in
  let (more_to_be_restricted', subst) = (* restrict subst *)
    List.fold_right
      (* TODO: cambiare dopo l'aggiunta del ty *)
      (fun (n, (context, term,ty)) (more, subst') ->
        let to_be_restricted =
          List.map snd (List.filter (fun (m, _) -> m = n) to_be_restricted)
        in
        (try
          let (more_to_be_restricted, restricted, context') =
           (* just an optimization *)
            if to_be_restricted = [] then
              [], [], context
            else
              erase 1 to_be_restricted n context
          in
          let more_to_be_restricted', term' =
            force_does_not_occur subst restricted term
          in
          let more_to_be_restricted'', ty' =
            force_does_not_occur subst restricted ty in
          let subst' = (n, (context', term',ty')) :: subst' in
          let more = 
	    more @ more_to_be_restricted 
	    @ more_to_be_restricted'@more_to_be_restricted'' in
          (more, subst')
        with Occur ->
          let error_msg = lazy (sprintf
            "Cannot restrict the context of the metavariable ?%d over the hypotheses %s since ?%d is already instantiated with %s and at least one of the hypotheses occurs in the substituted term"
            n (names_of_context_indexes context to_be_restricted) n
            (ppterm ~metasenv subst term))
	  in 
          (* DEBUG
          debug_print (lazy error_msg);
          debug_print (lazy ("metasenv = \n" ^ (ppmetasenv metasenv subst)));
          debug_print (lazy ("subst = \n" ^ (ppsubst subst)));
          debug_print (lazy ("context = \n" ^ (ppcontext subst context))); *)
          raise (MetaSubstFailure error_msg))) 
      subst ([], []) 
  in
   restrict subst (more_to_be_restricted @ more_to_be_restricted') metasenv
;;

(*CSC: maybe we should rename delift in abstract, as I did in my dissertation *)(*Andrea: maybe not*)

let delift n subst context metasenv l t =
(* INVARIANT: we suppose that t is not another occurrence of Meta(n,_), 
   otherwise the occur check does not make sense *)

(*
 debug_print (lazy ("sto deliftando il termine " ^ (CicPp.ppterm t) ^ " rispetto
 al contesto locale " ^ (CicPp.ppterm (Cic.Meta(0,l)))));
*)

 let module S = CicSubstitution in
  let l =
   let (_, canonical_context, _) =
    try
     CicUtil.lookup_meta n metasenv
    with CicUtil.Meta_not_found _ ->
     raise (MetaSubstFailure (lazy
      ("delifting error: the metavariable " ^ string_of_int n ^ " is not " ^
       "declared in the metasenv")))
    in
   List.map2 (fun ct lt ->
     match (ct, lt) with
     | None, _ -> None
     | Some _, _ -> lt)
     canonical_context l
  in
  let to_be_restricted = ref [] in
  let rec deliftaux k =
   let module C = Cic in
    function
     | C.Rel m as t-> 
         if m <=k then
          t
         else
           (try
            match List.nth context (m-k-1) with
               Some (_,C.Def (t,_)) ->
                (try
                  C.Rel ((position (m-k) l) + k)
                 with
                  NotInTheList ->
                (*CSC: Hmmm. This bit of reduction is not in the spirit of    *)
                (*CSC: first order unification. Does it help or does it harm? *)
                (*CSC: ANSWER: it hurts performances since it is possible to  *)
                (*CSC: have an exponential explosion of the size of the proof.*)
                (*CSC: However, without this bit of reduction some "apply" in *)
                (*CSC: the library fail (e.g. nat/nth_prime.ma).              *)
                  deliftaux k (S.lift m t))
             | Some (_,C.Decl t) ->
                C.Rel ((position (m-k) l) + k)
             | None -> raise (MetaSubstFailure (lazy "RelToHiddenHypothesis"))
           with
            Failure _ -> 
             raise (MetaSubstFailure (lazy "Unbound variable found in deliftaux"))
          )
     | C.Var (uri,exp_named_subst) ->
        let exp_named_subst' =
         List.map (function (uri,t) -> uri,deliftaux k t) exp_named_subst
        in
         C.Var (uri,exp_named_subst')
     | C.Meta (i, l1) as t -> 
         (try
           let (_,t,_) = CicUtil.lookup_subst i subst in
             deliftaux k (CicSubstitution.subst_meta l1 t)
         with CicUtil.Subst_not_found _ ->
           (* see the top level invariant *)
           if (i = n) then 
            raise (MetaSubstFailure (lazy (sprintf
              "Cannot unify the metavariable ?%d with a term that has as subterm %s in which the same metavariable occurs (occur check)"
              i (ppterm ~metasenv subst t))))
          else
            begin
           (* I do not consider the term associated to ?i in subst since *)
           (* in this way I can restrict if something goes wrong.        *)
              let rec deliftl j =
                function
                    [] -> []
                  | None::tl -> None::(deliftl (j+1) tl)
                  | (Some t)::tl ->
                      let l1' = (deliftl (j+1) tl) in
                        try
                          Some (deliftaux k t)::l1'
                        with
                            NotInTheList
                          | MetaSubstFailure _ ->
                              to_be_restricted := 
                              (i,j)::!to_be_restricted ; None::l1'
              in
              let l' = deliftl 1 l1 in
                C.Meta(i,l')
            end)
     | C.Sort _ as t -> t
     | C.Implicit _ as t -> t
     | C.Cast (te,ty) -> C.Cast (deliftaux k te, deliftaux k ty)
     | C.Prod (n,s,t) -> C.Prod (n, deliftaux k s, deliftaux (k+1) t)
     | C.Lambda (n,s,t) -> C.Lambda (n, deliftaux k s, deliftaux (k+1) t)
     | C.LetIn (n,s,ty,t) ->
        C.LetIn (n, deliftaux k s, deliftaux k ty, deliftaux (k+1) t)
     | C.Appl l -> C.Appl (List.map (deliftaux k) l)
     | C.Const (uri,exp_named_subst) ->
        let exp_named_subst' =
         List.map (function (uri,t) -> uri,deliftaux k t) exp_named_subst
        in
         C.Const (uri,exp_named_subst')
     | C.MutInd (uri,typeno,exp_named_subst) ->
        let exp_named_subst' =
         List.map (function (uri,t) -> uri,deliftaux k t) exp_named_subst
        in
         C.MutInd (uri,typeno,exp_named_subst')
     | C.MutConstruct (uri,typeno,consno,exp_named_subst) ->
        let exp_named_subst' =
         List.map (function (uri,t) -> uri,deliftaux k t) exp_named_subst
        in
         C.MutConstruct (uri,typeno,consno,exp_named_subst')
     | C.MutCase (sp,i,outty,t,pl) ->
        C.MutCase (sp, i, deliftaux k outty, deliftaux k t,
         List.map (deliftaux k) pl)
     | C.Fix (i, fl) ->
        let len = List.length fl in
        let liftedfl =
         List.map
          (fun (name, i, ty, bo) ->
           (name, i, deliftaux k ty, deliftaux (k+len) bo))
           fl
        in
         C.Fix (i, liftedfl)
     | C.CoFix (i, fl) ->
        let len = List.length fl in
        let liftedfl =
         List.map
          (fun (name, ty, bo) -> (name, deliftaux k ty, deliftaux (k+len) bo))
           fl
        in
         C.CoFix (i, liftedfl)
  in
   let res =
    try
     deliftaux 0 t
    with
     NotInTheList ->
      (* This is the case where we fail even first order unification. *)
      (* The reason is that our delift function is weaker than first  *)
      (* order (in the sense of alpha-conversion). See comment above  *)
      (* related to the delift function.                              *)
(* debug_print (lazy "First Order UnificationFailure during delift") ;
debug_print(lazy (sprintf
        "Error trying to abstract %s over [%s]: the algorithm only tried to abstract over bound variables"
        (ppterm subst t)
        (String.concat "; "
          (List.map
            (function Some t -> ppterm subst t | None -> "_") l
          )))); *)
      let msg = (lazy (sprintf
        "Error trying to abstract %s over [%s]: the algorithm only tried to abstract over bound variables"
        (ppterm ~metasenv subst t)
        (String.concat "; "
          (List.map
            (function Some t -> ppterm ~metasenv subst t | None -> "_")
            l))))
      in
       if
         List.exists
          (function
              Some t -> CicUtil.is_meta_closed (apply_subst subst t)
            | None -> true) l
       then
        raise (Uncertain msg)
       else
        raise (MetaSubstFailure msg)
   in
   let (metasenv, subst) = restrict subst !to_be_restricted metasenv in
    res, metasenv, subst
;;

(* delifts a term t of n levels strating from k, that is changes (Rel m)
 * to (Rel (m - n)) when m > (k + n). if k <= m < k + n delift fails
 *)
let delift_rels_from subst metasenv k n =
 let rec liftaux subst metasenv k =
  let module C = Cic in
   function
      C.Rel m as t ->
       if m < k then
        t, subst, metasenv
       else if m < k + n then
         raise DeliftingARelWouldCaptureAFreeVariable
       else
        C.Rel (m - n), subst, metasenv
    | C.Var (uri,exp_named_subst) ->
       let exp_named_subst',subst,metasenv = 
        List.fold_right
         (fun (uri,t) (l,subst,metasenv) ->
           let t',subst,metasenv = liftaux subst metasenv k t in
            (uri,t')::l,subst,metasenv) exp_named_subst ([],subst,metasenv)
       in
        C.Var (uri,exp_named_subst'),subst,metasenv
    | C.Meta (i,l) ->
        (try
          let (_, t,_) = lookup_subst i subst in
           liftaux subst metasenv k (CicSubstitution.subst_meta l t)
         with CicUtil.Subst_not_found _ -> 
          let l',to_be_restricted,subst,metasenv =
           let rec aux con l subst metasenv =
            match l with
               [] -> [],[],subst,metasenv
             | he::tl ->
                let tl',to_be_restricted,subst,metasenv =
                 aux (con + 1) tl subst metasenv in
                let he',more_to_be_restricted,subst,metasenv =
                 match he with
                    None -> None,[],subst,metasenv
                  | Some t ->
                     try
                      let t',subst,metasenv = liftaux subst metasenv k t in
                       Some t',[],subst,metasenv
                     with
                      DeliftingARelWouldCaptureAFreeVariable ->
                       None,[i,con],subst,metasenv
                in
                 he'::tl',more_to_be_restricted@to_be_restricted,subst,metasenv
           in
            aux 1 l subst metasenv in
          let metasenv,subst = restrict subst to_be_restricted metasenv in
           C.Meta(i,l'),subst,metasenv)
    | C.Sort _ as t -> t,subst,metasenv
    | C.Implicit _ as t -> t,subst,metasenv
    | C.Cast (te,ty) ->
       let te',subst,metasenv = liftaux subst metasenv k te in
       let ty',subst,metasenv = liftaux subst metasenv k ty in
        C.Cast (te',ty'),subst,metasenv
    | C.Prod (n,s,t) ->
       let s',subst,metasenv = liftaux subst metasenv k s in
       let t',subst,metasenv = liftaux subst metasenv (k+1) t in
        C.Prod (n,s',t'),subst,metasenv
    | C.Lambda (n,s,t) ->
       let s',subst,metasenv = liftaux subst metasenv k s in
       let t',subst,metasenv = liftaux subst metasenv (k+1) t in
        C.Lambda (n,s',t'),subst,metasenv
    | C.LetIn (n,s,ty,t) ->
       let s',subst,metasenv = liftaux subst metasenv k s in
       let ty',subst,metasenv = liftaux subst metasenv k ty in
       let t',subst,metasenv = liftaux subst metasenv (k+1) t in
        C.LetIn (n,s',ty',t'),subst,metasenv
    | C.Appl l ->
       let l',subst,metasenv =
        List.fold_right
         (fun t (l,subst,metasenv) ->
           let t',subst,metasenv = liftaux subst metasenv k t in
            t'::l,subst,metasenv) l ([],subst,metasenv) in
       C.Appl l',subst,metasenv
    | C.Const (uri,exp_named_subst) ->
       let exp_named_subst',subst,metasenv = 
        List.fold_right
         (fun (uri,t) (l,subst,metasenv) ->
           let t',subst,metasenv = liftaux subst metasenv k t in
            (uri,t')::l,subst,metasenv) exp_named_subst ([],subst,metasenv)
       in
        C.Const (uri,exp_named_subst'),subst,metasenv
    | C.MutInd (uri,tyno,exp_named_subst) ->
       let exp_named_subst',subst,metasenv = 
        List.fold_right
         (fun (uri,t) (l,subst,metasenv) ->
           let t',subst,metasenv = liftaux subst metasenv k t in
            (uri,t')::l,subst,metasenv) exp_named_subst ([],subst,metasenv)
       in
        C.MutInd (uri,tyno,exp_named_subst'),subst,metasenv
    | C.MutConstruct (uri,tyno,consno,exp_named_subst) ->
       let exp_named_subst',subst,metasenv = 
        List.fold_right
         (fun (uri,t) (l,subst,metasenv) ->
           let t',subst,metasenv = liftaux subst metasenv k t in
            (uri,t')::l,subst,metasenv) exp_named_subst ([],subst,metasenv)
       in
        C.MutConstruct (uri,tyno,consno,exp_named_subst'),subst,metasenv
    | C.MutCase (sp,i,outty,t,pl) ->
       let outty',subst,metasenv = liftaux subst metasenv k outty in
       let t',subst,metasenv = liftaux subst metasenv k t in
       let pl',subst,metasenv =
        List.fold_right
         (fun t (l,subst,metasenv) ->
           let t',subst,metasenv = liftaux subst metasenv k t in
            t'::l,subst,metasenv) pl ([],subst,metasenv)
       in
        C.MutCase (sp,i,outty',t',pl'),subst,metasenv
    | C.Fix (i, fl) ->
       let len = List.length fl in
       let liftedfl,subst,metasenv =
        List.fold_right
         (fun (name, i, ty, bo) (l,subst,metasenv) ->
           let ty',subst,metasenv = liftaux subst metasenv k ty in
           let bo',subst,metasenv = liftaux subst metasenv (k+len) bo in
            (name,i,ty',bo')::l,subst,metasenv
         ) fl ([],subst,metasenv)
       in
        C.Fix (i, liftedfl),subst,metasenv
    | C.CoFix (i, fl) ->
       let len = List.length fl in
       let liftedfl,subst,metasenv =
        List.fold_right
         (fun (name, ty, bo) (l,subst,metasenv) ->
           let ty',subst,metasenv = liftaux subst metasenv k ty in
           let bo',subst,metasenv = liftaux subst metasenv (k+len) bo in
            (name,ty',bo')::l,subst,metasenv
         ) fl ([],subst,metasenv)
       in
        C.CoFix (i, liftedfl),subst,metasenv
 in
  liftaux subst metasenv k

let delift_rels subst metasenv n t =
  delift_rels_from subst metasenv 1 n t
 

(**** END OF DELIFT ****)


(** {2 Format-like pretty printers} *)

let fpp_gen ppf s =
  Format.pp_print_string ppf s;
  Format.pp_print_newline ppf ();
  Format.pp_print_flush ppf ()

let fppsubst ppf subst = fpp_gen ppf (ppsubst ~metasenv:[] subst)
let fppterm ppf term = fpp_gen ppf (CicPp.ppterm term)
let fppmetasenv ppf metasenv = fpp_gen ppf (ppmetasenv [] metasenv)
