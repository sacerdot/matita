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
 * http://cs.unibo.it/helm/.
 *)

(* let _profiler = <:profiler<_profiler>>;; *)

(* $Id: inference.ml 6245 2006-04-05 12:07:51Z tassi $ *)

type rule = SuperpositionRight | SuperpositionLeft | Demodulation
type uncomparable = int -> int 

type equality =
    uncomparable *       (* trick to break structural equality *)
    int  *               (* weight *)
    proof * 
    (Cic.term *          (* type *)
     Cic.term *          (* left side *)
     Cic.term *          (* right side *)
     Utils.comparison) * (* ordering *)  
    Cic.metasenv  *      (* environment for metas *)
    int                  (* id *)
and proof = 
  | Exact of Cic.term
  | Step of Subst.substitution * (rule * int*(Utils.pos*int)* Cic.term) 
            (* subst, (rule,eq1, eq2,predicate) *)  
and goal_proof = (rule * Utils.pos * int * Subst.substitution * Cic.term) list
;;
(* the hashtbl eq_id -> proof, max_eq_id *)
module IntOt = struct type t = int let compare = Pervasives.compare end
module M = Map.Make(IntOt)
type equality_bag = equality M.t * int

type goal = goal_proof * Cic.metasenv * Cic.term

(* globals *)
let mk_equality_bag () = M.empty, 10000 ;; 

let freshid (m,i) = (m,i+1), i+1 ;;

let add_to_bag (id_to_eq,i) id eq = M.add id eq id_to_eq,i ;;

let uncomparable = fun _ -> 0

let mk_equality bag (weight,p,(ty,l,r,o),m) =
  let bag, id = freshid bag in
  let eq = (uncomparable,weight,p,(ty,l,r,o),m,id) in
  let bag = add_to_bag bag id eq in
  bag, eq
;;

let mk_tmp_equality (weight,(ty,l,r,o),m) =
  let id = -1 in
  uncomparable,weight,Exact (Cic.Implicit None),(ty,l,r,o),m,id
;;


let open_equality (_,weight,proof,(ty,l,r,o),m,id) = 
  (weight,proof,(ty,l,r,o),m,id)

let id_of e = 
  let _,_,_,_,id = open_equality e in id
;;


let string_of_rule = function
  | SuperpositionRight -> "SupR"
  | SuperpositionLeft -> "SupL"
  | Demodulation -> "Demod"
;;

let string_of_equality ?env eq =
  match env with
  | None ->
      let w, _, (ty, left, right, o), m , id = open_equality eq in
      Printf.sprintf "Id: %d, Weight: %d, {%s}: %s =(%s) %s [%s]" 
              id w (CicPp.ppterm ty)
              (CicPp.ppterm left) 
              (Utils.string_of_comparison o) (CicPp.ppterm right)
         (String.concat ", " (List.map (fun (i,_,_) -> string_of_int i) m)) 
(*          "..."  *)
  | Some (_, context, _) -> 
      let names = Utils.names_of_context context in
      let w, _, (ty, left, right, o), m , id = open_equality eq in
      Printf.sprintf "Id: %d, Weight: %d, {%s}: %s =(%s) %s [%s]" 
              id w (CicPp.pp ty names)
              (CicPp.pp left names) (Utils.string_of_comparison o)
              (CicPp.pp right names)
         (String.concat ", " (List.map (fun (i,_,_) -> string_of_int i) m)) 
(*            "..." *)
;;

let compare (_,_,_,s1,_,_) (_,_,_,s2,_,_) =
  Pervasives.compare s1 s2
;;

let rec max_weight_in_proof ((id_to_eq,_) as bag) current =
  function
   | Exact _ -> current
   | Step (_, (_,id1,(_,id2),_)) ->
       let eq1 = M.find id1 id_to_eq in
       let eq2 = M.find id2 id_to_eq in  
       let (w1,p1,(_,_,_,_),_,_) = open_equality eq1 in
       let (w2,p2,(_,_,_,_),_,_) = open_equality eq2 in
       let current = max current w1 in
       let current = max_weight_in_proof bag current p1 in
       let current = max current w2 in
       max_weight_in_proof bag current p2

let max_weight_in_goal_proof ((id_to_eq,_) as bag) =
  List.fold_left 
    (fun current (_,_,id,_,_) ->
       let eq = M.find id id_to_eq in
       let (w,p,(_,_,_,_),_,_) = open_equality eq in
       let current = max current w in
       max_weight_in_proof bag current p)

let max_weight bag goal_proof proof =
  let current = max_weight_in_proof bag 0 proof in
  max_weight_in_goal_proof bag current goal_proof

let proof_of_id (id_to_eq,_) id =
  try
    let (_,p,(_,l,r,_),_,_) = open_equality (M.find id id_to_eq) in
      p,l,r
  with
      Not_found -> 
              prerr_endline ("Unable to find the proof of " ^ string_of_int id);
              assert false
;;

let is_in (id_to_eq,_) id = 
  M.mem id id_to_eq
;;


let string_of_proof ?(names=[]) bag p gp = 
  let str_of_pos = function
    | Utils.Left -> "left"
    | Utils.Right -> "right"
  in
  let fst3 (x,_,_) = x in
  let rec aux margin name = 
    let prefix = String.make margin ' ' ^ name ^ ": " in function 
    | Exact t -> 
        Printf.sprintf "%sExact (%s)\n" 
          prefix (CicPp.pp t names)
    | Step (subst,(rule,eq1,(pos,eq2),pred)) -> 
        Printf.sprintf "%s%s(%s|%d with %d dir %s pred %s))\n"
          prefix (string_of_rule rule) (Subst.ppsubst ~names subst) eq1 eq2 (str_of_pos pos) 
          (CicPp.pp pred names)^ 
        aux (margin+1) (Printf.sprintf "%d" eq1) (fst3 (proof_of_id bag eq1)) ^ 
        aux (margin+1) (Printf.sprintf "%d" eq2) (fst3 (proof_of_id bag eq2)) 
  in
  aux 0 "" p ^ 
  String.concat "\n" 
    (List.map 
      (fun (r,pos,i,s,t) -> 
        (Printf.sprintf 
          "GOAL: %s %s %d %s %s\n" (string_of_rule r)
            (str_of_pos pos) i (Subst.ppsubst ~names s) (CicPp.pp t names)) ^ 
        aux 1 (Printf.sprintf "%d " i) (fst3 (proof_of_id bag i)))
      gp)
;;

let rec depend ((id_to_eq,_) as bag) eq id seen =
  let (_,p,(_,_,_,_),_,ideq) = open_equality eq in
  if List.mem ideq seen then 
    false,seen
  else
    if id = ideq then 
      true,seen
    else  
      match p with
      | Exact _ -> false,seen
      | Step (_,(_,id1,(_,id2),_)) ->
          let seen = ideq::seen in
          let eq1 = M.find id1 id_to_eq in
          let eq2 = M.find id2 id_to_eq in  
          let b1,seen = depend bag eq1 id seen in
          if b1 then b1,seen else depend bag eq2 id seen
;;

let depend bag eq id = fst (depend bag eq id []);;

let ppsubst = Subst.ppsubst ~names:[];;

(* returns an explicit named subst and a list of arguments for sym_eq_URI *)
let build_ens uri termlist =
  let obj, _ = CicEnvironment.get_obj CicUniv.empty_ugraph uri in
  match obj with
  | Cic.Constant (_, _, _, uris, _) ->
      (* assert (List.length uris <= List.length termlist); *)
      let rec aux = function
        | [], tl -> [], tl
        | (uri::uris), (term::tl) ->
            let ens, args = aux (uris, tl) in
            (uri, term)::ens, args
        | _, _ -> assert false
      in
      aux (uris, termlist)
  | _ -> assert false
;;

let mk_sym uri ty t1 t2 p =
  let ens, args =  build_ens uri [ty;t1;t2;p] in
    Cic.Appl (Cic.Const(uri, ens) :: args)
;;

let mk_trans uri ty t1 t2 t3 p12 p23 =
  let ens, args = build_ens uri [ty;t1;t2;t3;p12;p23] in
    Cic.Appl (Cic.Const (uri, ens) :: args)
;;

let mk_eq_ind uri ty what pred p1 other p2 =
  let ens, args = build_ens uri [ty; what; pred; p1; other; p2] in
  Cic.Appl (Cic.Const (uri, ens) :: args)
;;

let p_of_sym ens tl =
  let args = List.map snd ens @ tl in
  match args with 
    | [_;_;_;p] -> p 
    | _ -> assert false 
;;

let open_trans ens tl =
  let args = List.map snd ens @ tl in
  match args with 
    | [ty;l;m;r;p1;p2] -> ty,l,m,r,p1,p2
    | _ -> assert false   
;;

let open_sym ens tl =
  let args = List.map snd ens @ tl in
  match args with 
    | [ty;l;r;p] -> ty,l,r,p
    | _ -> assert false   
;;

let open_eq_ind args =
  match args with 
  | [ty;l;pred;pl;r;pleqr] -> ty,l,pred,pl,r,pleqr
  | _ -> assert false   
;;

let open_pred pred =
  match pred with 
  | Cic.Lambda (_,_,(Cic.Appl [Cic.MutInd (uri, 0,_);ty;l;r])) 
     when LibraryObjects.is_eq_URI uri -> ty,uri,l,r
  | _ -> Utils.debug_print (lazy (CicPp.ppterm pred)); assert false   
;;

let is_not_fixed t =
   CicSubstitution.subst (Cic.Implicit None) t <>
   CicSubstitution.subst (Cic.Rel 1) t
;;

let canonical t context menv = 
  let remove_cycles t =
   let is_transitive =
    function
       Cic.Appl (Cic.Const (uri_trans,_)::_)
        when LibraryObjects.is_trans_eq_URI uri_trans ->
         true
     | _ -> false in
   let rec collect =
    function
       Cic.Appl (Cic.Const (uri_trans,ens)::tl)
        when LibraryObjects.is_trans_eq_URI uri_trans ->
         let ty,l,m,r,p1,p2 = open_trans ens tl in
          (if is_transitive p1 then fst (collect p1) else [l,p1]) @
           (if is_transitive p2 then fst (collect p2) else [m,p2]),
          (r, uri_trans, ty)
     | t -> assert false in
   let rec cut_to_last_duplicate l acc =
    function
       [] -> List.rev acc
     | (l',p)::tl when l=l' -> 
if acc <> [] then
Utils.debug_print (lazy ("!!! RISPARMIO " ^ string_of_int (List.length acc) ^ " PASSI"));
         cut_to_last_duplicate l [l',p] tl
     | (l',p)::tl ->
         cut_to_last_duplicate l ((l',p)::acc) tl
   in
   let rec rebuild =
    function
       (l,_)::_::_ as steps, ((r,uri_trans,ty) as last) ->
         (match cut_to_last_duplicate l [] steps with
             (l,p1)::((m,_)::_::_ as tl) ->
               mk_trans uri_trans ty l m r p1 (rebuild (tl,last))
           | [l,p1 ; m,p2] -> mk_trans uri_trans ty l m r p1 p2
           | [l,p1] -> p1
           | [] -> assert false)
     | _ -> assert false
   in
    if is_transitive t then
     rebuild (collect t)
    else
     t
  in
  let rec remove_refl t =
    match t with
    | Cic.Appl (((Cic.Const(uri_trans,ens))::tl) as args)
          when LibraryObjects.is_trans_eq_URI uri_trans ->
          let ty,l,m,r,p1,p2 = open_trans ens tl in
            (match p1,p2 with
              | Cic.Appl [Cic.MutConstruct (uri, 0, 1,_);_;_],p2 -> 
                  remove_refl p2
              | p1,Cic.Appl [Cic.MutConstruct (uri, 0, 1,_);_;_] -> 
                  remove_refl p1
              | _ -> Cic.Appl (List.map remove_refl args))
    | Cic.Appl l -> Cic.Appl (List.map remove_refl l)
    | Cic.LetIn (name,bo,ty,rest) ->
        Cic.LetIn (name,remove_refl bo,remove_refl ty,remove_refl rest)
    | _ -> t
  in
  let rec canonical_trough_lambda context = function
    | Cic.Lambda(name,ty,bo) -> 
        let context' = (Some (name,Cic.Decl ty))::context in
        Cic.Lambda(name,ty,canonical_trough_lambda context' bo)
    | t -> canonical context t

  and canonical context t =
    match t with
      | Cic.LetIn(name,bo,ty,rest) -> 
          let bo = canonical_trough_lambda context bo in
          let ty = canonical_trough_lambda context ty in
          let context' = (Some (name,Cic.Def (bo,ty)))::context in
          Cic.LetIn(name,bo,ty,canonical context' rest)
      | Cic.Appl (((Cic.Const(uri_sym,ens))::tl) as args)
          when LibraryObjects.is_sym_eq_URI uri_sym ->
          (match p_of_sym ens tl with
             | Cic.Appl ((Cic.Const(uri,ens))::tl)
                 when LibraryObjects.is_sym_eq_URI uri -> 
                   canonical context (p_of_sym ens tl)
             | Cic.Appl ((Cic.Const(uri_trans,ens))::tl)
                 when LibraryObjects.is_trans_eq_URI uri_trans ->
                 let ty,l,m,r,p1,p2 = open_trans ens tl in
                   mk_trans uri_trans ty r m l 
                     (canonical context (mk_sym uri_sym ty m r p2)) 
                     (canonical context (mk_sym uri_sym ty l m p1))
             | Cic.Appl (([Cic.Const(uri_feq,ens);ty1;ty2;f;x;y;p]))
                 when LibraryObjects.is_eq_f_URI uri_feq ->
                 let eq = LibraryObjects.eq_URI_of_eq_f_URI uri_feq in
                 let eq_f_sym =
                   Cic.Const (LibraryObjects.eq_f_sym_URI ~eq, [])
                 in
                 let rc = Cic.Appl [eq_f_sym;ty1;ty2;f;x;y;p] in
                 Utils.debug_print (lazy ("CANONICAL " ^ CicPp.ppterm rc));
                 rc
             | Cic.Appl [Cic.MutConstruct (uri, 0, 1,_);_;_] as t
                 when LibraryObjects.is_eq_URI uri -> t
             | _ -> Cic.Appl (List.map (canonical context) args))
      | Cic.Appl l -> Cic.Appl (List.map (canonical context) l)
      | _ -> t
  in
   remove_cycles (remove_refl (canonical context t))
;;
  
let compose_contexts ctx1 ctx2 = 
  ProofEngineReduction.replace_lifting 
  ~equality:(fun _ ->(=)) ~context:[] ~what:[Cic.Implicit(Some `Hole)] ~with_what:[ctx2] ~where:ctx1
;;

let put_in_ctx ctx t = 
  ProofEngineReduction.replace_lifting
  ~equality:(fun _ -> (=)) ~context:[] ~what:[Cic.Implicit (Some `Hole)] ~with_what:[t] ~where:ctx
;;

let mk_eq uri ty l r =
  let ens, args = build_ens uri [ty; l; r] in
  Cic.Appl (Cic.MutInd(uri,0,ens) :: args)
;;

let mk_refl uri ty t = 
  let ens, args = build_ens uri [ty; t] in
  Cic.Appl (Cic.MutConstruct(uri,0,1,ens) :: args)
;;

let open_eq = function 
  | Cic.Appl [Cic.MutInd(uri,0,[]);ty;l;r] when LibraryObjects.is_eq_URI uri ->
      uri, ty, l ,r
  | _ -> assert false
;;

let mk_feq uri_feq ty ty1 left pred right t = 
  let ens, args = build_ens uri_feq [ty;ty1;pred;left;right;t] in
  Cic.Appl (Cic.Const(uri_feq,ens) :: args)
;;

let rec look_ahead aux = function
  | Cic.Appl ((Cic.Const(uri_ind,ens))::tl) as t
        when LibraryObjects.is_eq_ind_URI uri_ind || 
             LibraryObjects.is_eq_ind_r_URI uri_ind ->
          let ty1,what,pred,p1,other,p2 = open_eq_ind tl in
          let ty2,eq,lp,rp = open_pred pred in 
          let hole = Cic.Implicit (Some `Hole) in
          let ty2 = CicSubstitution.subst hole ty2 in
          aux ty1 (CicSubstitution.subst other lp) (CicSubstitution.subst other rp) hole ty2 t
  | Cic.Lambda (n,s,t) -> Cic.Lambda (n,s,look_ahead aux t)
  | t -> t
;;

let contextualize uri ty left right t = 
  let hole = Cic.Implicit (Some `Hole) in
  (* aux [uri] [ty] [left] [right] [ctx] [ctx_ty] [t] 
   * 
   * the parameters validate this invariant  
   *   t: eq(uri) ty left right
   * that is used only by the base case
   *
   * ctx is a term with an hole. Cic.Implicit(Some `Hole) is the empty context
   * ctx_ty is the type of ctx
   *)
    let rec aux uri ty left right ctx_d ctx_ty t =
      match t with 
      | Cic.Appl ((Cic.Const(uri_sym,ens))::tl) 
        when LibraryObjects.is_sym_eq_URI uri_sym  ->
          let ty,l,r,p = open_sym ens tl in
          mk_sym uri_sym ty l r (aux uri ty l r ctx_d ctx_ty p)
      | Cic.LetIn (name,body,bodyty,rest) ->
         Cic.LetIn
          (name,look_ahead (aux uri) body, bodyty,
           aux uri ty left right ctx_d ctx_ty rest)
      | Cic.Appl ((Cic.Const(uri_ind,ens))::tl)
        when LibraryObjects.is_eq_ind_URI uri_ind || 
             LibraryObjects.is_eq_ind_r_URI uri_ind ->
          let ty1,what,pred,p1,other,p2 = open_eq_ind tl in
          let ty2,eq,lp,rp = open_pred pred in 
          let uri_trans = LibraryObjects.trans_eq_URI ~eq:uri in
          let uri_sym = LibraryObjects.sym_eq_URI ~eq:uri in
          let is_not_fixed_lp = is_not_fixed lp in
          let avoid_eq_ind = LibraryObjects.is_eq_ind_URI uri_ind in
          (* extract the context and the fixed term from the predicate *)
          let m, ctx_c, ty2 = 
            let m, ctx_c = if is_not_fixed_lp then rp,lp else lp,rp in
            (* they were under a lambda *)
            let m =  CicSubstitution.subst hole m in
            let ctx_c = CicSubstitution.subst hole ctx_c in
            let ty2 = CicSubstitution.subst hole ty2 in
            m, ctx_c, ty2          
          in
          (* create the compound context and put the terms under it *)
          let ctx_dc = compose_contexts ctx_d ctx_c in
          let dc_what = put_in_ctx ctx_dc what in
          let dc_other = put_in_ctx ctx_dc other in
          (* m is already in ctx_c so it is put in ctx_d only *)
          let d_m = put_in_ctx ctx_d m in
          (* we also need what in ctx_c *)
          let c_what = put_in_ctx ctx_c what in
          (* now put the proofs in the compound context *)
          let p1 = (* p1: dc_what = d_m *)
            if is_not_fixed_lp then
              aux uri ty2 c_what m ctx_d ctx_ty p1
            else
              mk_sym uri_sym ctx_ty d_m dc_what
                (aux uri ty2 m c_what ctx_d ctx_ty p1)
          in
          let p2 = (* p2: dc_other = dc_what *)
            if avoid_eq_ind then
              mk_sym uri_sym ctx_ty dc_what dc_other
                (aux uri ty1 what other ctx_dc ctx_ty p2)
             else
              aux uri ty1 other what ctx_dc ctx_ty p2
          in
          (* if pred = \x.C[x]=m --> t : C[other]=m --> trans other what m
             if pred = \x.m=C[x] --> t : m=C[other] --> trans m what other *)
          let a,b,c,paeqb,pbeqc =
            if is_not_fixed_lp then
              dc_other,dc_what,d_m,p2,p1
            else
              d_m,dc_what,dc_other,
                (mk_sym uri_sym ctx_ty dc_what d_m p1),
                (mk_sym uri_sym ctx_ty dc_other dc_what p2)
          in
          mk_trans uri_trans ctx_ty a b c paeqb pbeqc
    | t when ctx_d = hole -> t 
    | t -> 
(*         let uri_sym = LibraryObjects.sym_eq_URI ~eq:uri in *)
(*         let uri_ind = LibraryObjects.eq_ind_URI ~eq:uri in *)

        let uri_feq = LibraryObjects.eq_f_URI ~eq:uri in
        let pred = 
(*           let r = CicSubstitution.lift 1 (put_in_ctx ctx_d left) in *)
          let l = 
            let ctx_d = CicSubstitution.lift 1 ctx_d in
            put_in_ctx ctx_d (Cic.Rel 1)
          in
(*           let lty = CicSubstitution.lift 1 ctx_ty in  *)
(*           Cic.Lambda (Cic.Name "foo",ty,(mk_eq uri lty l r)) *)
          Cic.Lambda (Cic.Name "foo",ty,l)
        in
(*         let d_left = put_in_ctx ctx_d left in *)
(*         let d_right = put_in_ctx ctx_d right in *)
(*         let refl_eq = mk_refl uri ctx_ty d_left in *)
(*         mk_sym uri_sym ctx_ty d_right d_left *)
(*           (mk_eq_ind uri_ind ty left pred refl_eq right t) *)
          (mk_feq uri_feq ty ctx_ty left pred right t)
  in
  aux uri ty left right hole ty t
;;

let contextualize_rewrites t ty = 
  let eq,ty,l,r = open_eq ty in
  contextualize eq ty l r t
;;

let add_subst subst =
  function
    | Exact t -> Exact (Subst.apply_subst subst t)
    | Step (s,(rule, id1, (pos,id2), pred)) -> 
        Step (Subst.concat subst s,(rule, id1, (pos,id2), pred))
;;
	
let build_proof_step eq lift subst p1 p2 pos l r pred =
  let p1 = Subst.apply_subst_lift lift subst p1 in
  let p2 = Subst.apply_subst_lift lift subst p2 in
  let l  = CicSubstitution.lift lift l in
  let l = Subst.apply_subst_lift lift subst l in
  let r  = CicSubstitution.lift lift r in
  let r = Subst.apply_subst_lift lift subst r in
  let pred = CicSubstitution.lift lift pred in
  let pred = Subst.apply_subst_lift lift subst pred in
  let ty,body = 
    match pred with
      | Cic.Lambda (_,ty,body) -> ty,body 
      | _ -> assert false
  in
  let what, other = 
    if pos = Utils.Left then l,r else r,l
  in
  let p =
    match pos with
      | Utils.Left ->
        mk_eq_ind (LibraryObjects.eq_ind_URI ~eq) ty what pred p1 other p2
      | Utils.Right ->
        mk_eq_ind (LibraryObjects.eq_ind_r_URI ~eq) ty what pred p1 other p2
  in
    p
;;

let parametrize_proof p l r = 
  let uniq l = HExtlib.list_uniq (List.sort (fun (i,_) (j,_) -> Pervasives.compare i j) l) in
  let mot = CicUtil.metas_of_term_set in
  let parameters = uniq (mot p @ mot l @ mot r) in 
  (* ?if they are under a lambda? *)
(*
  let parameters = 
    HExtlib.list_uniq (List.sort Pervasives.compare parameters) 
  in
*)
  (* resorts l such that *hopefully* dependencies can be inferred *)
  let guess_dependency p l =
    match p with
    | Cic.Appl ((Cic.Const(uri_ind,ens))::tl) 
        when LibraryObjects.is_eq_ind_URI uri_ind || 
             LibraryObjects.is_eq_ind_r_URI uri_ind ->
        let ty,_,_,_,_,_ = open_eq_ind tl in
        let metas = CicUtil.metas_of_term ty in
        let nondep, dep = 
          List.partition (fun (i,_) -> List.exists (fun (j,_) -> j=i) metas) l
        in
        nondep@dep
    | _ -> l
  in
  let parameters = guess_dependency p parameters in
  let what = List.map (fun (i,l) -> Cic.Meta (i,l)) parameters in 
  let with_what, lift_no = 
    List.fold_right (fun _ (acc,n) -> ((Cic.Rel n)::acc),n+1) what ([],1) 
  in
  let p = CicSubstitution.lift (lift_no-1) p in
  let p = 
    ProofEngineReduction.replace_lifting
    ~equality:(fun _ t1 t2 -> 
      match t1,t2 with Cic.Meta (i,_),Cic.Meta(j,_) -> i=j | _ -> false) 
    ~context:[]
    ~what ~with_what ~where:p
  in
  let ty_of_m _ = Cic.Implicit (Some `Type) in
  let args, proof,_ = 
    List.fold_left 
      (fun (instance,p,n) m -> 
        (instance@[m],
        Cic.Lambda 
          (Cic.Name ("X"^string_of_int n),
          CicSubstitution.lift (lift_no - n - 1) (ty_of_m m),
          p),
        n+1)) 
      ([Cic.Rel 1],p,1) 
      what
  in
  let instance = match args with | [x] -> x | _ -> Cic.Appl args in
  proof, instance
;;

let wfo bag goalproof proof id =
  let rec aux acc id =
    let p,_,_ = proof_of_id bag id in
    match p with
    | Exact _ -> if (List.mem id acc) then acc else id :: acc
    | Step (_,(_,id1, (_,id2), _)) -> 
        let acc = if not (List.mem id1 acc) then aux acc id1 else acc in
        let acc = if not (List.mem id2 acc) then aux acc id2 else acc in
        id :: acc
  in
  let acc = 
    match proof with
      | Exact _ -> [id]
      | Step (_,(_,id1, (_,id2), _)) -> aux (aux [id] id1) id2
  in 
  List.fold_left (fun acc (_,_,id,_,_) -> aux acc id) acc goalproof
;;

let string_of_id (id_to_eq,_) names id = 
  if id = 0 then "" else 
  try
    let (_,p,(t,l,r,_),m,_) = open_equality (M.find id id_to_eq) in
    match p with
    | Exact t -> 
        Printf.sprintf "%d = %s: %s = %s [%s]" id
          (CicPp.pp t names) (CicPp.pp l names) (CicPp.pp r names)
(*           "..." *)
         (String.concat ", " (List.map (fun (i,_,_) -> string_of_int i) m)) 
    | Step (_,(step,id1, (dir,id2), p) ) ->
        Printf.sprintf "%6d: %s %6d %6d   %s =(%s) %s [%s]" id
          (string_of_rule step)
          id1 id2 (CicPp.pp l names) (CicPp.pp t names) (CicPp.pp r names)
         (String.concat ", " (List.map (fun (i,_,_) -> string_of_int i) m)) 
          (*"..."*)
  with
      Not_found -> assert false

let pp_proof bag names goalproof proof subst id initial_goal =
  String.concat "\n" (List.map (string_of_id bag names) (wfo bag goalproof proof id)) ^ 
  "\ngoal:\n   " ^ 
    (String.concat "\n   " 
      (fst (List.fold_right
        (fun (r,pos,i,s,pred) (acc,g) -> 
          let _,_,left,right = open_eq g in
          let ty = 
            match pos with 
            | Utils.Left -> CicReduction.head_beta_reduce (Cic.Appl[pred;right])
            | Utils.Right -> CicReduction.head_beta_reduce (Cic.Appl[pred;left])
          in
          let ty = Subst.apply_subst s ty in
          ("("^ string_of_rule r ^ " " ^ string_of_int i^") -> "
          ^ CicPp.pp ty names) :: acc,ty) goalproof ([],initial_goal)))) ^
  "\nand then subsumed by " ^ string_of_int id ^ " when " ^ Subst.ppsubst subst
;;

let rec find_deps bag m i = 
  if M.mem i m then m
  else 
    let p,_,_ = proof_of_id bag i in
    match p with
    | Exact _ -> M.add i [] m
    | Step (_,(_,id1,(_,id2),_)) -> 
        let m = find_deps bag m id1 in
        let m = find_deps bag m id2 in
        (* without the uniq there is a stack overflow doing concatenation *)
        let xxx = [id1;id2] @ M.find id1 m @ M.find id2 m in 
        let xxx = HExtlib.list_uniq (List.sort Pervasives.compare xxx) in
        M.add i xxx m
;;

let topological_sort bag l = 
  (* build the partial order relation *)
  let m = List.fold_left (fun m i -> find_deps bag m i) M.empty l in
  let m = (* keep only deps inside l *) 
    List.fold_left 
      (fun m' i ->
        M.add i (List.filter (fun x -> List.mem x l) (M.find i m)) m') 
      M.empty l 
  in
  let m = M.map (fun x -> Some x) m in
  (* utils *)
  let keys m = M.fold (fun i _ acc -> i::acc) m [] in
  let split l m = List.filter (fun i -> M.find i m = Some []) l in
  let purge l m = 
    M.mapi 
      (fun k v -> if List.mem k l then None else 
         match v with
         | None -> None
         | Some ll -> Some (List.filter (fun i -> not (List.mem i l)) ll)) 
      m
  in
  let rec aux m res = 
      let keys = keys m in
      let ok = split keys m in
      let m = purge ok m in
      let res = ok @ res in
      if ok = [] then res else aux m res
  in
  let rc = List.rev (aux m []) in
  rc
;;
  
(* returns the list of ids that should be factorized *)
let get_duplicate_step_in_wfo bag l p =
  let ol = List.rev l in
  let h = Hashtbl.create 13 in
  (* NOTE: here the n parameter is an approximation of the dependency 
     between equations. To do things seriously we should maintain a 
     dependency graph. This approximation is not perfect. *)
  let add i = 
    let p,_,_ = proof_of_id bag i in 
    match p with 
    | Exact _ -> true
    | _ -> 
        try 
          let no = Hashtbl.find h i in
          Hashtbl.replace h i (no+1);
          false
        with Not_found -> Hashtbl.add h i 1;true
  in
  let rec aux = function
    | Exact _ -> ()
    | Step (_,(_,i1,(_,i2),_)) -> 
        let go_on_1 = add i1 in
        let go_on_2 = add i2 in
        if go_on_1 then aux (let p,_,_ = proof_of_id bag i1 in p);
        if go_on_2 then aux (let p,_,_ = proof_of_id bag i2 in p)
  in
  aux p;
  List.iter
    (fun (_,_,id,_,_) -> aux (let p,_,_ = proof_of_id bag id in p))
    ol;
  (* now h is complete *)
  let proofs = Hashtbl.fold (fun k count acc-> (k,count)::acc) h [] in
  let proofs = List.filter (fun (_,c) -> c > 1) proofs in
  let res = topological_sort bag (List.map (fun (i,_) -> i) proofs) in
  res
;;

let build_proof_term bag eq h lift proof =
  let proof_of_id aux id =
    let p,l,r = proof_of_id bag id in
    try List.assoc id h,l,r with Not_found -> aux p, l, r
  in
  let rec aux = function
     | Exact term -> 
         CicSubstitution.lift lift term
     | Step (subst,(rule, id1, (pos,id2), pred)) ->
         let p1,_,_ = proof_of_id aux id1 in
         let p2,l,r = proof_of_id aux id2 in
         let varname = 
           match rule with
           | SuperpositionRight -> Cic.Name ("SupR" ^ Utils.string_of_pos pos) 
           | Demodulation -> Cic.Name ("DemEq"^ Utils.string_of_pos pos)
           | _ -> assert false
         in
         let pred = 
           match pred with
           | Cic.Lambda (_,a,b) -> Cic.Lambda (varname,a,b)
           | _ -> assert false
         in
         let p = build_proof_step eq lift subst p1 p2 pos l r pred in
(*         let cond =  (not (List.mem 302 (Utils.metas_of_term p)) || id1 = 8 || id1 = 132) in
           if not cond then
             prerr_endline ("ERROR " ^ string_of_int id1 ^ " " ^ string_of_int id2);
           assert cond;*)
           p
  in
   aux proof
;;

let build_goal_proof ?(contextualize=true) ?(forward=false) bag eq l initial ty se context menv =
  let se = List.map (fun i -> Cic.Meta (i,[])) se in 
  let lets = get_duplicate_step_in_wfo bag l initial in
  let letsno = List.length lets in
  let l = if forward then List.rev l else l in
  let lift_list l = List.map (fun (i,t) -> i,CicSubstitution.lift 1 t) l in
  let lets,_,h = 
    List.fold_left
      (fun (acc,n,h) id -> 
        let p,l,r = proof_of_id bag id in
        let cic = build_proof_term bag eq h n p in
        let real_cic,instance = 
          parametrize_proof cic l r 
        in
        let h = (id, instance)::lift_list h in
        acc@[id,real_cic],n+1,h) 
      ([],0,[]) lets
  in
  let lets =
   List.map (fun (id,cic) -> id,cic,Cic.Implicit (Some `Type)) lets
  in
  let proof,se = 
    let rec aux se current_proof = function
      | [] -> current_proof,se
      | (rule,pos,id,subst,pred)::tl ->
          let p,l,r = proof_of_id bag id in
           let p = build_proof_term bag eq h letsno p in
           let pos = if forward then pos else
	       if pos = Utils.Left then Utils.Right else Utils.Left in
         let varname = 
           match rule with
           | SuperpositionLeft -> Cic.Name ("SupL" ^ Utils.string_of_pos pos) 
           | Demodulation -> Cic.Name ("DemG"^ Utils.string_of_pos pos)
           | _ -> assert false
         in
         let pred = 
           match pred with
           | Cic.Lambda (_,a,b) -> Cic.Lambda (varname,a,b)
           | _ -> assert false
         in
           let proof = 
             build_proof_step eq letsno subst current_proof p pos l r pred
           in
           let proof,se = aux se proof tl in
           Subst.apply_subst_lift letsno subst proof,
           List.map (fun x -> Subst.apply_subst(*_lift letsno*) subst x) se
    in
    aux se (build_proof_term bag eq h letsno initial) l
  in
  let n,proof = 
    let initial = proof in
    List.fold_right
      (fun (id,cic,ty) (n,p) -> 
        n-1,
        Cic.LetIn (
          Cic.Name ("H"^string_of_int id),
          cic,
          ty,
          p))
    lets (letsno-1,initial)
  in
  let proof = 
    if contextualize 
    then contextualize_rewrites proof (CicSubstitution.lift letsno ty)
    else proof in
  canonical proof context menv, se
;;

let refl_proof eq_uri ty term = 
  Cic.Appl [Cic.MutConstruct (eq_uri, 0, 1, []); ty; term]
;;

let metas_of_proof bag p =
  let eq = 
    match LibraryObjects.eq_URI () with
    | Some u -> u 
    | None -> 
        raise 
          (ProofEngineTypes.Fail 
            (lazy "No default equality defined when calling metas_of_proof"))
  in
  let p = build_proof_term bag eq [] 0 p in
  Utils.metas_of_term p
;;

let remove_local_context eq =
   let w, p, (ty, left, right, o), menv,id = open_equality eq in
   let p = Utils.remove_local_context p in
   let ty = Utils.remove_local_context ty in
   let left = Utils.remove_local_context left in
   let right = Utils.remove_local_context right in
   w, p, (ty, left, right, o), menv, id
;;

let relocate newmeta menv to_be_relocated =
  let subst, newmetasenv, newmeta = 
    List.fold_right 
      (fun i (subst, metasenv, maxmeta) ->         
        let _,context,ty = CicUtil.lookup_meta i menv in
        let irl = [] in
        let newmeta = Cic.Meta(maxmeta,irl) in
        let newsubst = Subst.buildsubst i context newmeta ty subst in
        (* newsubst, (maxmeta,context,ty)::metasenv, maxmeta+1) *)
        newsubst, (maxmeta,[],ty)::metasenv, maxmeta+1) 
      to_be_relocated (Subst.empty_subst, [], newmeta+1)
  in
  (* let subst = Subst.flatten_subst subst in *)
  let menv = Subst.apply_subst_metasenv subst (menv @ newmetasenv) in
  subst, menv, newmeta

let fix_metas_goal (id_to_eq,newmeta) goal =
  let (proof, menv, ty) = goal in
  let to_be_relocated = List.map (fun i ,_,_ -> i) menv in
  let subst, menv, newmeta = relocate newmeta menv to_be_relocated in
  let ty = Subst.apply_subst subst ty in
  let proof = 
    match proof with
    | [] -> assert false (* is a nonsense to relocate the initial goal *)
    | (r,pos,id,s,p) :: tl -> (r,pos,id,Subst.concat subst s,p) :: tl
  in
  (id_to_eq,newmeta+1),(proof, menv, ty)
;;

let fix_metas (id_to_eq, newmeta) eq = 
  let w, p, (ty, left, right, o), menv,_ = open_equality eq in
  let to_be_relocated = List.map (fun i ,_,_ -> i) menv in
  let subst, metasenv, newmeta = relocate newmeta menv to_be_relocated in
  let ty = Subst.apply_subst subst ty in
  let left = Subst.apply_subst subst left in
  let right = Subst.apply_subst subst right in
  let fix_proof = function
    | Exact p -> Exact (Subst.apply_subst subst p)
    | Step (s,(r,id1,(pos,id2),pred)) -> 
        Step (Subst.concat s subst,(r,id1,(pos,id2), pred))
  in
  let p = fix_proof p in
  let bag = id_to_eq, newmeta in
  let bag, e = mk_equality bag (w, p, (ty, left, right, o), metasenv) in
  bag, e
;;

exception NotMetaConvertible;;

let meta_convertibility_aux table t1 t2 =
  let module C = Cic in
  let rec aux ((table_l,table_r) as table) t1 t2 =
    match t1, t2 with
    | C.Meta (m1, tl1), C.Meta (m2, tl2) when m1 = m2 -> table
    | C.Meta (m1, tl1), C.Meta (m2, tl2) when m1 < m2 -> aux table t2 t1
    | C.Meta (m1, tl1), C.Meta (m2, tl2) ->
        let m1_binding, table_l =
          try List.assoc m1 table_l, table_l
          with Not_found -> m2, (m1, m2)::table_l
        and m2_binding, table_r =
          try List.assoc m2 table_r, table_r
          with Not_found -> m1, (m2, m1)::table_r
        in
        if (m1_binding <> m2) || (m2_binding <> m1) then
          raise NotMetaConvertible
        else table_l,table_r
    | C.Var (u1, ens1), C.Var (u2, ens2)
    | C.Const (u1, ens1), C.Const (u2, ens2) when (UriManager.eq u1 u2) ->
        aux_ens table ens1 ens2
    | C.Cast (s1, t1), C.Cast (s2, t2)
    | C.Prod (_, s1, t1), C.Prod (_, s2, t2)
    | C.Lambda (_, s1, t1), C.Lambda (_, s2, t2) ->
        let table = aux table s1 s2 in
        aux table t1 t2
    | C.LetIn (_, s1, ty1, t1), C.LetIn (_, s2, ty2, t2) ->
        let table = aux table s1 s2 in
        let table = aux table ty1 ty2 in
        aux table t1 t2
    | C.Appl l1, C.Appl l2 -> (
        try List.fold_left2 (fun res t1 t2 -> (aux res t1 t2)) table l1 l2
        with Invalid_argument _ -> raise NotMetaConvertible
      )
    | C.MutInd (u1, i1, ens1), C.MutInd (u2, i2, ens2)
        when (UriManager.eq u1 u2) && i1 = i2 -> aux_ens table ens1 ens2
    | C.MutConstruct (u1, i1, j1, ens1), C.MutConstruct (u2, i2, j2, ens2)
        when (UriManager.eq u1 u2) && i1 = i2 && j1 = j2 ->
        aux_ens table ens1 ens2
    | C.MutCase (u1, i1, s1, t1, l1), C.MutCase (u2, i2, s2, t2, l2)
        when (UriManager.eq u1 u2) && i1 = i2 ->
        let table = aux table s1 s2 in
        let table = aux table t1 t2 in (
          try List.fold_left2 (fun res t1 t2 -> (aux res t1 t2)) table l1 l2
          with Invalid_argument _ -> raise NotMetaConvertible
        )
    | C.Fix (i1, il1), C.Fix (i2, il2) when i1 = i2 -> (
        try
          List.fold_left2
            (fun res (n1, i1, s1, t1) (n2, i2, s2, t2) ->
               if i1 <> i2 then raise NotMetaConvertible
               else
                 let res = (aux res s1 s2) in aux res t1 t2)
            table il1 il2
        with Invalid_argument _ -> raise NotMetaConvertible
      )
    | C.CoFix (i1, il1), C.CoFix (i2, il2) when i1 = i2 -> (
        try
          List.fold_left2
            (fun res (n1, s1, t1) (n2, s2, t2) ->
               let res = aux res s1 s2 in aux res t1 t2)
            table il1 il2
        with Invalid_argument _ -> raise NotMetaConvertible
      )
    | t1, t2 when t1 = t2 -> table
    | _, _ -> raise NotMetaConvertible
        
  and aux_ens table ens1 ens2 =
    let cmp (u1, t1) (u2, t2) =
      Pervasives.compare (UriManager.string_of_uri u1) (UriManager.string_of_uri u2)
    in
    let ens1 = List.sort cmp ens1
    and ens2 = List.sort cmp ens2 in
    try
      List.fold_left2
        (fun res (u1, t1) (u2, t2) ->
           if not (UriManager.eq u1 u2) then raise NotMetaConvertible
           else aux res t1 t2)
        table ens1 ens2
    with Invalid_argument _ -> raise NotMetaConvertible
  in
  aux table t1 t2
;;


let meta_convertibility_eq eq1 eq2 =
  let _, _, (ty, left, right, _), _,_ = open_equality eq1 in
  let _, _, (ty', left', right', _), _,_ = open_equality eq2 in
  if ty <> ty' then
    false
  else if (left = left') && (right = right') then
    true
  else if (left = right') && (right = left') then
    true
  else
    try
      let table = meta_convertibility_aux ([],[]) left left' in
      let _ = meta_convertibility_aux table right right' in
      true
    with NotMetaConvertible ->
      try
        let table = meta_convertibility_aux ([],[]) left right' in
        let _ = meta_convertibility_aux table right left' in
        true
      with NotMetaConvertible ->
        false
;;

let meta_convertibility t1 t2 =
  if t1 = t2 then
    true
  else
    try
      ignore(meta_convertibility_aux ([],[]) t1 t2);
      true
    with NotMetaConvertible ->
      false
;;

let meta_convertibility_subst t1 t2 menv =
  if t1 = t2 then
    Some([])
  else
    try
      let (l,_) = meta_convertibility_aux ([],[]) t1 t2 in
      let subst =
	List.map
	  (fun (x,y) ->
	     try 
	       let (_,c,t) = CicUtil.lookup_meta x menv in
	       let irl = 
		 CicMkImplicit.identity_relocation_list_for_metavariable c in
	       (y,(c,Cic.Meta(x,irl),t))
	     with CicUtil.Meta_not_found _ ->
	       try 
		 let (_,c,t) = CicUtil.lookup_meta y menv in
		 let irl =  
		   CicMkImplicit.identity_relocation_list_for_metavariable c in
		   (x,(c,Cic.Meta(y,irl),t))
	       with CicUtil.Meta_not_found _ -> assert false) l in   
	Some subst
    with NotMetaConvertible ->
      None
;;

exception TermIsNotAnEquality;;

let term_is_equality term =
  match term with
  | Cic.Appl [Cic.MutInd (uri, _, _); _; _; _] 
    when LibraryObjects.is_eq_URI uri -> true
  | _ -> false
;;

let equality_of_term bag proof term newmetas =
  match term with
  | Cic.Appl [Cic.MutInd (uri, _, _); ty; t1; t2] 
    when LibraryObjects.is_eq_URI uri ->
      let o = !Utils.compare_terms t1 t2 in
      let stat = (ty,t1,t2,o) in
      let w = Utils.compute_equality_weight stat in
      let bag, e = mk_equality bag (w, Exact proof, stat,newmetas) in
      bag, e
  | _ ->
      raise TermIsNotAnEquality
;;

let is_weak_identity eq = 
  let _,_,(_,left, right,_),_,_ = open_equality eq in
   left = right 
   (* doing metaconv here is meaningless *)
;;

let is_identity (_, context, ugraph) eq = 
  let _,_,(ty,left,right,_),menv,_ = open_equality eq in
  (* doing metaconv here is meaningless *)
  left = right
(*   fst (CicReduction.are_convertible ~metasenv:menv context left right ugraph)
 *   *)
;;


let term_of_equality eq_uri equality =
  let _, _, (ty, left, right, _), menv, _= open_equality equality in
  let eq i = function Cic.Meta (j, _) -> i = j | _ -> false in
  let argsno = List.length menv in
  let t =
    CicSubstitution.lift argsno
      (Cic.Appl [Cic.MutInd (eq_uri, 0, []); ty; left; right])
  in
  snd (
    List.fold_right
      (fun (i,_,ty) (n, t) ->
         let name = Cic.Name ("X" ^ (string_of_int n)) in
         let ty = CicSubstitution.lift (n-1) ty in
         let t = 
           ProofEngineReduction.replace
             ~equality:eq ~what:[i]
             ~with_what:[Cic.Rel (argsno - (n - 1))] ~where:t
         in
           (n-1, Cic.Prod (name, ty, t)))
      menv (argsno, t))
;;

let symmetric bag eq_ty l id uri m =
  let eq = Cic.MutInd(uri,0,[]) in
  let pred = 
    Cic.Lambda (Cic.Name "Sym",eq_ty,
     Cic.Appl [CicSubstitution.lift 1 eq ;
               CicSubstitution.lift 1 eq_ty;
               Cic.Rel 1;CicSubstitution.lift 1 l]) 
  in
  let prefl = 
    Exact (Cic.Appl
      [Cic.MutConstruct(uri,0,1,[]);eq_ty;l]) 
  in
  let bag, id1 = 
    let bag, eq = mk_equality bag (0,prefl,(eq_ty,l,l,Utils.Eq),m) in
    let (_,_,_,_,id) = open_equality eq in
    bag, id
  in
  bag, Step(Subst.empty_subst,
    (Demodulation,id1,(Utils.Left,id),pred))
;;

module IntOT = struct
  type t = int
  let compare = Pervasives.compare
end

module IntSet = Set.Make(IntOT);;

let n_purged = ref 0;;

let collect ((id_to_eq,maxmeta) as bag) alive1 alive2 alive3 =
  let deps_of id = 
    let p,_,_ = proof_of_id bag id in  
    match p with
    | Exact _ -> IntSet.empty
    | Step (_,(_,id1,(_,id2),_)) ->
          IntSet.add id1 (IntSet.add id2 IntSet.empty)
  in
  let rec close s = 
    let news = IntSet.fold (fun id s -> IntSet.union (deps_of id) s) s s in
    if IntSet.equal news s then s else close news
  in
  let l_to_s s l = List.fold_left (fun s x -> IntSet.add x s) s l in
  let alive_set = l_to_s (l_to_s (l_to_s IntSet.empty alive2) alive1) alive3 in
  let closed_alive_set = close alive_set in
  let to_purge = 
    M.fold 
      (fun k _ s -> 
        if not (IntSet.mem k closed_alive_set) then
          k::s else s) id_to_eq []
  in
  n_purged := !n_purged + List.length to_purge;
  List.fold_right M.remove to_purge id_to_eq, maxmeta
;;

let get_stats () = "" 
(*
  <:show<Equality.>> ^ 
  "# of purged eq by the collector: " ^ string_of_int !n_purged ^ "\n"
*)
;;

let rec pp_proofterm name t context = 
  let rec skip_lambda tys ctx = function
    | Cic.Lambda (n,s,t) -> skip_lambda (s::tys) ((Some n)::ctx) t
    | t -> ctx,tys,t
  in
  let rename s name = 
    match name with 
    | Cic.Name s1 -> Cic.Name (s ^ s1)
    | _ -> assert false
  in
  let rec skip_letin ctx = function
    | Cic.LetIn (n,b,_,t) -> 
        pp_proofterm (Some (rename "Lemma " n)) b ctx:: 
          skip_letin ((Some n)::ctx) t
    | t -> 
        let ppterm t = CicPp.pp t ctx in
        let rec pp inner = function
          | Cic.Appl [Cic.Const (uri,[]);_;l;m;r;p1;p2] 
              when Pcre.pmatch ~pat:"trans_eq" (UriManager.string_of_uri uri)->
                if not inner then
                  ("     " ^ ppterm l) :: pp true p1 @ 
                            [ "   = " ^ ppterm m ] @ pp true p2 @ 
                            [ "   = " ^ ppterm r ]
                else
                   pp true p1 @ 
                            [ "   = " ^ ppterm m ] @ pp true p2 
          | Cic.Appl [Cic.Const (uri,[]);_;l;m;p] 
              when Pcre.pmatch ~pat:"sym_eq" (UriManager.string_of_uri uri)->
                pp true p
          | Cic.Appl [Cic.Const (uri,[]);_;_;_;_;_;p] 
              when Pcre.pmatch ~pat:"eq_f" (UriManager.string_of_uri uri)->
                pp true p
          | Cic.Appl [Cic.Const (uri,[]);_;_;_;_;_;p] 
              when Pcre.pmatch ~pat:"eq_OF_eq" (UriManager.string_of_uri uri)->
                pp true p
          | Cic.Appl [Cic.MutConstruct (uri,_,_,[]);_;_;t;p] 
              when Pcre.pmatch ~pat:"ex.ind" (UriManager.string_of_uri uri)->
                      [ "witness " ^ ppterm t ] @ pp true p
          | Cic.Appl (t::_) ->[ " [by " ^ ppterm t ^ "]"]
          | t ->[ " [by " ^ ppterm t ^ "]"]
        in
        let rec compat = function
          | a::b::tl -> (b ^ a) :: compat tl
          | h::[] -> [h]
          | [] -> []
        in
        let compat l = List.hd l :: compat (List.tl l) in
        compat (pp false t) @ ["";""]
  in      
  let names, tys, body = skip_lambda [] context t in
  let ppname name = (match name with Some (Cic.Name s) -> s | _ -> "") in
  ppname name ^ ":\n" ^
  (if context = [] then
     let rec pp_l ctx = function
          | (t,name)::tl -> 
              "   " ^ ppname name ^ ": " ^ CicPp.pp t ctx ^ "\n" ^ 
              pp_l (name::ctx) tl
          | [] -> "\n\n"
     in
       pp_l [] (List.rev (List.combine tys names))
   else "")
    ^
  String.concat "\n" (skip_letin names body)
;;

let pp_proofterm t = 
  "\n\n" ^ 
  pp_proofterm (Some (Cic.Name "Hypothesis")) t []
;;

let initial_nameset_list = [
 "x"; "y"; "z"; "t"; "u"; "v"; "a"; "b"; "c"; "d"; 
 "e"; "l"; "m"; "n"; "o"; "p"; "q"; "r"; 
]

module S = Set.Make(String)

let initial_nameset = List.fold_right S.add initial_nameset_list S.empty, [];;

let freshname (nameset, subst) term = 
  let m = CicUtil.metas_of_term term in
  let nameset, subst = 
    List.fold_left 
      (fun (set,rc) (m,_) -> 
        if List.mem_assoc m rc then set,rc else
        let name = S.choose set in
        let set = S.remove name set in
        set, 
        (m,Cic.Const(UriManager.uri_of_string 
             ("cic:/"^name^".con"),[]))::rc)
      (nameset,subst) m
  in
  let term = 
   ProofEngineReduction.replace
    ~equality:(fun i t -> match t with Cic.Meta (j,_) -> i=j| _ -> false) 
    ~what:(List.map fst subst) 
    ~with_what:(List.map snd subst) ~where:term
  in
  (nameset, subst), term
;;

let remove_names_in_context (set,subst) names =
  List.fold_left
    (fun s n -> 
      match n with Some (Cic.Name n) -> S.remove n s | _ -> s) 
    set names, subst
;;

let string_of_id2 (id_to_eq,_) names nameset id = 
  if id = 0 then "" else 
  try
    let (_,_,(_,l,r,_),_,_) = open_equality (M.find id id_to_eq) in
    let nameset, l = freshname nameset l in
    let nameset, r = freshname nameset r in
    Printf.sprintf "%s = %s" (CicPp.pp l names) (CicPp.pp r names)
  with
      Not_found -> assert false
;;

let draw_proof bag names goal_proof proof id =
  let b = Buffer.create 100 in
  let fmt = Format.formatter_of_buffer b in 
  let sint = string_of_int in
  let fst3 (x,_,_) = x in
  let visited = ref [] in
  let nameset = remove_names_in_context initial_nameset names in
  let rec fact id = function
    | Exact t -> 
        if not (List.mem id !visited) then
          begin
          visited := id :: !visited;
          let nameset, t = freshname nameset t in
          let t = CicPp.pp t names in
          GraphvizPp.Dot.node (sint id) 
          ~attrs:["label",t^":"^string_of_id2 bag names nameset id;
          "shape","rectangle"] fmt;
          end
    | Step (_,(_,id1,(_,id2),_)) ->
        GraphvizPp.Dot.edge (sint id) (sint id1) fmt;
        GraphvizPp.Dot.edge (sint id) (sint id2) fmt;
        let p1,_,_ = proof_of_id bag id1 in
        let p2,_,_ = proof_of_id bag id2 in
        fact id1 p1;
        fact id2 p2;
        if not (List.mem id !visited); then
          begin
          visited := id :: !visited;
          GraphvizPp.Dot.node (sint id) 
          ~attrs:["label",sint id^":"^string_of_id2 bag names nameset id;
                  "shape","ellipse"] fmt
          end
  in
  let sleft acc (_,_,id,_,_) =
    if acc != 0 then GraphvizPp.Dot.edge (sint acc) (sint id) fmt;
    fact id (fst3 (proof_of_id bag id));
    id
  in
  GraphvizPp.Dot.header ~node_attrs:["fontsize","10"; ] fmt;
  ignore(List.fold_left sleft id goal_proof);
  GraphvizPp.Dot.trailer fmt;
  let oc = open_out "/tmp/matita_paramod.dot" in
  Buffer.output_buffer oc b;
  close_out oc;
  Utils.debug_print (lazy "dot!");
  ignore(Unix.system 
    "dot -Tps -o /tmp/matita_paramod.eps /tmp/matita_paramod.dot"
(* "cat /tmp/matita_paramod.dot| tred | dot -Tps -o /tmp/matita_paramod.eps" *)
  );
  ignore(Unix.system "gv /tmp/matita_paramod.eps");
;;

let saturate_term (id_to_eq, maxmeta) metasenv subst context term = 
  let maxmeta = max maxmeta (CicMkImplicit.new_meta metasenv subst) in
  let head, metasenv, args, newmeta =
    TermUtil.saturate_term maxmeta metasenv context term 0
  in
  (id_to_eq, newmeta), head, metasenv, args
;;

let push_maxmeta (id_to_eq, maxmeta) m = id_to_eq, max maxmeta m ;;
let filter_metasenv_gt_maxmeta (_,maxmeta) =
  List.filter (fun (j,_,_) -> j >= maxmeta)
;;
let maxmeta = snd;;
