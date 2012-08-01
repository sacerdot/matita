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

(* $Id: cicPp.ml 7413 2007-05-29 15:30:53Z tassi $ *)

let fix_sorts t = t;;
let apply_subst subst t = assert (subst=[]); t;;

type typformerreference = NReference.reference
type reference = NReference.reference

type kind =
   Type
 | KArrow of kind * kind
 | KSkip of kind (* dropped abstraction *)

type typ =
   Var of int
 | Top
 | TConst of typformerreference
 | Arrow of typ * typ
 | Skip of typ
 | Forall of string * kind * typ
 | TAppl of typ list

type term =
   Rel of int
 | Const of reference
 | Lambda of string * (* typ **) term
 | Appl of term list
 | LetIn of string * (* typ **) term * term
 | Match of reference * term * term list
 | TLambda of (* string **) term
 | Inst of (*typ_former **) term

let unitty =
 NCic.Const (NReference.reference_of_spec (NUri.uri_of_string "cic:/matita/basics/types/unit.ind") (NReference.Ind (true,0,0)));;

(* None = dropped abstraction *)
type typ_context = (string * kind) option list
type term_context = (string * [`OfKind of kind | `OfType of typ]) option list

type typ_former_decl = typ_context * kind
type typ_former_def = typ_former_decl * typ

type term_former_decl = term_context * typ
type term_former_def = term_former_decl * term

type obj_kind =
   TypeDeclaration of typ_former_decl
 | TypeDefinition of typ_former_def
 | TermDeclaration of term_former_decl
 | TermDefinition of term_former_def
 | LetRec of (string * typ * term) list
 (* inductive and records missing *)

type obj = NUri.uri * obj_kind

exception NotInFOmega

let rec classify_not_term status no_dep_prods context t =
 match NCicReduction.whd status ~subst:[] context t with
  | NCic.Sort s ->
     (match s with
         NCic.Prop
       | NCic.Type [`CProp,_] -> `PropKind
       | NCic.Type [`Type,_] ->
          if no_dep_prods then `Kind
          else
           raise NotInFOmega (* ?? *)
       | NCic.Type _ -> assert false)
  | NCic.Prod (b,s,t) ->
     (*CSC: using invariant on "_" *)
     classify_not_term status (no_dep_prods && b.[0] = '_')
      ((b,NCic.Decl s)::context) t
  | NCic.Implicit _
  | NCic.LetIn _
  | NCic.Lambda _
  | NCic.Const (NReference.Ref (_,NReference.CoFix _))
  | NCic.Appl [] -> assert false (* NOT POSSIBLE *)
  | NCic.Match _
  | NCic.Const (NReference.Ref (_,NReference.Fix _)) ->
     (* be aware: we can be the head of an application *)
     assert false (* TODO *)
  | NCic.Meta _ -> assert false (* TODO *)
  | NCic.Appl (he::_) -> classify_not_term status no_dep_prods context he
  | NCic.Rel _ -> `KindOrType
  | NCic.Const (NReference.Ref (_,NReference.Decl _) as ref) ->
     let _,_,ty,_,_ = NCicEnvironment.get_checked_decl status ref in
      (match classify_not_term status true [] ty with
        | `Proposition
        | `Type -> assert false (* IMPOSSIBLE *)
        | `Kind
        | `KindOrType -> `KindOrType
        | `PropKind -> `Proposition)
  | NCic.Const (NReference.Ref (_,NReference.Ind _) as ref) ->
     let _,_,ityl,_,i = NCicEnvironment.get_checked_indtys status ref in
     let _,_,arity,_ = List.nth ityl i in
      (match classify_not_term status true [] arity with
        | `Proposition
        | `Type
        | `KindOrType -> assert false (* IMPOSSIBLE *)
        | `Kind -> `Type
        | `PropKind -> `Proposition)
  | NCic.Const (NReference.Ref (_,NReference.Con _))
  | NCic.Const (NReference.Ref (_,NReference.Def _)) ->
     assert false (* NOT POSSIBLE *)
;;

type not_term = [`Kind | `KindOrType | `PropKind | `Proposition | `Type];;

let classify status ~metasenv context t =
 match NCicTypeChecker.typeof status ~metasenv ~subst:[] context t with
  | NCic.Sort _ ->
     (classify_not_term status true context t : not_term :> [> not_term])
  | ty ->
     let ty = fix_sorts ty in
prerr_endline ("XXX: " ^ status#ppterm ~metasenv:[] ~subst:[] ~context:[] ty);
      `Term
        (match classify_not_term status true context ty with
          | `Proposition -> `Proof
          | `Type -> `Term
          | `KindOrType -> `TypeFormerOrTerm
          | `Kind -> `TypeFormer
          | `PropKind -> `PropFormer)
;;
      

let rec kind_of status ~metasenv context k =
 match NCicReduction.whd status ~subst:[] context k with
  | NCic.Sort _ -> Type
  | NCic.Prod (b,s,t) ->
     (* CSC: non-invariant assumed here about "_" *)
     (match classify status ~metasenv context s with
       | `Kind
       | `KindOrType -> (* KindOrType OK?? *)
           KArrow (kind_of status ~metasenv context s,
            kind_of ~metasenv status ((b,NCic.Decl s)::context) t)
       | `Type
       | `Proposition
       | `PropKind ->
           KSkip (kind_of status ~metasenv ((b,NCic.Decl s)::context) t)
       | `Term _ -> assert false (* IMPOSSIBLE *))
  | NCic.Implicit _
  | NCic.LetIn _ -> assert false (* IMPOSSIBLE *)
  | NCic.Lambda _
  | NCic.Rel _
  | NCic.Const _ -> assert false (* NOT A KIND *)
  | NCic.Appl _ -> assert false (* TODO: when head is a match/let rec;
                                   otherwise NOT A KIND *)
  | NCic.Meta _
  | NCic.Match (_,_,_,_) -> assert false (* TODO *)
;;

let rec skip_args status ~metasenv context =
 function
  | _,[] -> []
  | [],_ -> assert false (* IMPOSSIBLE *)
  | None::tl1,_::tl2 -> skip_args status ~metasenv context (tl1,tl2)
  | _::tl1,arg::tl2 ->
     match classify status ~metasenv context arg with
      | `KindOrType
      | `Type
      | `Term `TypeFormer -> arg::skip_args status ~metasenv context (tl1,tl2)
      | `Kind
      | `Proposition
      | `PropKind -> unitty::skip_args status ~metasenv context (tl1,tl2)
      | `Term _ -> assert false (* IMPOSSIBLE *)
;;

module ReferenceMap = Map.Make(struct type t = NReference.reference let compare = NReference.compare end)

type db = typ_context ReferenceMap.t

class type g_status =
 object
  method extraction_db: db
 end

class virtual status =
 object
  inherit NCic.status
  val extraction_db = ReferenceMap.empty
  method extraction_db = extraction_db
  method set_extraction_db v = {< extraction_db = v >}
  method set_extraction_status
   : 'status. #g_status as 'status -> 'self
   = fun o -> {< extraction_db = o#extraction_db >}
 end

let rec split_kind_prods context =
 function
  | KArrow (so,ta)-> split_kind_prods (Some ("_",so)::context) ta
  | KSkip ta -> split_kind_prods (None::context) ta
  | Type -> context,Type
;;

let rec split_typ_prods context =
 function
  | Arrow (so,ta)-> split_typ_prods (Some ("_",`OfType so)::context) ta
  | Forall (name,so,ta)-> split_typ_prods (Some (name,`OfKind so)::context) ta
  | Skip ta -> split_typ_prods (None::context) ta
  | _ as t -> context,t
;;

let rec split_typ_lambdas status n ~metasenv context typ =
 if n = 0 then context,typ
 else
  match NCicReduction.whd status ~delta:max_int ~subst:[] context typ with
   | NCic.Lambda (name,s,t) ->
      split_typ_lambdas status (n-1) ~metasenv ((name,NCic.Decl s)::context) t
   | t ->
      (* eta-expansion required *)
      let ty = NCicTypeChecker.typeof status ~metasenv ~subst:[] context t in
      match NCicReduction.whd status ~delta:max_int ~subst:[] context ty with
       | NCic.Prod (name,typ,_) ->
          split_typ_lambdas status (n-1) ~metasenv
           ((name,NCic.Decl typ)::context)
           (NCicUntrusted.mk_appl t [NCic.Rel 1])
       | _ -> assert false (* IMPOSSIBLE *)
;;


let context_of_typformer status ~metasenv context =
 function
    NCic.Const (NReference.Ref (_,NReference.Ind _) as ref)
  | NCic.Const (NReference.Ref (_,NReference.Def _) as ref)
  | NCic.Const (NReference.Ref (_,NReference.Decl _) as ref)
  | NCic.Const (NReference.Ref (_,NReference.Fix _) as ref) ->
     (try ReferenceMap.find ref status#extraction_db
      with
       Not_found -> assert false (* IMPOSSIBLE *))
  | NCic.Match _ -> assert false (* TODO ???? *)
  | NCic.Rel n ->
     let typ =
      match List.nth context (n-1) with
         _,NCic.Decl typ -> typ
       | _,NCic.Def _ -> assert false (* IMPOSSIBLE *) in
     let typ_ctx = snd (HExtlib.split_nth n context) in
     let typ = kind_of status ~metasenv typ_ctx typ in
      fst (split_kind_prods [] typ)
  | NCic.Meta _ -> assert false (* TODO *)
  | NCic.Const (NReference.Ref (_,NReference.Con _))
  | NCic.Const (NReference.Ref (_,NReference.CoFix _))
  | NCic.Sort _ | NCic.Implicit _ | NCic.Lambda _ | NCic.LetIn _
  | NCic.Appl _ | NCic.Prod _ ->
     assert false (* IMPOSSIBLE *)

let rec typ_of status ~metasenv context k =
 match NCicReduction.whd status ~delta:max_int ~subst:[] context k with
  | NCic.Prod (b,s,t) ->
     (* CSC: non-invariant assumed here about "_" *)
     (match classify status ~metasenv context s with
       | `Kind ->
           Forall (b, kind_of status ~metasenv context s,
            typ_of ~metasenv status ((b,NCic.Decl s)::context) t)
       | `Type
       | `KindOrType -> (* ??? *)
           Arrow (typ_of status ~metasenv context s,
            typ_of status ~metasenv ((b,NCic.Decl s)::context) t)
       | `PropKind
       | `Proposition ->
           Skip (typ_of status ~metasenv ((b,NCic.Decl s)::context) t)
       | `Term _ -> assert false (* IMPOSSIBLE *))
  | NCic.Sort _
  | NCic.Implicit _
  | NCic.LetIn _ -> assert false (* IMPOSSIBLE *)
  | NCic.Lambda _ -> assert false (* NOT A TYPE *)
  | NCic.Rel n -> Var n
  | NCic.Const ref -> TConst ref
  | NCic.Appl (he::args) ->
     let he_context = context_of_typformer status ~metasenv context he in
     TAppl (typ_of status ~metasenv context he ::
      List.map (typ_of status ~metasenv context)
       (skip_args status ~metasenv context (List.rev he_context,args)))
  | NCic.Appl _ -> assert false (* TODO: when head is a match/let rec;
                                   otherwise NOT A TYPE *)
  | NCic.Meta _
  | NCic.Match (_,_,_,_) -> assert false (* TODO *)
;;

let rec term_of status ~metasenv context =
 function
  | NCic.Implicit _
  | NCic.Sort _
  | NCic.Prod _ -> assert false (* IMPOSSIBLE *)
  | NCic.Lambda (b,ty,bo) ->
     (* CSC: non-invariant assumed here about "_" *)
     (match classify status ~metasenv context ty with
       | `Kind ->
           TLambda (term_of status ~metasenv ((b,NCic.Decl ty)::context) bo)
       | `KindOrType (* ??? *)
       | `Type ->
           Lambda (b, term_of status ~metasenv ((b,NCic.Decl ty)::context) bo)
       | `PropKind
       | `Proposition ->
           (* CSC: LAZY ??? *)
           term_of status ~metasenv ((b,NCic.Decl ty)::context) bo
       | `Term _ -> assert false (* IMPOSSIBLE *))
  | NCic.LetIn (b,ty,t,bo) ->
     (match classify status ~metasenv context t with
       | `Term `Term ->
          LetIn (b,term_of status ~metasenv context t,
           term_of status ~metasenv ((b,NCic.Def (t,ty))::context) bo)
       | `Kind
       | `Type
       | `KindOrType
       | `PropKind
       | `Proposition
       | `Term `PropFormer
       | `Term `TypeFormer
       | `Term `TypeFormerOrTerm
       | `Term `Proof -> assert false (* EXPAND IT ??? *))
  | NCic.Rel n -> Rel n
  | NCic.Const ref -> Const ref
  | NCic.Appl (he::args) ->
     assert false (* TODO
     let he_context = context_of_typformer status ~metasenv context he in
     TAppl (typ_of status ~metasenv context he ::
      List.map (typ_of status ~metasenv context)
       (skip_args status ~metasenv context (List.rev he_context,args)))*)
  | NCic.Appl _ -> assert false (* TODO: when head is a match/let rec;
                                   otherwise NOT A TYPE *)
  | NCic.Meta _ -> assert false (* TODO *)
  | NCic.Match (ref,_,t,pl) ->
     Match (ref,term_of status ~metasenv context t,
      List.map (term_of status ~metasenv context) pl)
;;

let obj_of status (uri,height,metasenv,subst,obj_kind) =
 let obj_kind = apply_subst subst obj_kind in
 try
  match obj_kind with
   | NCic.Constant (_,_,None,ty,_) ->
      (match classify status ~metasenv [] ty with
        | `Kind ->
            let ty = kind_of status ~metasenv [] ty in
            let ctx,_ as res = split_kind_prods [] ty in
            let ref = NReference.reference_of_spec uri NReference.Decl in
             status#set_extraction_db
              (ReferenceMap.add ref ctx status#extraction_db),
             Some (uri, TypeDeclaration res)
        | `KindOrType -> assert false (* TODO ??? *)
        | `PropKind
        | `Proposition -> status, None
        | `Type ->
            let ty = typ_of status ~metasenv [] ty in
             status,
             Some (uri, TermDeclaration (split_typ_prods [] ty))
        | `Term _ -> assert false (* IMPOSSIBLE *))
   | NCic.Constant (_,_,Some bo,ty,_) ->
      (match classify status ~metasenv [] ty with
        | `Kind ->
            let ty = kind_of status ~metasenv [] ty in
            let ctx0,_ as res = split_kind_prods [] ty in
            let ctx,bo =
             split_typ_lambdas status ~metasenv (List.length ctx0) [] bo in
            (match classify status ~metasenv ctx bo with
              | `Type
              | `KindOrType -> (* ?? no kind formers in System F_omega *)
                  let ref =
                   NReference.reference_of_spec uri (NReference.Def height) in
                   status#set_extraction_db
                    (ReferenceMap.add ref ctx0 status#extraction_db),
                   Some (uri,TypeDefinition(res,typ_of status ~metasenv ctx bo))
              | `Kind -> status, None
              | `PropKind
              | `Proposition -> status, None
              | `Term _ -> assert false (* IMPOSSIBLE *))
        | `PropKind
        | `Proposition -> status, None
        | `KindOrType (* ??? *)
        | `Type ->
           (* CSC: TO BE FINISHED, REF NON REGISTERED *)
           let ty = typ_of status ~metasenv [] ty in
            status,
            Some (uri, TermDefinition (split_typ_prods [] ty,
             term_of status ~metasenv [](* BAD! *) bo))
        | `Term _ -> assert false (* IMPOSSIBLE *))
 with
  NotInFOmega ->
   prerr_endline "NOT IN F_omega";
   status, None

(************************ HASKELL *************************)

let pp_ref status = NCicPp.r2s status false

(* cons avoid duplicates *)
let rec (@::) name l =
 if name.[0] = '_' then "a" @:: l
 else if List.mem name l then (name ^ "'") @:: l
 else name::l
;;


let rec pp_kind =
 function
   Type -> "*"
 | KArrow (k1,k2) -> "(" ^ pp_kind k1 ^ ") -> " ^ pp_kind k2
 | KSkip k -> pp_kind k

let rec pp_typ status ctx =
 function
   Var n -> List.nth ctx (n-1)
 | Top -> assert false (* ??? *)
 | TConst ref -> pp_ref status ref
 | Arrow (t1,t2) -> "(" ^ pp_typ status ctx t1 ^ ") -> " ^ pp_typ status ("_"::ctx) t2
 | Skip t -> pp_typ status ("_"::ctx) t
 | Forall (name,_,t) -> "(forall " ^ name ^ ". " ^ pp_typ status (name@::ctx) t ^")"
 | TAppl tl -> "(" ^ String.concat " " (List.map (pp_typ status ctx) tl) ^ ")"

let rec pp_term status ctx =
 function
   Rel n -> List.nth ctx (n-1)
 | Const ref -> pp_ref status ref
 | Lambda (name,t) -> "(\\" ^ name ^ " -> " ^ pp_term status (name@::ctx) t ^ ")"
 | Appl tl -> "(" ^ String.concat " " (List.map (pp_term status ctx) tl) ^ ")"
 | LetIn (name,s,t) ->
    "(let " ^ name ^ " = " ^ pp_term status ctx s ^ " in " ^ pp_term status (name@::ctx) t ^
    ")"
 | Match _ -> assert false (* TODO of reference * term * term list *)
 | TLambda t -> pp_term status ctx t
 | Inst t -> pp_term status ctx t

(*
type term_context = (string * [`OfKind of kind | `OfType of typ]) option list

type term_former_def = term_context * term * typ
type term_former_decl = term_context * typ
*)

let pp_obj status (uri,obj_kind) =
 let printctx ctx =
  String.concat " " (List.rev
   (List.fold_right (fun (x,_) l -> x@::l)
     (HExtlib.filter_map (fun x -> x) ctx) [])) in
 let namectx_of_ctx ctx =
  List.fold_right (@::)
   (List.map (function None -> "_" | Some (x,_) -> x) ctx) [] in
 match obj_kind with
   TypeDeclaration (ctx,_) ->
    (* data?? unsure semantics *)
    "data " ^ NUri.name_of_uri uri ^ " " ^ printctx ctx
 | TypeDefinition ((ctx,_),ty) ->
    let namectx = namectx_of_ctx ctx in
    "type " ^ NUri.name_of_uri uri ^ " " ^ printctx ctx ^ " = " ^
       pp_typ status namectx ty
 | TermDeclaration (ctx,ty) ->
    (*CSC: Ask Dominic about the syntax *)
    let namectx = namectx_of_ctx ctx in
    "let " ^ NUri.name_of_uri uri ^ " " ^ printctx ctx ^
    " : " ^ pp_typ status namectx ty
 | TermDefinition ((ctx,ty),bo) ->
    (*CSC: Ask Dominic about the syntax *)
    let namectx = namectx_of_ctx ctx in
    "let " ^ NUri.name_of_uri uri ^ " " ^ printctx ctx ^
    " : " ^ pp_typ status namectx ty ^ " = " ^
    pp_term status namectx bo
 | LetRec _ -> assert false (* TODO 
 (* inductive and records missing *)*)

let haskell_of_obj status obj =
 let status, obj = obj_of status obj in
  status,HExtlib.map_option (pp_obj status) obj

(*
let rec typ_of context =
 function
(*
    C.Rel n ->
       begin
        try
         (match get_nth context n with
             Some (C.Name s,_) -> ppid s
           | Some (C.Anonymous,_) -> "__" ^ string_of_int n
           | None -> "_hidden_" ^ string_of_int n
         )
        with
         NotEnoughElements -> string_of_int (List.length context - n)
       end
    | C.Meta (n,l1) ->
       (match metasenv with
           None ->
            "?" ^ (string_of_int n) ^ "[" ^ 
             String.concat " ; "
              (List.rev_map
                (function
                    None -> "_"
                  | Some t -> pp ~in_type:false t context) l1) ^
             "]"
         | Some metasenv ->
            try
             let _,context,_ = CicUtil.lookup_meta n metasenv in
              "?" ^ (string_of_int n) ^ "[" ^ 
               String.concat " ; "
                (List.rev
                  (List.map2
                    (fun x y ->
                      match x,y with
                         _, None
                       | None, _ -> "_"
                       | Some _, Some t -> pp ~in_type:false t context
                    ) context l1)) ^
               "]"
            with
	      CicUtil.Meta_not_found _ 
            | Invalid_argument _ ->
              "???" ^ (string_of_int n) ^ "[" ^ 
               String.concat " ; "
                (List.rev_map (function None -> "_" | Some t ->
                  pp ~in_type:false t context) l1) ^
               "]"
       )
    | C.Sort s ->
       (match s with
           C.Prop  -> "Prop"
         | C.Set   -> "Set"
         | C.Type _ -> "Type"
         (*| C.Type u -> ("Type" ^ CicUniv.string_of_universe u)*)
	 | C.CProp _ -> "CProp" 
       )
    | C.Implicit (Some `Hole) -> "%"
    | C.Implicit _ -> "?"
    | C.Prod (b,s,t) ->
       (match b, is_term s with
           _, true -> typ_of (None::context) t
         | "_",_ -> Arrow (typ_of context s) (typ_of (Some b::context) t)
         | _,_ -> Forall (b,typ_of (Some b::context) t)
    | C.Lambda (b,s,t) ->
       (match analyze_type context s with
           `Sort _
         | `Statement -> pp ~in_type t ((Some (b,Cic.Decl s))::context)
         | `Optimize -> prerr_endline "XXX lambda";assert false
         | `Type ->
            "(function " ^ ppname b ^ " -> " ^
             pp ~in_type t ((Some (b,Cic.Decl s))::context) ^ ")")
    | C.LetIn (b,s,ty,t) ->
       (match analyze_term context s with
         | `Type
         | `Proof -> pp ~in_type t ((Some (b,Cic.Def (s,ty)))::context)
         | `Optimize 
         | `Term ->
            "(let " ^ ppname b ^ (*" : " ^ pp ~in_type:true ty context ^*)
            " = " ^ pp ~in_type:false s context ^ " in " ^
             pp ~in_type t ((Some (b,Cic.Def (s,ty)))::context) ^ ")")
    | C.Appl (he::tl) when in_type ->
       let hes = pp ~in_type he context in
       let stl = String.concat "," (clean_args_for_ty context tl) in
        (if stl = "" then "" else "(" ^ stl ^ ") ") ^ hes
    | C.Appl (C.MutInd _ as he::tl) ->
       let hes = pp ~in_type he context in
       let stl = String.concat "," (clean_args_for_ty context tl) in
        (if stl = "" then "" else "(" ^ stl ^ ") ") ^ hes
    | C.Appl (C.MutConstruct (uri,n,_,_) as he::tl) ->
       let nparams =
        match fst(CicEnvironment.get_obj CicUniv.oblivion_ugraph uri) with
           C.InductiveDefinition (_,_,nparams,_) -> nparams
         | _ -> assert false in
       let hes = pp ~in_type he context in
       let stl = String.concat "," (clean_args_for_constr nparams context tl) in
        "(" ^ hes ^ (if stl = "" then "" else "(" ^ stl ^ ")") ^ ")"
    | C.Appl li ->
       "(" ^ String.concat " " (clean_args context li) ^ ")"
    | C.Const (uri,exp_named_subst) ->
       qualified_name_of_uri current_module_uri uri ^
        pp_exp_named_subst exp_named_subst context
    | C.MutInd (uri,n,exp_named_subst) ->
       (try
         match fst(CicEnvironment.get_obj CicUniv.oblivion_ugraph uri) with
            C.InductiveDefinition (dl,_,_,_) ->
             let (name,_,_,_) = get_nth dl (n+1) in
              qualified_name_of_uri current_module_uri
               (UriManager.uri_of_string
                 (UriManager.buri_of_uri uri ^ "/" ^ name ^ ".con")) ^
              pp_exp_named_subst exp_named_subst context
          | _ -> raise CicExportationInternalError
        with
           Sys.Break as exn -> raise exn
         | _ -> UriManager.string_of_uri uri ^ "#1/" ^ string_of_int (n + 1)
       )
    | C.MutConstruct (uri,n1,n2,exp_named_subst) ->
       (try
         match fst(CicEnvironment.get_obj CicUniv.oblivion_ugraph uri) with
            C.InductiveDefinition (dl,_,_,_) ->
             let _,_,_,cons = get_nth dl (n1+1) in
              let id,_ = get_nth cons n2 in
               qualified_name_of_uri current_module_uri ~capitalize:true
                (UriManager.uri_of_string
                  (UriManager.buri_of_uri uri ^ "/" ^ id ^ ".con")) ^
               pp_exp_named_subst exp_named_subst context
          | _ -> raise CicExportationInternalError
        with
           Sys.Break as exn -> raise exn
         | _ ->
          UriManager.string_of_uri uri ^ "#1/" ^ string_of_int (n1 + 1) ^ "/" ^
           string_of_int n2
       )
    | C.MutCase (uri,n1,ty,te,patterns) ->
       if in_type then
        "unit (* TOO POLYMORPHIC TYPE *)"
       else (
       let rec needs_obj_magic ty =
        match CicReduction.whd context ty with
         | Cic.Lambda (_,_,(Cic.Lambda(_,_,_) as t)) -> needs_obj_magic t
         | Cic.Lambda (_,_,t) -> not (DoubleTypeInference.does_not_occur 1 t)
         | _ -> false (* it can be a Rel, e.g. in *_rec *)
       in
       let needs_obj_magic = needs_obj_magic ty in
       (match analyze_term context te with
           `Type -> assert false
         | `Proof ->
             (match patterns with
                 [] -> "assert false"   (* empty type elimination *)
               | [he] ->
                  pp ~in_type:false he context  (* singleton elimination *)
               | _ -> assert false)
         | `Optimize 
         | `Term ->
            if patterns = [] then "assert false"
            else
             (let connames_and_argsno, go_up, go_pu, go_down, go_nwod =
               (match fst(CicEnvironment.get_obj CicUniv.oblivion_ugraph uri) with
                   C.InductiveDefinition (dl,_,paramsno,_) ->
                    let (_,_,_,cons) = get_nth dl (n1+1) in
                    let rc = 
                     List.map
                      (fun (id,ty) ->
                        (* this is just an approximation since we do not have
                           reduction yet! *)
                        let rec count_prods toskip =
                         function
                            C.Prod (_,_,bo) when toskip > 0 ->
                             count_prods (toskip - 1) bo
                          | C.Prod (_,_,bo) -> 1 + count_prods 0 bo
                          | _ -> 0
                        in
                         qualified_name_of_uri current_module_uri
                          ~capitalize:true
                          (UriManager.uri_of_string
                            (UriManager.buri_of_uri uri ^ "/" ^ id ^ ".con")),
                         count_prods paramsno ty
                      ) cons
                    in
                    if not (is_mcu_type uri) then rc, "","","",""
                    else rc, !current_go_up, "))", "( .< (", " ) >.)"
                 | _ -> raise CicExportationInternalError
               )
              in
               let connames_and_argsno_and_patterns =
                let rec combine =
                   function
                      [],[] -> []
                    | (x,no)::tlx,y::tly -> (x,no,y)::(combine (tlx,tly))
                    | _,_ -> assert false
                in
                 combine (connames_and_argsno,patterns)
               in
                go_up ^
                "\n(match " ^ pp ~in_type:false te context ^ " with \n   " ^
                 (String.concat "\n | "
                  (List.map
                   (fun (x,argsno,y) ->
                     let rec aux argsno context =
                      function
                         Cic.Lambda (name,ty,bo) when argsno > 0 ->
                          let name =
                           match name with
                              Cic.Anonymous -> Cic.Anonymous
                            | Cic.Name n -> Cic.Name (ppid n) in
                          let args,res =
                           aux (argsno - 1) (Some (name,Cic.Decl ty)::context)
                            bo
                          in
                           (match analyze_type context ty with
                             | `Optimize -> prerr_endline "XXX contructor with l2 arg"; assert false
                             | `Statement
                             | `Sort _ -> args,res
                             | `Type ->
                                 (match name with
                                     C.Anonymous -> "_"
                                   | C.Name s -> s)::args,res)
                       | t when argsno = 0 -> [],pp ~in_type:false t context
                       | t ->
                          ["{" ^ string_of_int argsno ^ " args missing}"],
                           pp ~in_type:false t context
                     in
                      let pattern,body =
                       if argsno = 0 then x,pp ~in_type:false y context
                       else
                        let args,body = aux argsno context y in
                        let sargs = String.concat "," args in
                         x ^ (if sargs = "" then "" else "(" ^ sargs^ ")"),
                          body
                      in
                       pattern ^ " -> " ^ go_down ^
                        (if needs_obj_magic then
                         "Obj.magic (" ^ body ^ ")"
                        else
                         body) ^ go_nwod
                   ) connames_and_argsno_and_patterns)) ^
                 ")\n"^go_pu)))
    | C.Fix (no, funs) ->
       let names,_ =
        List.fold_left
         (fun (types,len) (n,_,ty,_) ->
            (Some (C.Name n,(C.Decl (CicSubstitution.lift len ty)))::types,
             len+1)
         ) ([],0) funs
       in
         "let rec " ^
         List.fold_right
          (fun (name,ind,ty,bo) i -> name ^ " = \n" ^
            pp ~in_type:false bo (names@context) ^ i)
          funs "" ^
         " in " ^
         (match get_nth names (no + 1) with
             Some (Cic.Name n,_) -> n
           | _ -> assert false)
    | C.CoFix (no,funs) ->
       let names,_ =
        List.fold_left
         (fun (types,len) (n,ty,_) ->
            (Some (C.Name n,(C.Decl (CicSubstitution.lift len ty)))::types,
             len+1)
         ) ([],0) funs
       in
         "\nCoFix " ^ " {" ^
         List.fold_right
          (fun (name,ty,bo) i -> "\n" ^ name ^ 
            " : " ^ pp ~in_type:true ty context ^ " := \n" ^
            pp ~in_type:false bo (names@context) ^ i)
          funs "" ^
         "}\n"
*)

(*
exception CicExportationInternalError;;
exception NotEnoughElements;;

(* *)

let is_mcu_type u = 
  UriManager.eq (UriManager.uri_of_string
  "cic:/matita/freescale/opcode/mcu_type.ind") u
;;

(* Utility functions *)

let analyze_term context t =
 match fst(CicTypeChecker.type_of_aux' [] context t CicUniv.oblivion_ugraph)with
  | Cic.Sort _ -> `Type
  | Cic.MutInd (u,0,_) when is_mcu_type u -> `Optimize
  | ty -> 
     match
      fst (CicTypeChecker.type_of_aux' [] context ty CicUniv.oblivion_ugraph)
     with
     | Cic.Sort Cic.Prop -> `Proof
     | _ -> `Term
;;

let analyze_type context t =
 let rec aux =
  function
     Cic.Sort s -> `Sort s
   | Cic.MutInd (u,0,_) when is_mcu_type u -> `Optimize
   | Cic.Prod (_,_,t) -> aux t
   | _ -> `SomethingElse
 in
 match aux t with
    `Sort _ | `Optimize as res -> res
  | `SomethingElse ->
      match
       fst(CicTypeChecker.type_of_aux' [] context t CicUniv.oblivion_ugraph)
      with
          Cic.Sort Cic.Prop -> `Statement
       | _ -> `Type
;;

let ppid =
 let reserved =
  [ "to";
    "mod";
    "val";
    "in";
    "function"
  ]
 in
  function n ->
   let n = String.uncapitalize n in
    if List.mem n reserved then n ^ "_" else n
;;

let ppname =
 function
    Cic.Name s     -> ppid s
  | Cic.Anonymous  -> "_"
;;

(* get_nth l n   returns the nth element of the list l if it exists or *)
(* raises NotEnoughElements if l has less than n elements             *)
let rec get_nth l n =
 match (n,l) with
    (1, he::_) -> he
  | (n, he::tail) when n > 1 -> get_nth tail (n-1)
  | (_,_) -> raise NotEnoughElements
;;

let qualified_name_of_uri current_module_uri ?(capitalize=false) uri =
 let name =
  if capitalize then
   String.capitalize (UriManager.name_of_uri uri)
  else
   ppid (UriManager.name_of_uri uri) in
  let filename =
   let suri = UriManager.buri_of_uri uri in
   let s = String.sub suri 5 (String.length suri - 5) in
   let s = Pcre.replace ~pat:"/" ~templ:"_" s in
    String.uncapitalize s in
  if current_module_uri = UriManager.buri_of_uri uri then
   name
  else
   String.capitalize filename ^ "." ^ name
;;

let current_go_up = ref "(.!(";;
let at_level2 f x = 
  try 
    current_go_up := "(.~(";
    let rc = f x in 
    current_go_up := "(.!("; 
    rc
  with exn -> 
    current_go_up := "(.!("; 
    raise exn
;;

let pp current_module_uri ?metasenv ~in_type =
let rec pp ~in_type t context =
 let module C = Cic in
   match t with
      C.Rel n ->
       begin
        try
         (match get_nth context n with
             Some (C.Name s,_) -> ppid s
           | Some (C.Anonymous,_) -> "__" ^ string_of_int n
           | None -> "_hidden_" ^ string_of_int n
         )
        with
         NotEnoughElements -> string_of_int (List.length context - n)
       end
    | C.Var (uri,exp_named_subst) ->
        qualified_name_of_uri current_module_uri uri ^
         pp_exp_named_subst exp_named_subst context
    | C.Meta (n,l1) ->
       (match metasenv with
           None ->
            "?" ^ (string_of_int n) ^ "[" ^ 
             String.concat " ; "
              (List.rev_map
                (function
                    None -> "_"
                  | Some t -> pp ~in_type:false t context) l1) ^
             "]"
         | Some metasenv ->
            try
             let _,context,_ = CicUtil.lookup_meta n metasenv in
              "?" ^ (string_of_int n) ^ "[" ^ 
               String.concat " ; "
                (List.rev
                  (List.map2
                    (fun x y ->
                      match x,y with
                         _, None
                       | None, _ -> "_"
                       | Some _, Some t -> pp ~in_type:false t context
                    ) context l1)) ^
               "]"
            with
	      CicUtil.Meta_not_found _ 
            | Invalid_argument _ ->
              "???" ^ (string_of_int n) ^ "[" ^ 
               String.concat " ; "
                (List.rev_map (function None -> "_" | Some t ->
                  pp ~in_type:false t context) l1) ^
               "]"
       )
    | C.Sort s ->
       (match s with
           C.Prop  -> "Prop"
         | C.Set   -> "Set"
         | C.Type _ -> "Type"
         (*| C.Type u -> ("Type" ^ CicUniv.string_of_universe u)*)
	 | C.CProp _ -> "CProp" 
       )
    | C.Implicit (Some `Hole) -> "%"
    | C.Implicit _ -> "?"
    | C.Prod (b,s,t) ->
       (match b with
          C.Name n ->
           let n = "'" ^ String.uncapitalize n in
            "(" ^ pp ~in_type:true s context ^ " -> " ^
            pp ~in_type:true t ((Some (Cic.Name n,Cic.Decl s))::context) ^ ")"
        | C.Anonymous ->
           "(" ^ pp ~in_type:true s context ^ " -> " ^
           pp ~in_type:true t ((Some (b,Cic.Decl s))::context) ^ ")")
    | C.Cast (v,t) -> pp ~in_type v context
    | C.Lambda (b,s,t) ->
       (match analyze_type context s with
           `Sort _
         | `Statement -> pp ~in_type t ((Some (b,Cic.Decl s))::context)
         | `Optimize -> prerr_endline "XXX lambda";assert false
         | `Type ->
            "(function " ^ ppname b ^ " -> " ^
             pp ~in_type t ((Some (b,Cic.Decl s))::context) ^ ")")
    | C.LetIn (b,s,ty,t) ->
       (match analyze_term context s with
         | `Type
         | `Proof -> pp ~in_type t ((Some (b,Cic.Def (s,ty)))::context)
         | `Optimize 
         | `Term ->
            "(let " ^ ppname b ^ (*" : " ^ pp ~in_type:true ty context ^*)
            " = " ^ pp ~in_type:false s context ^ " in " ^
             pp ~in_type t ((Some (b,Cic.Def (s,ty)))::context) ^ ")")
    | C.Appl (he::tl) when in_type ->
       let hes = pp ~in_type he context in
       let stl = String.concat "," (clean_args_for_ty context tl) in
        (if stl = "" then "" else "(" ^ stl ^ ") ") ^ hes
    | C.Appl (C.MutInd _ as he::tl) ->
       let hes = pp ~in_type he context in
       let stl = String.concat "," (clean_args_for_ty context tl) in
        (if stl = "" then "" else "(" ^ stl ^ ") ") ^ hes
    | C.Appl (C.MutConstruct (uri,n,_,_) as he::tl) ->
       let nparams =
        match fst(CicEnvironment.get_obj CicUniv.oblivion_ugraph uri) with
           C.InductiveDefinition (_,_,nparams,_) -> nparams
         | _ -> assert false in
       let hes = pp ~in_type he context in
       let stl = String.concat "," (clean_args_for_constr nparams context tl) in
        "(" ^ hes ^ (if stl = "" then "" else "(" ^ stl ^ ")") ^ ")"
    | C.Appl li ->
       "(" ^ String.concat " " (clean_args context li) ^ ")"
    | C.Const (uri,exp_named_subst) ->
       qualified_name_of_uri current_module_uri uri ^
        pp_exp_named_subst exp_named_subst context
    | C.MutInd (uri,n,exp_named_subst) ->
       (try
         match fst(CicEnvironment.get_obj CicUniv.oblivion_ugraph uri) with
            C.InductiveDefinition (dl,_,_,_) ->
             let (name,_,_,_) = get_nth dl (n+1) in
              qualified_name_of_uri current_module_uri
               (UriManager.uri_of_string
                 (UriManager.buri_of_uri uri ^ "/" ^ name ^ ".con")) ^
              pp_exp_named_subst exp_named_subst context
          | _ -> raise CicExportationInternalError
        with
           Sys.Break as exn -> raise exn
         | _ -> UriManager.string_of_uri uri ^ "#1/" ^ string_of_int (n + 1)
       )
    | C.MutConstruct (uri,n1,n2,exp_named_subst) ->
       (try
         match fst(CicEnvironment.get_obj CicUniv.oblivion_ugraph uri) with
            C.InductiveDefinition (dl,_,_,_) ->
             let _,_,_,cons = get_nth dl (n1+1) in
              let id,_ = get_nth cons n2 in
               qualified_name_of_uri current_module_uri ~capitalize:true
                (UriManager.uri_of_string
                  (UriManager.buri_of_uri uri ^ "/" ^ id ^ ".con")) ^
               pp_exp_named_subst exp_named_subst context
          | _ -> raise CicExportationInternalError
        with
           Sys.Break as exn -> raise exn
         | _ ->
          UriManager.string_of_uri uri ^ "#1/" ^ string_of_int (n1 + 1) ^ "/" ^
           string_of_int n2
       )
    | C.MutCase (uri,n1,ty,te,patterns) ->
       if in_type then
        "unit (* TOO POLYMORPHIC TYPE *)"
       else (
       let rec needs_obj_magic ty =
        match CicReduction.whd context ty with
         | Cic.Lambda (_,_,(Cic.Lambda(_,_,_) as t)) -> needs_obj_magic t
         | Cic.Lambda (_,_,t) -> not (DoubleTypeInference.does_not_occur 1 t)
         | _ -> false (* it can be a Rel, e.g. in *_rec *)
       in
       let needs_obj_magic = needs_obj_magic ty in
       (match analyze_term context te with
           `Type -> assert false
         | `Proof ->
             (match patterns with
                 [] -> "assert false"   (* empty type elimination *)
               | [he] ->
                  pp ~in_type:false he context  (* singleton elimination *)
               | _ -> assert false)
         | `Optimize 
         | `Term ->
            if patterns = [] then "assert false"
            else
             (let connames_and_argsno, go_up, go_pu, go_down, go_nwod =
               (match fst(CicEnvironment.get_obj CicUniv.oblivion_ugraph uri) with
                   C.InductiveDefinition (dl,_,paramsno,_) ->
                    let (_,_,_,cons) = get_nth dl (n1+1) in
                    let rc = 
                     List.map
                      (fun (id,ty) ->
                        (* this is just an approximation since we do not have
                           reduction yet! *)
                        let rec count_prods toskip =
                         function
                            C.Prod (_,_,bo) when toskip > 0 ->
                             count_prods (toskip - 1) bo
                          | C.Prod (_,_,bo) -> 1 + count_prods 0 bo
                          | _ -> 0
                        in
                         qualified_name_of_uri current_module_uri
                          ~capitalize:true
                          (UriManager.uri_of_string
                            (UriManager.buri_of_uri uri ^ "/" ^ id ^ ".con")),
                         count_prods paramsno ty
                      ) cons
                    in
                    if not (is_mcu_type uri) then rc, "","","",""
                    else rc, !current_go_up, "))", "( .< (", " ) >.)"
                 | _ -> raise CicExportationInternalError
               )
              in
               let connames_and_argsno_and_patterns =
                let rec combine =
                   function
                      [],[] -> []
                    | (x,no)::tlx,y::tly -> (x,no,y)::(combine (tlx,tly))
                    | _,_ -> assert false
                in
                 combine (connames_and_argsno,patterns)
               in
                go_up ^
                "\n(match " ^ pp ~in_type:false te context ^ " with \n   " ^
                 (String.concat "\n | "
                  (List.map
                   (fun (x,argsno,y) ->
                     let rec aux argsno context =
                      function
                         Cic.Lambda (name,ty,bo) when argsno > 0 ->
                          let name =
                           match name with
                              Cic.Anonymous -> Cic.Anonymous
                            | Cic.Name n -> Cic.Name (ppid n) in
                          let args,res =
                           aux (argsno - 1) (Some (name,Cic.Decl ty)::context)
                            bo
                          in
                           (match analyze_type context ty with
                             | `Optimize -> prerr_endline "XXX contructor with l2 arg"; assert false
                             | `Statement
                             | `Sort _ -> args,res
                             | `Type ->
                                 (match name with
                                     C.Anonymous -> "_"
                                   | C.Name s -> s)::args,res)
                       | t when argsno = 0 -> [],pp ~in_type:false t context
                       | t ->
                          ["{" ^ string_of_int argsno ^ " args missing}"],
                           pp ~in_type:false t context
                     in
                      let pattern,body =
                       if argsno = 0 then x,pp ~in_type:false y context
                       else
                        let args,body = aux argsno context y in
                        let sargs = String.concat "," args in
                         x ^ (if sargs = "" then "" else "(" ^ sargs^ ")"),
                          body
                      in
                       pattern ^ " -> " ^ go_down ^
                        (if needs_obj_magic then
                         "Obj.magic (" ^ body ^ ")"
                        else
                         body) ^ go_nwod
                   ) connames_and_argsno_and_patterns)) ^
                 ")\n"^go_pu)))
    | C.Fix (no, funs) ->
       let names,_ =
        List.fold_left
         (fun (types,len) (n,_,ty,_) ->
            (Some (C.Name n,(C.Decl (CicSubstitution.lift len ty)))::types,
             len+1)
         ) ([],0) funs
       in
         "let rec " ^
         List.fold_right
          (fun (name,ind,ty,bo) i -> name ^ " = \n" ^
            pp ~in_type:false bo (names@context) ^ i)
          funs "" ^
         " in " ^
         (match get_nth names (no + 1) with
             Some (Cic.Name n,_) -> n
           | _ -> assert false)
    | C.CoFix (no,funs) ->
       let names,_ =
        List.fold_left
         (fun (types,len) (n,ty,_) ->
            (Some (C.Name n,(C.Decl (CicSubstitution.lift len ty)))::types,
             len+1)
         ) ([],0) funs
       in
         "\nCoFix " ^ " {" ^
         List.fold_right
          (fun (name,ty,bo) i -> "\n" ^ name ^ 
            " : " ^ pp ~in_type:true ty context ^ " := \n" ^
            pp ~in_type:false bo (names@context) ^ i)
          funs "" ^
         "}\n"
and pp_exp_named_subst exp_named_subst context =
 if exp_named_subst = [] then "" else
  "\\subst[" ^
   String.concat " ; " (
    List.map
     (function (uri,t) -> UriManager.name_of_uri uri ^ " \\Assign " ^ pp ~in_type:false t context)
     exp_named_subst
   ) ^ "]"
and clean_args_for_constr nparams context =
 let nparams = ref nparams in
 HExtlib.filter_map
  (function t ->
    decr nparams;
    match analyze_term context t with
       `Term when !nparams < 0 -> Some (pp ~in_type:false t context)
     | `Optimize 
     | `Term
     | `Type
     | `Proof -> None)
and clean_args context =
 function
 | [] | [_] -> assert false
 | he::arg1::tl as l ->
    let head_arg1, rest = 
       match analyze_term context arg1 with
      | `Optimize -> 
         !current_go_up :: pp ~in_type:false he context :: 
                 pp ~in_type:false arg1 context :: ["))"], tl
      | _ -> [], l
    in
    head_arg1 @ 
    HExtlib.filter_map
     (function t ->
       match analyze_term context t with
        | `Term -> Some (pp ~in_type:false t context)
        | `Optimize -> 
            prerr_endline "XXX function taking twice (or not as first) a l2 term"; assert false
        | `Type
        | `Proof -> None) rest
and clean_args_for_ty context =
 HExtlib.filter_map
  (function t ->
    match analyze_term context t with
       `Type -> Some (pp ~in_type:true t context)
     | `Optimize -> None
     | `Proof -> None
     | `Term -> None)
in
 pp ~in_type
;;

let ppty current_module_uri =
 (* nparams is the number of left arguments
    left arguments should either become parameters or be skipped altogether *)
 let rec args nparams context =
  function
     Cic.Prod (n,s,t) ->
      let n =
       match n with
          Cic.Anonymous -> Cic.Anonymous
        | Cic.Name n -> Cic.Name (String.uncapitalize n)
      in
       (match analyze_type context s with
         | `Optimize
         | `Statement
         | `Sort Cic.Prop ->
             args (nparams - 1) ((Some (n,Cic.Decl s))::context) t
         | `Type when nparams > 0 ->
             args (nparams - 1) ((Some (n,Cic.Decl s))::context) t
         | `Type ->
             let abstr,args =
              args (nparams - 1) ((Some (n,Cic.Decl s))::context) t in
               abstr,pp ~in_type:true current_module_uri s context::args
         | `Sort _ when nparams <= 0 ->
             let n = Cic.Name "unit (* EXISTENTIAL TYPE *)" in
              args (nparams - 1) ((Some (n,Cic.Decl s))::context) t
         | `Sort _ ->
             let n =
              match n with
                 Cic.Anonymous -> Cic.Anonymous
               | Cic.Name name -> Cic.Name ("'" ^ name) in
             let abstr,args =
              args (nparams - 1) ((Some (n,Cic.Decl s))::context) t
             in
              (match n with
                  Cic.Anonymous -> abstr
                | Cic.Name name -> name::abstr),
              args)
   | _ -> [],[]
 in
  args
;;

exception DoNotExtract;;

let pp_abstracted_ty current_module_uri =
 let rec args context =
  function
     Cic.Lambda (n,s,t) ->
      let n =
       match n with
          Cic.Anonymous -> Cic.Anonymous
        | Cic.Name n -> Cic.Name (String.uncapitalize n)
      in
       (match analyze_type context s with
         | `Optimize 
         | `Statement
         | `Type
         | `Sort Cic.Prop ->
             args ((Some (n,Cic.Decl s))::context) t
         | `Sort _ ->
             let n =
              match n with
                 Cic.Anonymous -> Cic.Anonymous
               | Cic.Name name -> Cic.Name ("'" ^ name) in
             let abstr,res =
              args ((Some (n,Cic.Decl s))::context) t
             in
              (match n with
                  Cic.Anonymous -> abstr
                | Cic.Name name -> name::abstr),
              res)
   | ty ->
     match analyze_type context ty with
      | `Optimize ->
           prerr_endline "XXX abstracted l2 ty"; assert false
      | `Sort _
      | `Statement -> raise DoNotExtract
      | `Type ->
          (* BUG HERE: this can be a real System F type *)
          let head = pp ~in_type:true current_module_uri ty context in
          [],head
 in
  args
;;


(* ppinductiveType (typename, inductive, arity, cons)                       *)
(* pretty-prints a single inductive definition                              *)
(* (typename, inductive, arity, cons)                                       *)
let ppinductiveType current_module_uri nparams (typename, inductive, arity, cons)
=
 match analyze_type [] arity with
    `Sort Cic.Prop -> ""
  | `Optimize 
  | `Statement
  | `Type -> assert false
  | `Sort _ ->
    if cons = [] then
     "type " ^ String.uncapitalize typename ^ " = unit (* empty type *)\n"
    else (
     let abstr,scons =
      List.fold_right
       (fun (id,ty) (_abstr,i) -> (* we should verify _abstr = abstr' *)
          let abstr',sargs = ppty current_module_uri nparams [] ty in
          let sargs = String.concat " * " sargs in
           abstr',
           String.capitalize id ^
            (if sargs = "" then "" else " of " ^ sargs) ^
            (if i = "" then "" else "\n | ") ^ i)
       cons ([],"")
      in
       let abstr =
        let s = String.concat "," abstr in
        if s = "" then "" else "(" ^ s ^ ") "
       in
       "type " ^ abstr ^ String.uncapitalize typename ^ " =\n" ^ scons ^ "\n")
;;

let ppobj current_module_uri obj =
 let module C = Cic in
 let module U = UriManager in
  let pp ~in_type = pp ~in_type current_module_uri in
  match obj with
    C.Constant (name, Some t1, t2, params, _) ->
      (match analyze_type [] t2 with
        | `Sort Cic.Prop
        | `Statement -> ""
        | `Optimize 
        | `Type -> 
            (match t1 with
            | Cic.Lambda (Cic.Name arg, s, t) ->
                            (match analyze_type [] s with
                | `Optimize -> 

                    "let " ^ ppid name ^ "__1 = function " ^ ppid arg 
                    ^ " -> .< " ^ 
                    at_level2 (pp ~in_type:false t) [Some (Cic.Name arg, Cic.Decl s)] 
                    ^ " >. ;;\n"
                    ^ "let " ^ ppid name ^ "__2 = ref ([] : (unit list*unit list) list);;\n"
                    ^ "let " ^ ppid name ^ " = function " ^ ppid arg
                    ^ " -> (try ignore (List.assoc "^ppid arg^" (Obj.magic  !"^ppid name
                    ^"__2)) with Not_found -> "^ppid name^"__2 := (Obj.magic ("
                    ^ ppid arg^",.! ("^ppid name^"__1 "^ppid arg^")))::!"
                    ^ppid name^"__2); .< List.assoc "^ppid arg^" (Obj.magic (!"
                    ^ppid name^"__2)) >.\n;;\n"
                    ^" let xxx = prerr_endline \""^ppid name^"\"; .!("^ppid
                    name^" Matita_freescale_opcode.HCS08)"
                | _ -> 
                   "let " ^ ppid name ^ " =\n" ^ pp ~in_type:false t1 [] ^ "\n")
            | _ -> "let " ^ ppid name ^ " =\n" ^ pp ~in_type:false t1 [] ^ "\n")
        | `Sort _ ->
            match analyze_type [] t1 with
               `Sort Cic.Prop -> ""
             | `Optimize -> prerr_endline "XXX aliasing l2 type"; assert false
             | _ ->
               (try
                 let abstr,res = pp_abstracted_ty current_module_uri [] t1 in
                 let abstr =
                  let s = String.concat "," abstr in
                  if s = "" then "" else "(" ^ s ^ ") "
                 in
                  "type " ^ abstr ^ ppid name ^ " = " ^ res ^ "\n"
                with
                 DoNotExtract -> ""))
   | C.Constant (name, None, ty, params, _) ->
      (match analyze_type [] ty with
          `Sort Cic.Prop
        | `Optimize -> prerr_endline "XXX axiom l2"; assert false
        | `Statement -> ""
        | `Sort _ -> "type " ^ ppid name ^ "\n"
        | `Type -> "let " ^ ppid name ^ " = assert false\n")
   | C.Variable (name, bo, ty, params, _) ->
      "Variable " ^ name ^
       "(" ^ String.concat ";" (List.map UriManager.string_of_uri params) ^
       ")" ^ ":\n" ^
       pp ~in_type:true ty [] ^ "\n" ^
       (match bo with None -> "" | Some bo -> ":= " ^ pp ~in_type:false bo [])
   | C.CurrentProof (name, conjectures, value, ty, params, _) ->
      "Current Proof of " ^ name ^
       "(" ^ String.concat ";" (List.map UriManager.string_of_uri params) ^
       ")" ^ ":\n" ^
      let separate s = if s = "" then "" else s ^ " ; " in
       List.fold_right
        (fun (n, context, t) i -> 
          let conjectures',name_context =
	         List.fold_right 
	          (fun context_entry (i,name_context) ->
	            (match context_entry with
	                Some (n,C.Decl at) ->
                         (separate i) ^
                           ppname n ^ ":" ^
                            pp ~in_type:true ~metasenv:conjectures
                            at name_context ^ " ",
                            context_entry::name_context
	              | Some (n,C.Def (at,aty)) ->
                         (separate i) ^
                           ppname n ^ ":" ^
                            pp ~in_type:true ~metasenv:conjectures
                            aty name_context ^
                           ":= " ^ pp ~in_type:false
                            ~metasenv:conjectures at name_context ^ " ",
                            context_entry::name_context
                      | None ->
                         (separate i) ^ "_ :? _ ", context_entry::name_context)
            ) context ("",[])
          in
           conjectures' ^ " |- " ^ "?" ^ (string_of_int n) ^ ": " ^
            pp ~in_type:true ~metasenv:conjectures t name_context ^ "\n" ^ i
        ) conjectures "" ^
        "\n" ^ pp ~in_type:false ~metasenv:conjectures value [] ^ " : " ^
          pp ~in_type:true ~metasenv:conjectures ty [] 
   | C.InductiveDefinition (l, params, nparams, _) ->
      List.fold_right
       (fun x i -> ppinductiveType current_module_uri nparams x ^ i) l ""
;;

let ppobj current_module_uri obj =
 let res = ppobj current_module_uri obj in
  if res = "" then "" else res ^ ";;\n\n"
;;
*)
*)
