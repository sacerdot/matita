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

(**************************************************************************)
(*                                                                        *)
(*                           PROJECT HELM                                 *)
(*                                                                        *)
(*                Andrea Asperti <asperti@cs.unibo.it>                    *)
(*                             16/6/2003                                   *)
(*                                                                        *)
(**************************************************************************)

(* $Id$ *)

let object_prefix = "obj:";;
let declaration_prefix = "decl:";;
let definition_prefix = "def:";;
let inductive_prefix = "ind:";;
let joint_prefix = "joint:";;
let proof_prefix = "proof:";;
let conclude_prefix = "concl:";;
let premise_prefix = "prem:";;
let lemma_prefix = "lemma:";;

let hide_coercions = ref true;;

(* e se mettessi la conversione di BY nell'apply_context ? *)
(* sarebbe carino avere l'invariante che la proof2pres
generasse sempre prove con contesto vuoto *)
 
let gen_id prefix seed =
 let res = prefix ^ string_of_int !seed in
  incr seed ;
  res
;;

let name_of = function
    Cic.Anonymous -> None
  | Cic.Name b -> Some b;;
 
exception Not_a_proof;;
exception NotImplemented;;
exception NotApplicable;;
   
(* we do not care for positivity, here, that in any case is enforced by
   well typing. Just a brutal search *)

let rec occur uri = 
  let module C = Cic in
  function
      C.Rel _ -> false
    | C.Var _ -> false
    | C.Meta _ -> false
    | C.Sort _ -> false
    | C.Implicit _ -> assert false
    | C.Prod (_,s,t) -> (occur uri s) or (occur uri t)
    | C.Cast (te,ty) -> (occur uri te)
    | C.Lambda (_,s,t) -> (occur uri s) or (occur uri t) (* or false ?? *)
    | C.LetIn (_,s,ty,t) -> (occur uri s) or (occur uri ty) or (occur uri t)
    | C.Appl l -> 
        List.fold_left 
          (fun b a -> 
             if b then b  
             else (occur uri a)) false l
    | C.Const (_,_) -> false
    | C.MutInd (uri1,_,_) -> if uri = uri1 then true else false
    | C.MutConstruct (_,_,_,_) -> false
    | C.MutCase _ -> false (* presuming too much?? *)
    | C.Fix _ -> false (* presuming too much?? *)
    | C.CoFix (_,_) -> false (* presuming too much?? *)
;;

let get_id = 
  let module C = Cic in
  function
      C.ARel (id,_,_,_) -> id
    | C.AVar (id,_,_) -> id
    | C.AMeta (id,_,_) -> id
    | C.ASort (id,_) -> id
    | C.AImplicit _ -> raise NotImplemented
    | C.AProd (id,_,_,_) -> id
    | C.ACast (id,_,_) -> id
    | C.ALambda (id,_,_,_) -> id
    | C.ALetIn (id,_,_,_,_) -> id
    | C.AAppl (id,_) -> id
    | C.AConst (id,_,_) -> id
    | C.AMutInd (id,_,_,_) -> id
    | C.AMutConstruct (id,_,_,_,_) -> id
    | C.AMutCase (id,_,_,_,_,_) -> id
    | C.AFix (id,_,_) -> id
    | C.ACoFix (id,_,_) -> id
;;

let test_for_lifting ~ids_to_inner_types ~ids_to_inner_sorts= 
  let module C = Cic in
  let module C2A = Cic2acic in
  (* atomic terms are never lifted, according to my policy *)
  function
      C.ARel (id,_,_,_) ->
         (try 
            ignore (Hashtbl.find ids_to_inner_types id).C2A.annsynthesized;
            true;
          with Not_found -> false) 
    | C.AVar (id,_,_) -> 
         (try 
            ignore (Hashtbl.find ids_to_inner_types id).C2A.annsynthesized;
            true;
          with Not_found -> false) 
    | C.AMeta (id,_,_) -> 
         (try 
            Hashtbl.find ids_to_inner_sorts id = `Prop
          with Not_found -> assert false)
    | C.ASort (id,_) -> false
    | C.AImplicit _ -> raise NotImplemented
    | C.AProd (id,_,_,_) -> false
    | C.ACast (id,_,_) -> 
         (try 
            ignore (Hashtbl.find ids_to_inner_types id).C2A.annsynthesized;
            true;
          with Not_found -> false)
    | C.ALambda (id,_,_,_) -> 
         (try 
            ignore (Hashtbl.find ids_to_inner_types id).C2A.annsynthesized;
            true;
          with Not_found -> false)
    | C.ALetIn (id,_,_,_,_) -> 
         (try 
            ignore (Hashtbl.find ids_to_inner_types id).C2A.annsynthesized;
            true;
          with Not_found -> false)
    | C.AAppl (id,_) ->
         (try 
            ignore (Hashtbl.find ids_to_inner_types id).C2A.annsynthesized;
            true;
          with Not_found -> false) 
    | C.AConst (id,_,_) -> 
         (try 
            ignore (Hashtbl.find ids_to_inner_types id).C2A.annsynthesized;
            true;
          with Not_found -> false) 
    | C.AMutInd (id,_,_,_) -> false
    | C.AMutConstruct (id,_,_,_,_) -> 
       (try 
            ignore (Hashtbl.find ids_to_inner_types id).C2A.annsynthesized;
            true;
          with Not_found -> false)
        (* oppure: false *)
    | C.AMutCase (id,_,_,_,_,_) ->
         (try 
            ignore (Hashtbl.find ids_to_inner_types id).C2A.annsynthesized;
            true;
          with Not_found -> false)
    | C.AFix (id,_,_) ->
          (try 
            ignore (Hashtbl.find ids_to_inner_types id).C2A.annsynthesized;
            true;
          with Not_found -> false)
    | C.ACoFix (id,_,_) ->
         (try 
            ignore (Hashtbl.find ids_to_inner_types id).C2A.annsynthesized;
            true;
          with Not_found -> false)
;;

(* transform a proof p into a proof list, concatenating the last 
conclude element to the apply_context list, in case context is
empty. Otherwise, it just returns [p] *)

let flat seed p = 
 let module K = Content in
  if (p.K.proof_context = []) then
    if p.K.proof_apply_context = [] then [p]
    else 
      let p1 =
        { p with
          K.proof_context = []; 
          K.proof_apply_context = []
        } in
      p.K.proof_apply_context@[p1]
  else 
    [p]
;;

let rec serialize seed = 
  function 
    [] -> []
  | a::l -> (flat seed a)@(serialize seed l) 
;;

(* top_down = true if the term is a LAMBDA or a decl *)
let generate_conversion seed top_down id inner_proof ~ids_to_inner_types =
 let module C2A = Cic2acic in
 let module K = Content in
 let exp = (try ((Hashtbl.find ids_to_inner_types id).C2A.annexpected)
            with Not_found -> None)
 in
 match exp with
     None -> inner_proof
   | Some expty ->
       if inner_proof.K.proof_conclude.K.conclude_method = "Intros+LetTac" then
         { K.proof_name = inner_proof.K.proof_name;
            K.proof_id   = gen_id proof_prefix seed;
            K.proof_context = [] ;
            K.proof_apply_context = [];
            K.proof_conclude = 
              { K.conclude_id = gen_id conclude_prefix seed; 
                K.conclude_aref = id;
                K.conclude_method = "TD_Conversion";
                K.conclude_args = 
                  [K.ArgProof {inner_proof with K.proof_name = None}];
                K.conclude_conclusion = Some expty
              };
          }
        else
          { K.proof_name =  inner_proof.K.proof_name;
            K.proof_id   = gen_id proof_prefix seed;
            K.proof_context = [] ;
            K.proof_apply_context = [{inner_proof with K.proof_name = None}];
            K.proof_conclude = 
              { K.conclude_id = gen_id conclude_prefix seed; 
                K.conclude_aref = id;
                K.conclude_method = "BU_Conversion";
                K.conclude_args =  
                 [K.Premise 
                  { K.premise_id = gen_id premise_prefix seed;
                    K.premise_xref = inner_proof.K.proof_id; 
                    K.premise_binder = None;
                    K.premise_n = None
                  } 
                 ]; 
                K.conclude_conclusion = Some expty
              };
          }
;;

let generate_exact seed t id name ~ids_to_inner_types =
  let module C2A = Cic2acic in
  let module K = Content in
    { K.proof_name = name;
      K.proof_id   = gen_id proof_prefix seed ;
      K.proof_context = [] ;
      K.proof_apply_context = [];
      K.proof_conclude = 
        { K.conclude_id = gen_id conclude_prefix seed; 
          K.conclude_aref = id;
          K.conclude_method = "Exact";
          K.conclude_args = [K.Term (false, t)];
          K.conclude_conclusion = 
              try Some (Hashtbl.find ids_to_inner_types id).C2A.annsynthesized
              with Not_found -> None
        };
    }
;;

let generate_intros_let_tac seed id n s ty inner_proof name ~ids_to_inner_types =
  let module C2A = Cic2acic in
  let module C = Cic in
  let module K = Content in
    { K.proof_name = name;
      K.proof_id  = gen_id proof_prefix seed ;
      K.proof_context = [] ;
      K.proof_apply_context = [];
      K.proof_conclude = 
        { K.conclude_id = gen_id conclude_prefix seed; 
          K.conclude_aref = id;
          K.conclude_method = "Intros+LetTac";
          K.conclude_args = [K.ArgProof inner_proof];
          K.conclude_conclusion = 
            try Some 
             (Hashtbl.find ids_to_inner_types id).C2A.annsynthesized
            with Not_found -> 
              (match inner_proof.K.proof_conclude.K.conclude_conclusion with
                 None -> None
              | Some t -> 
                 match ty with
                    None -> Some (C.AProd ("gen"^id,n,s,t))
                  | Some ty -> Some (C.ALetIn ("gen"^id,n,s,ty,t)))
        };
    }
;;

let build_decl_item seed id n s ~ids_to_inner_sorts =
 let module K = Content in
 let sort =
   try
    Some (Hashtbl.find ids_to_inner_sorts (Cic2acic.source_id_of_id id))
   with Not_found -> None
 in
 match sort with
 | Some `Prop ->
    `Hypothesis
      { K.dec_name = name_of n;
        K.dec_id = gen_id declaration_prefix seed; 
        K.dec_inductive = false;
        K.dec_aref = id;
        K.dec_type = s
      }
 | _ ->
    `Declaration
      { K.dec_name = name_of n;
        K.dec_id = gen_id declaration_prefix seed; 
        K.dec_inductive = false;
        K.dec_aref = id;
        K.dec_type = s
      }
;;

let infer_dependent ~headless context metasenv = function
  | [] -> assert false 
  | [t] -> [false, t]
  | he::tl as l ->
     if headless then
      List.map (function s -> false,s) l
     else
     try
       let hety,_ = 
         CicTypeChecker.type_of_aux'
           metasenv context (Deannotate.deannotate_term he)
           CicUniv.oblivion_ugraph
       in
       let fstorder t =
         match CicReduction.whd context t with
         | Cic.Prod _ -> false
         | _ -> true
       in
       let rec dummify_last_tgt t = 
         match CicReduction.whd context t with
         | Cic.Prod (n,s,tgt) -> Cic.Prod(n,s, dummify_last_tgt tgt)
         | _ -> Cic.Implicit None
       in
       let rec aux ty = function
         | [] -> []
         | t::tl -> 
              match 
               FreshNamesGenerator.clean_dummy_dependent_types 
                 (dummify_last_tgt ty) 
              with
              | Cic.Prod (n,src,tgt) ->
                  (n <> Cic.Anonymous && fstorder src, t) :: 
                  aux (CicSubstitution.subst 
                        (Deannotate.deannotate_term t) tgt) tl
              | _ -> List.map (fun s -> false,s) (t::tl)
       in
       (false, he) :: aux hety tl
     with CicTypeChecker.TypeCheckerFailure _ -> assert false
;;

let rec build_subproofs_and_args ?(headless=false) seed context metasenv l ~ids_to_inner_types ~ids_to_inner_sorts =
  let module C = Cic in
  let module K = Content in
  let rec aux n =
    function
      [] -> [],[]
    | (dep, t)::l1 -> 
       let need_lifting =
        test_for_lifting t ~ids_to_inner_types ~ids_to_inner_sorts in
       let subproofs,args = aux (n + if need_lifting then 1 else 0) l1 in
        if need_lifting then
          let new_subproof = 
            acic2content 
              seed context metasenv 
               ~name:("H" ^ string_of_int n) ~ids_to_inner_types
               ~ids_to_inner_sorts t in
          let new_arg = 
            K.Premise
              { K.premise_id = gen_id premise_prefix seed;
                K.premise_xref = new_subproof.K.proof_id;
                K.premise_binder = new_subproof.K.proof_name;
                K.premise_n = None
              } in
          new_subproof::subproofs,new_arg::args
        else 
          let hd = 
            (match t with 
               C.ARel (idr,idref,n,b) ->
                 let sort = 
                   (try
                     Hashtbl.find ids_to_inner_sorts idr 
                    with Not_found -> `Type (CicUniv.fresh())) in 
                 if sort = `Prop then 
                    K.Premise 
                      { K.premise_id = gen_id premise_prefix seed;
                        K.premise_xref = idr;
                        K.premise_binder = Some b;
                        K.premise_n = Some n
                      }
                 else (K.Term (dep,t))
             | C.AConst(id,uri,[]) ->
                 let sort = 
                   (try
                     Hashtbl.find ids_to_inner_sorts id 
                    with Not_found -> `Type (CicUniv.fresh())) in 
                 if sort = `Prop then 
                    K.Lemma 
                      { K.lemma_id = gen_id lemma_prefix seed;
                        K.lemma_name = UriManager.name_of_uri uri;
                        K.lemma_uri = UriManager.string_of_uri uri
                      }
                 else (K.Term (dep,t))
             | C.AMutConstruct(id,uri,tyno,consno,[]) ->
                 let sort = 
                   (try
                     Hashtbl.find ids_to_inner_sorts id 
                    with Not_found -> `Type (CicUniv.fresh())) in 
                 if sort = `Prop then 
                    let inductive_types =
                      (let o,_ = 
			 CicEnvironment.get_obj CicUniv.oblivion_ugraph uri
		       in
			 match o with 
			   | Cic.InductiveDefinition (l,_,_,_) -> l 
                           | _ -> assert false
                      ) in
                    let (_,_,_,constructors) = 
                      List.nth inductive_types tyno in 
                    let name,_ = List.nth constructors (consno - 1) in
                    K.Lemma 
                      { K.lemma_id = gen_id lemma_prefix seed;
                        K.lemma_name = name;
                        K.lemma_uri = 
                          UriManager.string_of_uri uri ^ "#xpointer(1/" ^
                          string_of_int (tyno+1) ^ "/" ^ string_of_int consno ^
                          ")"
                      }
                 else (K.Term (dep,t)) 
             | _ -> (K.Term (dep,t))) in
          subproofs,hd::args
  in 
  match (aux 1 (infer_dependent ~headless context metasenv l)) with
    [p],args -> 
      [{p with K.proof_name = None}], 
        List.map 
	  (function 
	      K.Premise prem when prem.K.premise_xref = p.K.proof_id ->
               K.Premise {prem with K.premise_binder = None}
            | i -> i) args
  | p,a as c -> c

and

build_def_item seed context metasenv id n t ty ~ids_to_inner_sorts ~ids_to_inner_types =
 let module K = Content in
  try
   let sort = Hashtbl.find ids_to_inner_sorts id in
   if sort = `Prop then
       (let p = 
        (acic2content seed context metasenv ?name:(name_of n) ~ids_to_inner_sorts  ~ids_to_inner_types t)
       in 
        `Proof p;)
   else 
      `Definition
        { K.def_name = name_of n;
          K.def_id = gen_id definition_prefix seed; 
          K.def_aref = id;
          K.def_term = t;
          K.def_type = ty
        }
  with
   Not_found -> assert false

(* the following function must be called with an object of sort
Prop. For debugging purposes this is tested again, possibly raising an 
Not_a_proof exception *)

and acic2content seed context metasenv ?name ~ids_to_inner_sorts ~ids_to_inner_types t =
  let rec aux ?name context t =
  let module C = Cic in
  let module K = Content in
  let module C2A = Cic2acic in
  let t1 =
    match t with 
      C.ARel (id,idref,n,b) as t ->
        let sort = Hashtbl.find ids_to_inner_sorts id in
        if sort = `Prop then
          generate_exact seed t id name ~ids_to_inner_types 
        else raise Not_a_proof
    | C.AVar (id,uri,exp_named_subst) as t ->
        let sort = Hashtbl.find ids_to_inner_sorts id in
        if sort = `Prop then
          generate_exact seed t id name ~ids_to_inner_types 
        else raise Not_a_proof
    | C.AMeta (id,n,l) as t ->
        let sort = Hashtbl.find ids_to_inner_sorts id in
        if sort = `Prop then
          generate_exact seed t id name ~ids_to_inner_types 
        else raise Not_a_proof
    | C.ASort (id,s) -> raise Not_a_proof
    | C.AImplicit _ -> raise NotImplemented
    | C.AProd (_,_,_,_) -> raise Not_a_proof
    | C.ACast (id,v,t) -> aux context v
    | C.ALambda (id,n,s,t) -> 
        let sort = Hashtbl.find ids_to_inner_sorts id in
        if sort = `Prop then 
          let proof = 
            aux ((Some (n,Cic.Decl (Deannotate.deannotate_term s)))::context) t 
          in
          let proof' = 
            if proof.K.proof_conclude.K.conclude_method = "Intros+LetTac" then
               match proof.K.proof_conclude.K.conclude_args with
                 [K.ArgProof p] -> p
               | _ -> assert false                  
            else proof in
          let proof'' =
            { proof' with
              K.proof_name = None;
              K.proof_context = 
                (build_decl_item seed id n s ids_to_inner_sorts)::
                  proof'.K.proof_context
            }
          in
          generate_intros_let_tac seed id n s None proof'' name ~ids_to_inner_types
        else 
          raise Not_a_proof 
    | C.ALetIn (id,n,s,ty,t) ->
        let sort = Hashtbl.find ids_to_inner_sorts id in
        if sort = `Prop then
          let proof =
            aux
             ((Some (n,
              Cic.Def (Deannotate.deannotate_term s,Deannotate.deannotate_term ty)))::context) t 
          in
          let proof' = 
            if proof.K.proof_conclude.K.conclude_method = "Intros+LetTac" then
               match proof.K.proof_conclude.K.conclude_args with
                 [K.ArgProof p] -> p
               | _ -> assert false                  
            else proof in
          let proof'' =
            { proof' with
               K.proof_name = None;
               K.proof_context = 
                 ((build_def_item seed context metasenv (get_id s) n s ty ids_to_inner_sorts
                   ids_to_inner_types):> Cic.annterm K.in_proof_context_element)
                 ::proof'.K.proof_context;
            }
          in
          generate_intros_let_tac seed id n s (Some ty) proof'' name ~ids_to_inner_types
        else 
          raise Not_a_proof
    | C.AAppl (id,li) ->
        (try coercion 
           seed context metasenv id li ~ids_to_inner_types ~ids_to_inner_sorts
         with NotApplicable ->
         try rewrite 
           seed context metasenv name id li ~ids_to_inner_types ~ids_to_inner_sorts
         with NotApplicable ->
         try inductive 
          seed context metasenv name id li ~ids_to_inner_types ~ids_to_inner_sorts
         with NotApplicable ->
         try transitivity 
           seed context metasenv name id li ~ids_to_inner_types ~ids_to_inner_sorts
         with NotApplicable ->
          let subproofs, args =
            build_subproofs_and_args 
              seed context metasenv li ~ids_to_inner_types ~ids_to_inner_sorts in
(*            
          let args_to_lift = 
            List.filter (test_for_lifting ~ids_to_inner_types) li in
          let subproofs = 
            match args_to_lift with
                [_] -> List.map aux args_to_lift 
            | _ -> List.map (aux ~name:"H") args_to_lift in
          let args = build_args seed li subproofs 
                 ~ids_to_inner_types ~ids_to_inner_sorts in *)
            { K.proof_name = name;
              K.proof_id   = gen_id proof_prefix seed;
              K.proof_context = [];
              K.proof_apply_context = serialize seed subproofs;
              K.proof_conclude = 
                { K.conclude_id = gen_id conclude_prefix seed;
                  K.conclude_aref = id;
                  K.conclude_method = "Apply";
                  K.conclude_args = args;
                  K.conclude_conclusion = 
                     try Some 
                       (Hashtbl.find ids_to_inner_types id).C2A.annsynthesized
                     with Not_found -> None
                 };
            })
    | C.AConst (id,uri,exp_named_subst) as t ->
        let sort = Hashtbl.find ids_to_inner_sorts id in
        if sort = `Prop then
          generate_exact seed t id name ~ids_to_inner_types
        else raise Not_a_proof
    | C.AMutInd (id,uri,i,exp_named_subst) -> raise Not_a_proof
    | C.AMutConstruct (id,uri,i,j,exp_named_subst) as t ->
        let sort = Hashtbl.find ids_to_inner_sorts id in
        if sort = `Prop then 
          generate_exact seed t id name ~ids_to_inner_types
        else raise Not_a_proof
    | C.AMutCase (id,uri,typeno,ty,te,patterns) ->
        let inductive_types,noparams =
          (let o, _ = CicEnvironment.get_obj CicUniv.oblivion_ugraph uri in
	     match o with
		 Cic.Constant _ -> assert false
               | Cic.Variable _ -> assert false
               | Cic.CurrentProof _ -> assert false
               | Cic.InductiveDefinition (l,_,n,_) -> l,n 
          ) in
        let (_,_,_,constructors) = List.nth inductive_types typeno in
        let name_and_arities = 
          let rec count_prods =
            function 
               C.Prod (_,_,t) -> 1 + count_prods t
             | _ -> 0 in
          List.map 
            (function (n,t) -> Some n,((count_prods t) - noparams)) constructors in
        let pp = 
          let build_proof p (name,arity) =
            let rec make_context_and_body c p n =
              if n = 0 then c,(aux context p)
              else 
                (match p with
                   Cic.ALambda(idl,vname,s1,t1) ->
                     let ce = 
                       build_decl_item 
                         seed idl vname s1 ~ids_to_inner_sorts in
                     make_context_and_body (ce::c) t1 (n-1)
                   | _ -> assert false) in
             let context,body = make_context_and_body [] p arity in
               K.ArgProof
                {body with K.proof_name = name; K.proof_context=context} in
          List.map2 build_proof patterns name_and_arities in
        let context,term =
          (match 
             build_subproofs_and_args ~headless:true
               seed context metasenv ~ids_to_inner_types ~ids_to_inner_sorts [te]
           with
             l,[t] -> l,t
           | _ -> assert false) in
        { K.proof_name = name;
          K.proof_id   = gen_id proof_prefix seed;
          K.proof_context = []; 
          K.proof_apply_context = serialize seed context;
          K.proof_conclude = 
            { K.conclude_id = gen_id conclude_prefix seed; 
              K.conclude_aref = id;
              K.conclude_method = "Case";
              K.conclude_args = 
                (K.Aux (UriManager.string_of_uri uri))::
                (K.Aux (string_of_int typeno))::(K.Term (false,ty))::term::pp;
              K.conclude_conclusion = 
                try Some 
                  (Hashtbl.find ids_to_inner_types id).C2A.annsynthesized
                with Not_found -> None  
             }
        }
    | C.AFix (id, no, funs) -> 
        let context' = 
          List.fold_left
            (fun ctx (_,n,_,ty,_) -> 
              let ty = Deannotate.deannotate_term ty in
              Some (Cic.Name n,Cic.Decl ty) :: ctx)
            [] funs @ context
        in
        let proofs = 
          List.map 
            (function (_,name,_,_,bo) -> `Proof (aux context' ~name bo)) funs in
        let fun_name = 
          List.nth (List.map (fun (_,name,_,_,_) -> name) funs) no 
        in
        let decreasing_args = 
          List.map (function (_,_,n,_,_) -> n) funs in
        let jo = 
          { K.joint_id = gen_id joint_prefix seed;
            K.joint_kind = `Recursive decreasing_args;
            K.joint_defs = proofs
          } 
        in
          { K.proof_name = name;
            K.proof_id  = gen_id proof_prefix seed;
            K.proof_context = [`Joint jo]; 
            K.proof_apply_context = [];
            K.proof_conclude = 
              { K.conclude_id = gen_id conclude_prefix seed; 
                K.conclude_aref = id;
                K.conclude_method = "Exact";
                K.conclude_args =
                [ K.Premise
                  { K.premise_id = gen_id premise_prefix seed; 
                    K.premise_xref = jo.K.joint_id;
                    K.premise_binder = Some fun_name;
                    K.premise_n = Some no;
                  }
                ];
                K.conclude_conclusion =
                   try Some 
                     (Hashtbl.find ids_to_inner_types id).C2A.annsynthesized
                   with Not_found -> None
              }
        } 
    | C.ACoFix (id,no,funs) -> 
        let context' = 
          List.fold_left
            (fun ctx (_,n,ty,_) -> 
              let ty = Deannotate.deannotate_term ty in
              Some (Cic.Name n,Cic.Decl ty) :: ctx)
            [] funs @ context
        in
        let proofs = 
          List.map 
            (function (_,name,_,bo) -> `Proof (aux context' ~name bo)) funs in
        let jo = 
          { K.joint_id = gen_id joint_prefix seed;
            K.joint_kind = `CoRecursive;
            K.joint_defs = proofs
          } 
        in
          { K.proof_name = name;
            K.proof_id   = gen_id proof_prefix seed;
            K.proof_context = [`Joint jo]; 
            K.proof_apply_context = [];
            K.proof_conclude = 
              { K.conclude_id = gen_id conclude_prefix seed; 
                K.conclude_aref = id;
                K.conclude_method = "Exact";
                K.conclude_args =
                [ K.Premise
                  { K.premise_id = gen_id premise_prefix seed; 
                    K.premise_xref = jo.K.joint_id;
                    K.premise_binder = Some "tiralo fuori";
                    K.premise_n = Some no;
                  }
                ];
                K.conclude_conclusion =
                  try Some 
                    (Hashtbl.find ids_to_inner_types id).C2A.annsynthesized
                  with Not_found -> None
              };
        } 
     in 
     let id = get_id t in
     generate_conversion seed false id t1 ~ids_to_inner_types
in aux ?name context t

and inductive seed context metasenv name id li ~ids_to_inner_types ~ids_to_inner_sorts =
  let aux context ?name = 
    acic2content seed context metasenv ~ids_to_inner_types ~ids_to_inner_sorts 
  in
  let module C2A = Cic2acic in
  let module K = Content in
  let module C = Cic in
  match li with 
    C.AConst (idc,uri,exp_named_subst)::args ->
      let uri_str = UriManager.string_of_uri uri in
      let suffix = Str.regexp_string "_ind.con" in
      let len = String.length uri_str in 
      let n = (try (Str.search_backward suffix uri_str len)
               with Not_found -> -1) in
      if n<0 then raise NotApplicable
      else 
        let method_name =
          if UriManager.eq uri HelmLibraryObjects.Logic.ex_ind_URI then "Exists"
          else if UriManager.eq uri HelmLibraryObjects.Logic.and_ind_URI then "AndInd"
          else if UriManager.eq uri HelmLibraryObjects.Logic.false_ind_URI then "FalseInd"
          else "ByInduction" in
        let prefix = String.sub uri_str 0 n in
        let ind_str = (prefix ^ ".ind") in 
        let ind_uri = UriManager.uri_of_string ind_str in
        let inductive_types,noparams =
          (let o,_ = CicEnvironment.get_obj CicUniv.oblivion_ugraph ind_uri in
	     match o with
               | Cic.InductiveDefinition (l,_,n,_) -> (l,n) 
               | _ -> assert false
          ) in
        let rec split n l =
          if n = 0 then ([],l) else
          let p,a = split (n-1) (List.tl l) in
          ((List.hd l::p),a) in
        let params_and_IP,tail_args = split (noparams+1) args in
        let constructors = 
            (match inductive_types with
              [(_,_,_,l)] -> l
            | _ -> raise NotApplicable) (* don't care for mutual ind *) in
        let constructors1 = 
          let rec clean_up n t =
             if n = 0 then t else
             (match t with
                (label,Cic.Prod (_,_,t)) -> clean_up (n-1) (label,t)
              | _ -> assert false) in
          List.map (clean_up noparams) constructors in
        let no_constructors= List.length constructors in
        let args_for_cases, other_args = 
          split no_constructors tail_args in
        let subproofs,other_method_args =
          build_subproofs_and_args ~headless:true seed context metasenv
           other_args ~ids_to_inner_types ~ids_to_inner_sorts in
        let method_args=
          let rec build_method_args =
            function
                [],_-> [] (* extra args are ignored ???? *)
              | (name,ty)::tlc,arg::tla ->
                  let idarg = get_id arg in
                  let sortarg = 
                    (try (Hashtbl.find ids_to_inner_sorts idarg)
                     with Not_found -> `Type (CicUniv.fresh())) in
                  let hdarg = 
                    if sortarg = `Prop then
                      let (co,bo) = 
                        let rec bc context = 
                          function 
                            Cic.Prod (_,s,t),Cic.ALambda(idl,n,s1,t1) ->
                              let context' = 
                                Some (n,Cic.Decl(Deannotate.deannotate_term s1))
                                  ::context
                              in
                              let ce = 
                                build_decl_item 
                                  seed idl n s1 ~ids_to_inner_sorts in
                              if (occur ind_uri s) then
                                ( match t1 with
                                   Cic.ALambda(id2,n2,s2,t2) ->
                                     let context'' = 
                                       Some
                                         (n2,Cic.Decl
                                           (Deannotate.deannotate_term s2))
                                       ::context'
                                     in
                                     let inductive_hyp =
                                       `Hypothesis
                                         { K.dec_name = name_of n2;
                                           K.dec_id =
                                            gen_id declaration_prefix seed; 
                                           K.dec_inductive = true;
                                           K.dec_aref = id2;
                                           K.dec_type = s2
                                         } in
                                     let (context,body) = bc context'' (t,t2) in
                                     (ce::inductive_hyp::context,body)
                                 | _ -> assert false)
                              else 
                                ( 
                                let (context,body) = bc context' (t,t1) in
                                (ce::context,body))
                            | _ , t -> ([],aux context t) in
                        bc context (ty,arg) in
                      K.ArgProof
                       { bo with
                         K.proof_name = Some name;
                         K.proof_context = co; 
                       };
                    else (K.Term (false,arg)) in
                  hdarg::(build_method_args (tlc,tla))
              | _ -> assert false in
          build_method_args (constructors1,args_for_cases) in
          { K.proof_name = name;
            K.proof_id   = gen_id proof_prefix seed;
            K.proof_context = []; 
            K.proof_apply_context = serialize seed subproofs;
            K.proof_conclude = 
              { K.conclude_id = gen_id conclude_prefix seed; 
                K.conclude_aref = id;
                K.conclude_method = method_name;
                K.conclude_args =
                  K.Aux (string_of_int no_constructors) 
                  ::K.Term (false,(C.AAppl(id,((C.AConst(idc,uri,exp_named_subst))::params_and_IP))))
                  ::method_args@other_method_args;
                K.conclude_conclusion = 
                   try Some 
                     (Hashtbl.find ids_to_inner_types id).C2A.annsynthesized
                   with Not_found -> None  
              }
          } 
  | _ -> raise NotApplicable

and coercion seed context metasenv id li ~ids_to_inner_types ~ids_to_inner_sorts =
  match li with
    | ((Cic.AConst _) as he)::tl
    | ((Cic.AMutInd _) as he)::tl
    | ((Cic.AMutConstruct _) as he)::tl when 
       (match CoercDb.is_a_coercion (Deannotate.deannotate_term he) with
       | None -> false | Some (_,_,_,_,cpos) -> cpos < List.length tl)
       && !hide_coercions ->
        let cpos,sats =
          match CoercDb.is_a_coercion (Deannotate.deannotate_term he) with
          | None -> assert false
          | Some (_,_,_,sats,cpos) -> cpos, sats
        in
        let x = List.nth tl cpos in
        let _,rest = 
          try HExtlib.split_nth (cpos + sats +1) tl with Failure _ -> [],[] 
        in
        if rest = [] then
         acic2content 
          seed context metasenv ~ids_to_inner_types ~ids_to_inner_sorts 
           x
        else
         acic2content 
          seed context metasenv ~ids_to_inner_types ~ids_to_inner_sorts 
           (Cic.AAppl (id,x::rest))
    | _ -> raise NotApplicable

and rewrite seed context metasenv name id li ~ids_to_inner_types ~ids_to_inner_sorts =
  let aux context ?name = 
    acic2content seed context metasenv ~ids_to_inner_types ~ids_to_inner_sorts
  in
  let module C2A = Cic2acic in
  let module K = Content in
  let module C = Cic in
  match li with 
    C.AConst (sid,uri,exp_named_subst)::args ->
      if UriManager.eq uri HelmLibraryObjects.Logic.eq_ind_URI or
         UriManager.eq uri HelmLibraryObjects.Logic.eq_ind_r_URI or
         LibraryObjects.is_eq_ind_URI uri or
         LibraryObjects.is_eq_ind_r_URI uri then 
        let subproofs,arg = 
          (match 
             build_subproofs_and_args 
               seed context metasenv 
                 ~ids_to_inner_types ~ids_to_inner_sorts [List.nth args 3]
           with 
             l,[p] -> l,p
           | _,_ -> assert false) in 
        let method_args =
          let rec ma_aux n = function
              [] -> []
            | a::tl -> 
                let hd = 
                  if n = 0 then arg
                  else 
                    let aid = get_id a in
                    let asort = (try (Hashtbl.find ids_to_inner_sorts aid)
                      with Not_found -> `Type (CicUniv.fresh())) in
                    if asort = `Prop then
                      K.ArgProof (aux context a)
                    else K.Term (false,a) in
                hd::(ma_aux (n-1) tl) in
          (ma_aux 3 args) in 
          { K.proof_name = name;
            K.proof_id  = gen_id proof_prefix seed;
            K.proof_context = []; 
            K.proof_apply_context = serialize seed subproofs;
            K.proof_conclude = 
              { K.conclude_id = gen_id conclude_prefix seed; 
                K.conclude_aref = id;
                K.conclude_method =
                 if UriManager.eq uri HelmLibraryObjects.Logic.eq_ind_URI
                 || LibraryObjects.is_eq_ind_URI uri then
                  "RewriteLR"
                 else
                  "RewriteRL";
                K.conclude_args = 
                  K.Term (false,(C.AConst (sid,uri,exp_named_subst)))::method_args;
                K.conclude_conclusion = 
                   try Some 
                     (Hashtbl.find ids_to_inner_types id).C2A.annsynthesized
                   with Not_found -> None
              }
          } 
      else raise NotApplicable
  | _ -> raise NotApplicable

and transitivity 
  seed context metasenv name id li ~ids_to_inner_types ~ids_to_inner_sorts 
=
  let module C2A = Cic2acic in
  let module K = Content in
  let module C = Cic in
  match li with 
    | C.AConst (sid,uri,exp_named_subst)::args 
	when LibraryObjects.is_trans_eq_URI uri ->
	let exp_args = List.map snd exp_named_subst in
	let t1,t2,t3,p1,p2 =
	  match exp_args@args with
	    | [_;t1;t2;t3;p1;p2] -> t1,t2,t3,p1,p2
	    | _ -> raise NotApplicable
	in
	  { K.proof_name = name;
            K.proof_id  = gen_id proof_prefix seed;
            K.proof_context = []; 
            K.proof_apply_context = [];
            K.proof_conclude = 
              { K.conclude_id = gen_id conclude_prefix seed; 
                K.conclude_aref = id;
                K.conclude_method = "Eq_chain";
                K.conclude_args = 
                   K.Term (false,t1)::
		     (transitivity_aux 
			seed context metasenv ~ids_to_inner_types ~ids_to_inner_sorts p1)
                     @ [K.Term (false,t2)]@
		     (transitivity_aux 
			seed context metasenv ~ids_to_inner_types ~ids_to_inner_sorts p2)
                     @ [K.Term (false,t3)];
                K.conclude_conclusion = 
                   try Some 
                     (Hashtbl.find ids_to_inner_types id).C2A.annsynthesized
                   with Not_found -> None
              }
          } 
    | _ -> raise NotApplicable

and transitivity_aux seed context metasenv ~ids_to_inner_types ~ids_to_inner_sorts t =
  let module C2A = Cic2acic in
  let module K = Content in
  let module C = Cic in
  match t with 
    | C.AAppl (_,C.AConst (sid,uri,exp_named_subst)::args) 
	when LibraryObjects.is_trans_eq_URI uri ->
	let exp_args = List.map snd exp_named_subst in
	let t1,t2,t3,p1,p2 =
	  match exp_args@args with
	    | [_;t1;t2;t3;p1;p2] -> t1,t2,t3,p1,p2
	    | _ -> raise NotApplicable
	in
          (transitivity_aux 
            seed context metasenv ~ids_to_inner_types ~ids_to_inner_sorts p1)
	  @[K.Term (false,t2)]
	  @(transitivity_aux 
            seed context metasenv ~ids_to_inner_types ~ids_to_inner_sorts p2)
    | _ -> [K.ArgProof 
	(acic2content seed context metasenv ~ids_to_inner_sorts ~ids_to_inner_types t)]

;; 


let map_conjectures
 seed ~ids_to_inner_sorts ~ids_to_inner_types (id,n,context,ty)
=
 let module K = Content in
 let context' =
  List.map
   (function
       (id,None) -> None
     | (id,Some (name,Cic.ADecl t)) ->
         Some
          (* We should call build_decl_item, but we have not computed *)
          (* the inner-types ==> we always produce a declaration      *)
          (`Declaration
            { K.dec_name = name_of name;
              K.dec_id = gen_id declaration_prefix seed; 
              K.dec_inductive = false;
              K.dec_aref = get_id t;
              K.dec_type = t
            })
     | (id,Some (name,Cic.ADef (t,ty))) ->
         Some
          (* We should call build_def_item, but we have not computed *)
          (* the inner-types ==> we always produce a declaration     *)
          (`Definition
             { K.def_name = name_of name;
               K.def_id = gen_id definition_prefix seed; 
               K.def_aref = get_id t;
               K.def_term = t;
               K.def_type = ty
             })
   ) context
 in
  (id,n,context',ty)
;;

(* map_sequent is similar to map_conjectures, but the for the hid
of the hypothesis, which are preserved instead of generating
fresh ones. We shall have to adopt a uniform policy, soon or later *)

let map_sequent ((id,n,context,ty):Cic.annconjecture) =
 let module K = Content in
 let context' =
  List.map
   (function
       (id,None) -> None
     | (id,Some (name,Cic.ADecl t)) ->
         Some
          (* We should call build_decl_item, but we have not computed *)
          (* the inner-types ==> we always produce a declaration      *)
          (`Declaration
            { K.dec_name = name_of name;
              K.dec_id = id; 
              K.dec_inductive = false;
              K.dec_aref = get_id t;
              K.dec_type = t
            })
     | (id,Some (name,Cic.ADef (t,ty))) ->
         Some
          (* We should call build_def_item, but we have not computed *)
          (* the inner-types ==> we always produce a declaration     *)
          (`Definition
             { K.def_name = name_of name;
               K.def_id = id; 
               K.def_aref = get_id t;
               K.def_term = t;
               K.def_type = ty
             })
   ) context
 in
  (id,n,context',ty)
;;

let rec annobj2content ~ids_to_inner_sorts ~ids_to_inner_types = 
  let module C = Cic in
  let module K = Content in
  let module C2A = Cic2acic in
  let seed = ref 0 in
  function
      C.ACurrentProof (_,_,n,conjectures,bo,ty,params,_) ->
        (gen_id object_prefix seed, params,
          Some
           (List.map
             (map_conjectures seed ~ids_to_inner_sorts ~ids_to_inner_types)
             conjectures),
          `Def (K.Const,ty,
           build_def_item 
             seed [] (Deannotate.deannotate_conjectures conjectures) 
             (get_id bo) (C.Name n) bo ty
             ~ids_to_inner_sorts ~ids_to_inner_types))
    | C.AConstant (_,_,n,Some bo,ty,params,_) ->
         (gen_id object_prefix seed, params, None,
           `Def (K.Const,ty,
           build_def_item seed [] [] (get_id bo) (C.Name n) bo ty
               ~ids_to_inner_sorts ~ids_to_inner_types))
    | C.AConstant (id,_,n,None,ty,params,_) ->
         (gen_id object_prefix seed, params, None,
           `Decl (K.Const,
             build_decl_item seed id (C.Name n) ty 
               ~ids_to_inner_sorts))
    | C.AVariable (_,n,Some bo,ty,params,_) ->
         (gen_id object_prefix seed, params, None,
           `Def (K.Var,ty,
           build_def_item seed [] [] (get_id bo) (C.Name n) bo ty
               ~ids_to_inner_sorts ~ids_to_inner_types))
    | C.AVariable (id,n,None,ty,params,_) ->
         (gen_id object_prefix seed, params, None,
           `Decl (K.Var,
             build_decl_item seed id (C.Name n) ty
              ~ids_to_inner_sorts))
    | C.AInductiveDefinition (id,l,params,nparams,_) ->
         (gen_id object_prefix seed, params, None,
            `Joint
              { K.joint_id = gen_id joint_prefix seed;
                K.joint_kind = `Inductive nparams;
                K.joint_defs = List.map (build_inductive seed) l
              }) 

and
    build_inductive seed = 
     let module K = Content in
      fun (_,n,b,ty,l) ->
        `Inductive
          { K.inductive_id = gen_id inductive_prefix seed;
            K.inductive_name = n;
            K.inductive_kind = b;
            K.inductive_type = ty;
            K.inductive_constructors = build_constructors seed l
           }

and 
    build_constructors seed l =
     let module K = Content in
      List.map 
       (fun (n,t) ->
           { K.dec_name = Some n;
             K.dec_id = gen_id declaration_prefix seed;
             K.dec_inductive = false;
             K.dec_aref = "";
             K.dec_type = t
           }) l
;;
   
(* 
and 'term cinductiveType = 
 id * string * bool * 'term *                (* typename, inductive, arity *)
   'term cconstructor list                   (*  constructors        *)

and 'term cconstructor =
 string * 'term    
*)


