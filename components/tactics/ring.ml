(* Copyright (C) 2002, HELM Team.
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

open CicReduction
open PrimitiveTactics
open ProofEngineTypes
open UriManager

(** DEBUGGING *)

  (** perform debugging output? *)
let debug = false
let debug_print = fun _ -> ()

  (** debugging print *)
let warn s = debug_print (lazy ("RING WARNING: " ^ (Lazy.force s)))

(** CIC URIS *)

(**
  Note: For constructors URIs aren't really URIs but rather triples of
  the form (uri, typeno, consno).  This discrepancy is to preserver an
  uniformity of invocation of "mkXXX" functions.
*)

let equality_is_a_congruence_A =
 uri_of_string "cic:/Coq/Init/Logic/Logic_lemmas/equality/A.var"
let equality_is_a_congruence_x =
 uri_of_string "cic:/Coq/Init/Logic/Logic_lemmas/equality/x.var"
let equality_is_a_congruence_y =
 uri_of_string "cic:/Coq/Init/Logic/Logic_lemmas/equality/y.var"

let apolynomial_uri =
  uri_of_string "cic:/Coq/ring/Ring_abstract/apolynomial.ind"
let apvar_uri = (apolynomial_uri, 0, 1)
let ap0_uri = (apolynomial_uri, 0, 2)
let ap1_uri = (apolynomial_uri, 0, 3)
let applus_uri = (apolynomial_uri, 0, 4)
let apmult_uri = (apolynomial_uri, 0, 5)
let apopp_uri = (apolynomial_uri, 0, 6)

let quote_varmap_A_uri = uri_of_string "cic:/Coq/ring/Quote/variables_map/A.var"
let varmap_uri = uri_of_string "cic:/Coq/ring/Quote/varmap.ind"
let empty_vm_uri = (varmap_uri, 0, 1)
let node_vm_uri = (varmap_uri, 0, 2)
let varmap_find_uri = uri_of_string "cic:/Coq/ring/Quote/varmap_find.con"
let index_uri = uri_of_string "cic:/Coq/ring/Quote/index.ind"
let left_idx_uri = (index_uri, 0, 1)
let right_idx_uri = (index_uri, 0, 2)
let end_idx_uri = (index_uri, 0, 3)

let abstract_rings_A_uri =
 uri_of_string "cic:/Coq/ring/Ring_abstract/abstract_rings/A.var"
let abstract_rings_Aplus_uri =
 uri_of_string "cic:/Coq/ring/Ring_abstract/abstract_rings/Aplus.var"
let abstract_rings_Amult_uri =
 uri_of_string "cic:/Coq/ring/Ring_abstract/abstract_rings/Amult.var"
let abstract_rings_Aone_uri =
 uri_of_string "cic:/Coq/ring/Ring_abstract/abstract_rings/Aone.var"
let abstract_rings_Azero_uri =
 uri_of_string "cic:/Coq/ring/Ring_abstract/abstract_rings/Azero.var"
let abstract_rings_Aopp_uri =
 uri_of_string "cic:/Coq/ring/Ring_abstract/abstract_rings/Aopp.var"
let abstract_rings_Aeq_uri =
 uri_of_string "cic:/Coq/ring/Ring_abstract/abstract_rings/Aeq.var"
let abstract_rings_vm_uri =
 uri_of_string "cic:/Coq/ring/Ring_abstract/abstract_rings/vm.var"
let abstract_rings_T_uri =
 uri_of_string "cic:/Coq/ring/Ring_abstract/abstract_rings/T.var"
let interp_ap_uri = uri_of_string "cic:/Coq/ring/Ring_abstract/interp_ap.con"
let interp_sacs_uri =
  uri_of_string "cic:/Coq/ring/Ring_abstract/interp_sacs.con"
let apolynomial_normalize_uri =
  uri_of_string "cic:/Coq/ring/Ring_abstract/apolynomial_normalize.con"
let apolynomial_normalize_ok_uri =
  uri_of_string "cic:/Coq/ring/Ring_abstract/apolynomial_normalize_ok.con"

(** CIC PREDICATES *)

  (**
    check whether a term is a constant or not, if argument "uri" is given and is
    not "None" also check if the constant correspond to the given one or not
  *)
let cic_is_const ?(uri: uri option = None) term =
  match uri with
  | None ->
      (match term with
        | Cic.Const _ -> true
        | _ -> false)
  | Some realuri ->
      (match term with
        | Cic.Const (u, _) when (eq u realuri) -> true
        | _ -> false)

(** PROOF AND GOAL ACCESSORS *)

  (**
    @param proof a proof
    @return the uri of a given proof
  *)
let uri_of_proof ~proof:(uri, _, _, _, _, _) = uri

  (**
    @param status current proof engine status
    @raise Failure if proof is None
    @return current goal's metasenv
  *)
let metasenv_of_status ((_,m,_,_,_, _), _) = m

  (**
    @param status a proof engine status
    @raise Failure when proof or goal are None
    @return context corresponding to current goal
  *)
let context_of_status status =
  let (proof, goal) = status in
  let metasenv = metasenv_of_status status in
  let _, context, _ = CicUtil.lookup_meta goal metasenv in
   context

(** CIC TERM CONSTRUCTORS *)

  (**
    Create a Cic term consisting of a constant
    @param uri URI of the constant
    @proof current proof
    @exp_named_subst explicit named substitution
  *)
let mkConst ~uri ~exp_named_subst =
  Cic.Const (uri, exp_named_subst)

  (**
    Create a Cic term consisting of a constructor
    @param uri triple <uri, typeno, consno> where uri is the uri of an inductive
    type, typeno is the type number in a mutind structure (0 based), consno is
    the constructor number (1 based)
    @exp_named_subst explicit named substitution
  *)
let mkCtor ~uri:(uri, typeno, consno) ~exp_named_subst =
 Cic.MutConstruct (uri, typeno, consno, exp_named_subst)

  (**
    Create a Cic term consisting of a type member of a mutual induction
    @param uri pair <uri, typeno> where uri is the uri of a mutual inductive
    type and typeno is the type number (0 based) in the mutual induction
    @exp_named_subst explicit named substitution
  *)
let mkMutInd ~uri:(uri, typeno) ~exp_named_subst =
 Cic.MutInd (uri, typeno, exp_named_subst)

(** EXCEPTIONS *)

  (**
    raised when the current goal is not ringable; a goal is ringable when is an
    equality on reals (@see r_uri)
  *)
exception GoalUnringable

(** RING's FUNCTIONS LIBRARY *)

  (**
    Check whether the ring tactic can be applied on a given term (i.e. that is
    an equality on reals)
    @param term to be tested
    @return true if the term is ringable, false otherwise
  *)
let ringable =
  let is_equality = function
    | Cic.MutInd (uri, 0, []) when (eq uri HelmLibraryObjects.Logic.eq_URI) -> true
    | _ -> false
  in
  let is_real = function
    | Cic.Const (uri, _) when (eq uri HelmLibraryObjects.Reals.r_URI) -> true
    | _ -> false
  in
  function
    | Cic.Appl (app::set::_::_::[]) when (is_equality app && is_real set) ->
        warn (lazy "Goal Ringable!");
        true
    | _ ->
        warn (lazy "Goal Not Ringable :-((");
        false

  (**
    split an equality goal of the form "t1 = t2" in its two subterms t1 and t2
    after checking that the goal is ringable
    @param goal the current goal
    @return a pair (t1,t2) that are two sides of the equality goal
    @raise GoalUnringable if the goal isn't ringable
  *)
let split_eq = function
  | (Cic.Appl (_::_::t1::t2::[])) as term when ringable term ->
        warn (lazy ("<term1>" ^ (CicPp.ppterm t1) ^ "</term1>"));
        warn (lazy ("<term2>" ^ (CicPp.ppterm t2) ^ "</term2>"));
        (t1, t2)
  | _ -> raise GoalUnringable

  (**
    @param i an integer index representing a 1 based number of node in a binary
    search tree counted in a fbs manner (i.e.: 1 is the root, 2 is the left
    child of the root (if any), 3 is the right child of the root (if any), 4 is
    the left child of the left child of the root (if any), ....)
    @param proof the current proof
    @return an index representing the same node in a varmap (@see varmap_uri),
    the returned index is as defined in index (@see index_uri)
  *)
let path_of_int n =
  let rec digits_of_int n =
    if n=1 then [] else (n mod 2 = 1)::(digits_of_int (n lsr 1))
  in
  List.fold_right
    (fun digit path ->
      Cic.Appl [
        mkCtor (if (digit = true) then right_idx_uri else left_idx_uri) [];
        path])
    (List.rev (digits_of_int n)) (* remove leading true (i.e. digit 1) *)
    (mkCtor end_idx_uri [])

  (**
    Build a variable map (@see varmap_uri) from a variables array.
    A variable map is almost a binary tree so this function receiving a var list
    like [v;w;x;y;z] will build a varmap of shape:       v
                                                        / \
                                                       w   x
                                                      / \
                                                     y   z
    @param vars variables array
    @return a cic term representing the variable map containing vars variables
  *)
let btree_of_array ~vars =
  let r = HelmLibraryObjects.Reals.r in
  let empty_vm_r = mkCtor empty_vm_uri [quote_varmap_A_uri,r] in
  let node_vm_r = mkCtor node_vm_uri [quote_varmap_A_uri,r] in
  let size = Array.length vars in
  let halfsize = size lsr 1 in
  let rec aux n =   (* build the btree starting from position n *)
      (*
        n is the position in the vars array _1_based_ in order to access
        left and right child using (n*2, n*2+1) trick
      *)
    if n > size then
      empty_vm_r
    else if n > halfsize then  (* no more children *)
      Cic.Appl [node_vm_r; vars.(n-1); empty_vm_r; empty_vm_r]
    else  (* still children *)
      Cic.Appl [node_vm_r; vars.(n-1); aux (n*2); aux (n*2+1)]
  in
  aux 1

  (**
    abstraction function:
    concrete polynoms       ----->      (abstract polynoms, varmap)
    @param terms list of conrete polynoms
    @return a pair <aterms, varmap> where aterms is a list of abstract polynoms
    and varmap is the variable map needed to interpret them
  *)
let abstract_poly ~terms =
  let varhash = Hashtbl.create 19 in (* vars hash, to speed up lookup *)
  let varlist = ref [] in  (* vars list in reverse order *)
  let counter = ref 1 in  (* index of next new variable *)
  let rec aux = function  (* TODO not tail recursive *)
    (* "bop" -> binary operator | "uop" -> unary operator *)
    | Cic.Appl (bop::t1::t2::[])
      when (cic_is_const ~uri:(Some HelmLibraryObjects.Reals.rplus_URI) bop) -> (* +. *)
        Cic.Appl [mkCtor applus_uri []; aux t1; aux t2]
    | Cic.Appl (bop::t1::t2::[])
      when (cic_is_const ~uri:(Some HelmLibraryObjects.Reals.rmult_URI) bop) -> (* *. *)
        Cic.Appl [mkCtor apmult_uri []; aux t1; aux t2]
    | Cic.Appl (uop::t::[])
      when (cic_is_const ~uri:(Some HelmLibraryObjects.Reals.ropp_URI) uop) -> (* ~-. *)
        Cic.Appl [mkCtor apopp_uri []; aux t]
    | t when (cic_is_const ~uri:(Some HelmLibraryObjects.Reals.r0_URI) t) -> (* 0. *)
        mkCtor ap0_uri []
    | t when (cic_is_const ~uri:(Some HelmLibraryObjects.Reals.r1_URI) t) -> (* 1. *)
        mkCtor ap1_uri []
    | t ->  (* variable *)
      try
        Hashtbl.find varhash t (* use an old var *)
      with Not_found -> begin (* create a new var *)
        let newvar =
          Cic.Appl [mkCtor apvar_uri []; path_of_int !counter]
        in
        incr counter;
        varlist := t :: !varlist;
        Hashtbl.add varhash t newvar;
        newvar
      end
  in
  let aterms = List.map aux terms in  (* abstract vars *)
  let varmap =  (* build varmap *)
    btree_of_array ~vars:(Array.of_list (List.rev !varlist))
  in
  (aterms, varmap)

  (**
    given a list of abstract terms (i.e. apolynomials) build the ring "segments"
    that is triples like (t', t'', t''') where
          t'    = interp_ap(varmap, at)
          t''   = interp_sacs(varmap, (apolynomial_normalize at))
          t'''  = apolynomial_normalize_ok(varmap, at)
    at is the abstract term built from t, t is a single member of aterms
  *)
let build_segments ~terms =
  let theory_args_subst varmap =
   [abstract_rings_A_uri, HelmLibraryObjects.Reals.r ;
    abstract_rings_Aplus_uri, HelmLibraryObjects.Reals.rplus ;
    abstract_rings_Amult_uri, HelmLibraryObjects.Reals.rmult ;
    abstract_rings_Aone_uri, HelmLibraryObjects.Reals.r1 ;
    abstract_rings_Azero_uri, HelmLibraryObjects.Reals.r0 ;
    abstract_rings_Aopp_uri, HelmLibraryObjects.Reals.ropp ;
    abstract_rings_vm_uri, varmap] in
  let theory_args_subst' eq varmap t =
   [abstract_rings_A_uri, HelmLibraryObjects.Reals.r ;
    abstract_rings_Aplus_uri, HelmLibraryObjects.Reals.rplus ;
    abstract_rings_Amult_uri, HelmLibraryObjects.Reals.rmult ;
    abstract_rings_Aone_uri, HelmLibraryObjects.Reals.r1 ;
    abstract_rings_Azero_uri, HelmLibraryObjects.Reals.r0 ;
    abstract_rings_Aopp_uri, HelmLibraryObjects.Reals.ropp ;
    abstract_rings_Aeq_uri, eq ;
    abstract_rings_vm_uri, varmap ;
    abstract_rings_T_uri, t] in
  let interp_ap varmap =
   mkConst interp_ap_uri (theory_args_subst varmap) in
  let interp_sacs varmap =
   mkConst interp_sacs_uri (theory_args_subst varmap) in
  let apolynomial_normalize = mkConst apolynomial_normalize_uri [] in
  let apolynomial_normalize_ok eq varmap t =
   mkConst apolynomial_normalize_ok_uri (theory_args_subst' eq varmap t) in
  let lxy_false =   (** Cic funcion "fun (x,y):R -> false" *)
    Cic.Lambda (Cic.Anonymous, HelmLibraryObjects.Reals.r,
      Cic.Lambda (Cic.Anonymous, HelmLibraryObjects.Reals.r, HelmLibraryObjects.Datatypes.falseb))
  in
  let (aterms, varmap) = abstract_poly ~terms in  (* abstract polys *)
  List.map    (* build ring segments *)
   (fun t ->
     Cic.Appl [interp_ap varmap ; t],
     Cic.Appl (
       [interp_sacs varmap ; Cic.Appl [apolynomial_normalize; t]]),
     Cic.Appl [apolynomial_normalize_ok lxy_false varmap HelmLibraryObjects.Reals.rtheory ; t]
   ) aterms


let status_of_single_goal_tactic_result =
 function
    proof,[goal] -> proof,goal
  | _ ->
    raise (Fail (lazy "status_of_single_goal_tactic_result: the tactic did not produce exactly a new goal"))

(* Galla: spostata in variousTactics.ml 
  (**
    auxiliary tactic "elim_type"
    @param status current proof engine status
    @param term term to cut
  *)
let elim_type_tac ~term status =
  warn (lazy "in Ring.elim_type_tac");
  Tacticals.thens ~start:(cut_tac ~term)
   ~continuations:[elim_simpl_intros_tac ~term:(Cic.Rel 1) ; Tacticals.id_tac] status
*)

  (**
    auxiliary tactic, use elim_type and try to close 2nd subgoal using proof
    @param status current proof engine status
    @param term term to cut
    @param proof term used to prove second subgoal generated by elim_type
  *)
(* FG: METTERE I NOMI ANCHE QUI? *)  
let elim_type2_tac ~term ~proof =
 let elim_type2_tac ~term ~proof status =
  let module E = EliminationTactics in
  warn (lazy "in Ring.elim_type2");
  ProofEngineTypes.apply_tactic 
   (Tacticals.thens ~start:(E.elim_type_tac term)
    ~continuations:[Tacticals.id_tac ; exact_tac ~term:proof]) status
 in
  ProofEngineTypes.mk_tactic (elim_type2_tac ~term ~proof)

(* Galla: spostata in variousTactics.ml
  (**
    Reflexivity tactic, try to solve current goal using "refl_eqT"
    Warning: this isn't equale to the coq's Reflexivity because this one tries
    only refl_eqT, coq's one also try "refl_equal"
    @param status current proof engine status
  *)
let reflexivity_tac (proof, goal) =
  warn (lazy "in Ring.reflexivity_tac");
  let refl_eqt = mkCtor ~uri:refl_eqt_uri ~exp_named_subst:[] in
  try
    apply_tac (proof, goal) ~term:refl_eqt
  with (Fail _) as e ->
    let e_str = Printexc.to_string e in
    raise (Fail ("Reflexivity failed with exception: " ^ e_str))
*)

  (** lift an 8-uple of debrujins indexes of n *)
let lift ~n (a,b,c,d,e,f,g,h) =
  match (List.map (CicSubstitution.lift n) [a;b;c;d;e;f;g;h]) with
  | [a;b;c;d;e;f;g;h] -> (a,b,c,d,e,f,g,h)
  | _ -> assert false

  (**
    remove hypothesis from a given status starting from the last one
    @param count number of hypotheses to remove
    @param status current proof engine status
  *)
let purge_hyps_tac ~count =
 let purge_hyps_tac ~count status =
  let module S = ProofEngineStructuralRules in
  let (proof, goal) = status in
  let rec aux n context status =
    assert(n>=0);
    match (n, context) with
    | (0, _) -> status
    | (n, hd::tl) ->
        let name_of_hyp =
         match hd with
            None
          | Some (Cic.Anonymous,_) -> assert false
          | Some (Cic.Name name,_) -> name
        in
         aux (n-1) tl
          (status_of_single_goal_tactic_result 
	   (ProofEngineTypes.apply_tactic (S.clear ~hyps:[name_of_hyp]) status))
    | (_, []) -> failwith "Ring.purge_hyps_tac: no hypotheses left"
  in
   let (_, metasenv, _subst, _, _, _) = proof in
    let (_, context, _) = CicUtil.lookup_meta goal metasenv in
     let proof',goal' = aux count context status in
      assert (goal = goal') ;
      proof',[goal']
 in
  ProofEngineTypes.mk_tactic (purge_hyps_tac ~count)

(** THE TACTIC! *)

  (**
    Ring tactic, does associative and commutative rewritings in Reals ring
    @param status current proof engine status
  *)
 
let ring_tac status =
  let (proof, goal) = status in
  warn (lazy "in Ring tactic");
  let eqt = mkMutInd (HelmLibraryObjects.Logic.eq_URI, 0) [] in
  let r = HelmLibraryObjects.Reals.r in
  let metasenv = metasenv_of_status status in
  let (metano, context, ty) = CicUtil.lookup_meta goal metasenv in
  let (t1, t2) = split_eq ty in (* goal like t1 = t2 *)
  match (build_segments ~terms:[t1; t2]) with
  | (t1', t1'', t1'_eq_t1'')::(t2', t2'', t2'_eq_t2'')::[] -> begin
     if debug then
      List.iter  (* debugging, feel free to remove *)
        (fun (descr, term) ->
          warn (lazy (descr ^ " " ^ (CicPp.ppterm term))))
        (List.combine
          ["t1"; "t1'"; "t1''"; "t1'_eq_t1''";
           "t2"; "t2'"; "t2''"; "t2'_eq_t2''"]
          [t1; t1'; t1''; t1'_eq_t1'';
           t2; t2'; t2''; t2'_eq_t2'']);
      try
        let new_hyps = ref 0 in  (* number of new hypotheses created *)
	ProofEngineTypes.apply_tactic 
         (Tacticals.first
          ~tactics:[
            EqualityTactics.reflexivity_tac ;
            exact_tac ~term:t1'_eq_t1'' ;
            exact_tac ~term:t2'_eq_t2'' ;
            exact_tac
            ~term:(
              Cic.Appl
               [mkConst HelmLibraryObjects.Logic.sym_eq_URI
                 [equality_is_a_congruence_A, HelmLibraryObjects.Reals.r;
                  equality_is_a_congruence_x, t1'' ;
                  equality_is_a_congruence_y, t1
                 ] ;
                t1'_eq_t1''
               ]) ;
            ProofEngineTypes.mk_tactic (fun status ->
              let status' = (* status after 1st elim_type use *)
                let context = context_of_status status in
		let b,_ = (*TASSI : FIXME*)
		  are_convertible context t1'' t1 CicUniv.oblivion_ugraph in 
                if not b then begin
                  warn (lazy "t1'' and t1 are NOT CONVERTIBLE");
                  let newstatus =
		    ProofEngineTypes.apply_tactic 
                    (elim_type2_tac  (* 1st elim_type use *)
                      ~proof:t1'_eq_t1''
                      ~term:(Cic.Appl [eqt; r; t1''; t1]))
		    status 
                  in
                   incr new_hyps; (* elim_type add an hyp *)
                   match newstatus with
                      (proof,[goal]) -> proof,goal
                    | _ -> assert false
                end else begin
                  warn (lazy "t1'' and t1 are CONVERTIBLE");
                  status
                end
              in
              let (t1,t1',t1'',t1'_eq_t1'',t2,t2',t2'',t2'_eq_t2'') =
                lift 1 (t1,t1',t1'',t1'_eq_t1'', t2,t2',t2'',t2'_eq_t2'')
              in
              let status'' =
	       ProofEngineTypes.apply_tactic
                (Tacticals.first (* try to solve 1st subgoal *)
                  ~tactics:[
                    exact_tac ~term:t2'_eq_t2'';
                    exact_tac
                       ~term:(
                         Cic.Appl
                          [mkConst HelmLibraryObjects.Logic.sym_eq_URI
                            [equality_is_a_congruence_A, HelmLibraryObjects.Reals.r;
                             equality_is_a_congruence_x, t2'' ;
                             equality_is_a_congruence_y, t2
                            ] ;
                           t2'_eq_t2''
                          ]) ;
		     ProofEngineTypes.mk_tactic (fun status ->
                      let status' =
                        let context = context_of_status status in
			let b,_ = (* TASSI:FIXME *)
			  are_convertible context t2'' t2
                          CicUniv.oblivion_ugraph 
			in
			  if not b then begin 
                          warn (lazy "t2'' and t2 are NOT CONVERTIBLE");
                          let newstatus =
			    ProofEngineTypes.apply_tactic 
                             (elim_type2_tac  (* 2nd elim_type use *)
                              ~proof:t2'_eq_t2''
                              ~term:(Cic.Appl [eqt; r; t2''; t2]))
			     status
                          in
                          incr new_hyps; (* elim_type add an hyp *)
                          match newstatus with
                             (proof,[goal]) -> proof,goal
                           | _ -> assert false
                        end else begin
                          warn (lazy "t2'' and t2 are CONVERTIBLE");
                          status
                        end
                      in
                      try (* try to solve main goal *)
                        warn (lazy "trying reflexivity ....");
                        ProofEngineTypes.apply_tactic 
			 EqualityTactics.reflexivity_tac status'
                      with (Fail _) ->  (* leave conclusion to the user *)
                        warn (lazy "reflexivity failed, solution's left as an ex :-)");
                        ProofEngineTypes.apply_tactic 
			 (purge_hyps_tac ~count:!new_hyps) status')])
		  status'	
              in
              status'')])
	 status      
      with (Fail s) ->
        raise (Fail (lazy ("Ring failure: " ^ Lazy.force s)))
    end
  | _ -> (* impossible: we are applying ring exacty to 2 terms *)
    assert false

  (* wrap ring_tac catching GoalUnringable and raising Fail *)

let ring_tac status =
  try
    ring_tac status
  with GoalUnringable ->
    raise (Fail (lazy "goal unringable"))

let ring_tac = ProofEngineTypes.mk_tactic ring_tac

