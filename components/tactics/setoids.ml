(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id: setoid_replace.ml 8900 2006-06-06 14:40:27Z letouzey $ *)

module T = Tacticals
module RT = ReductionTactics
module PET = ProofEngineTypes

let default_eq () =
 match LibraryObjects.eq_URI () with
    Some uri -> uri
  | None ->
    raise (ProofEngineTypes.Fail (lazy "You need to register the default equality first. Please use the \"default\" command"))

let replace = ref (fun _ _ -> assert false)
let register_replace f = replace := f

let general_rewrite = ref (fun _ _ -> assert false)
let register_general_rewrite f = general_rewrite := f

let prlist_with_sepi sep elem =
 let rec aux n =
  function
   | []   -> ""
   | [h]  -> elem n h
   | h::t ->
      let e = elem n h and r = aux (n+1) t in
      e ^ sep ^ r
 in
  aux 1

type relation =
   { rel_a: Cic.term ;
     rel_aeq: Cic.term;
     rel_refl: Cic.term option;
     rel_sym: Cic.term option;
     rel_trans : Cic.term option;
     rel_quantifiers_no: int  (* it helps unification *);
     rel_X_relation_class: Cic.term;
     rel_Xreflexive_relation_class: Cic.term
   }

type 'a relation_class =
   Relation of 'a            (* the rel_aeq of the relation or the relation   *)
 | Leibniz of Cic.term option (* the carrier (if eq is partially instantiated)*)

type 'a morphism =
    { args : (bool option * 'a relation_class) list;
      output : 'a relation_class;
      lem : Cic.term;
      morphism_theory : Cic.term
    }

type funct =
    { f_args : Cic.term list;
      f_output : Cic.term
    }

type morphism_class =
   ACMorphism of relation morphism
 | ACFunction of funct

let constr_relation_class_of_relation_relation_class =
 function
    Relation relation -> Relation relation.rel_aeq
  | Leibniz t -> Leibniz t
 

(*COQ
let constr_of c = Constrintern.interp_constr Evd.empty (Global.env()) c
*)

(*COQ
let constant dir s = Coqlib.gen_constant "Setoid_replace" ("Setoids"::dir) s
*) let constant dir s = Cic.Implicit None
(*COQ
let gen_constant dir s = Coqlib.gen_constant "Setoid_replace" dir s
*) let gen_constant dir s = Cic.Implicit None
(*COQ
let reference dir s = Coqlib.gen_reference "Setoid_replace" ("Setoids"::dir) s
let eval_reference dir s = EvalConstRef (destConst (constant dir s))
*) let eval_reference dir s = Cic.Implicit None
(*COQ
let eval_init_reference dir s = EvalConstRef (destConst (gen_constant ("Init"::dir) s))
*)

(*COQ
let current_constant id =
  try
    global_reference id
  with Not_found ->
    anomaly ("Setoid: cannot find " ^ id)
*) let current_constant id = assert false

(* From Setoid.v *)

let coq_reflexive =
 (gen_constant ["Relations"; "Relation_Definitions"] "reflexive")
let coq_symmetric =
 (gen_constant ["Relations"; "Relation_Definitions"] "symmetric")
let coq_transitive =
 (gen_constant ["Relations"; "Relation_Definitions"] "transitive")
let coq_relation =
 (gen_constant ["Relations"; "Relation_Definitions"] "relation")

let coq_Relation_Class = (constant ["Setoid"] "Relation_Class")
let coq_Argument_Class = (constant ["Setoid"] "Argument_Class")
let coq_Setoid_Theory = (constant ["Setoid"] "Setoid_Theory")
let coq_Morphism_Theory = (constant ["Setoid"] "Morphism_Theory")
let coq_Build_Morphism_Theory= (constant ["Setoid"] "Build_Morphism_Theory")
let coq_Compat = (constant ["Setoid"] "Compat")

let coq_AsymmetricReflexive = (constant ["Setoid"] "AsymmetricReflexive")
let coq_SymmetricReflexive = (constant ["Setoid"] "SymmetricReflexive")
let coq_SymmetricAreflexive = (constant ["Setoid"] "SymmetricAreflexive")
let coq_AsymmetricAreflexive = (constant ["Setoid"] "AsymmetricAreflexive")
let coq_Leibniz = (constant ["Setoid"] "Leibniz")

let coq_RAsymmetric = (constant ["Setoid"] "RAsymmetric")
let coq_RSymmetric = (constant ["Setoid"] "RSymmetric")
let coq_RLeibniz = (constant ["Setoid"] "RLeibniz")

let coq_ASymmetric = (constant ["Setoid"] "ASymmetric")
let coq_AAsymmetric = (constant ["Setoid"] "AAsymmetric")

let coq_seq_refl = (constant ["Setoid"] "Seq_refl")
let coq_seq_sym = (constant ["Setoid"] "Seq_sym")
let coq_seq_trans = (constant ["Setoid"] "Seq_trans")

let coq_variance = (constant ["Setoid"] "variance")
let coq_Covariant = (constant ["Setoid"] "Covariant")
let coq_Contravariant = (constant ["Setoid"] "Contravariant")
let coq_Left2Right = (constant ["Setoid"] "Left2Right")
let coq_Right2Left = (constant ["Setoid"] "Right2Left")
let coq_MSNone = (constant ["Setoid"] "MSNone")
let coq_MSCovariant = (constant ["Setoid"] "MSCovariant")
let coq_MSContravariant = (constant ["Setoid"] "MSContravariant")

let coq_singl = (constant ["Setoid"] "singl")
let coq_cons = (constant ["Setoid"] "cons")

let coq_equality_morphism_of_asymmetric_areflexive_transitive_relation =
 (constant ["Setoid"]
  "equality_morphism_of_asymmetric_areflexive_transitive_relation")
let coq_equality_morphism_of_symmetric_areflexive_transitive_relation =
 (constant ["Setoid"]
  "equality_morphism_of_symmetric_areflexive_transitive_relation")
let coq_equality_morphism_of_asymmetric_reflexive_transitive_relation =
 (constant ["Setoid"]
  "equality_morphism_of_asymmetric_reflexive_transitive_relation")
let coq_equality_morphism_of_symmetric_reflexive_transitive_relation =
 (constant ["Setoid"]
  "equality_morphism_of_symmetric_reflexive_transitive_relation")
let coq_make_compatibility_goal =
 (constant ["Setoid"] "make_compatibility_goal")
let coq_make_compatibility_goal_eval_ref =
 (eval_reference ["Setoid"] "make_compatibility_goal")
let coq_make_compatibility_goal_aux_eval_ref =
 (eval_reference ["Setoid"] "make_compatibility_goal_aux")

let coq_App = (constant ["Setoid"] "App")
let coq_ToReplace = (constant ["Setoid"] "ToReplace")
let coq_ToKeep = (constant ["Setoid"] "ToKeep")
let coq_ProperElementToKeep = (constant ["Setoid"] "ProperElementToKeep")
let coq_fcl_singl = (constant ["Setoid"] "fcl_singl")
let coq_fcl_cons = (constant ["Setoid"] "fcl_cons")

let coq_setoid_rewrite = (constant ["Setoid"] "setoid_rewrite")
let coq_proj1 = (gen_constant ["Init"; "Logic"] "proj1")
let coq_proj2 = (gen_constant ["Init"; "Logic"] "proj2")
let coq_unit = (gen_constant ["Init"; "Datatypes"] "unit")
let coq_tt = (gen_constant ["Init"; "Datatypes"] "tt")
let coq_eq = (gen_constant ["Init"; "Logic"] "eq")

let coq_morphism_theory_of_function =
 (constant ["Setoid"] "morphism_theory_of_function")
let coq_morphism_theory_of_predicate =
 (constant ["Setoid"] "morphism_theory_of_predicate")
let coq_relation_of_relation_class =
 (eval_reference ["Setoid"] "relation_of_relation_class")
let coq_directed_relation_of_relation_class =
 (eval_reference ["Setoid"] "directed_relation_of_relation_class")
let coq_interp = (eval_reference ["Setoid"] "interp")
let coq_Morphism_Context_rect2 =
 (eval_reference ["Setoid"] "Morphism_Context_rect2")
let coq_iff = (gen_constant ["Init";"Logic"] "iff")
let coq_impl = (constant ["Setoid"] "impl")


(************************* Table of declared relations **********************)


(* Relations are stored in a table which is synchronised with the Reset mechanism. *)

module Gmap =
 Map.Make(struct type t = Cic.term let compare = Pervasives.compare end);;

let relation_table = ref Gmap.empty

let relation_table_add (s,th) = relation_table := Gmap.add s th !relation_table
let relation_table_find s = Gmap.find s !relation_table
let relation_table_mem s = Gmap.mem s !relation_table

let prrelation s =
  "(" ^ CicPp.ppterm s.rel_a ^ "," ^ CicPp.ppterm s.rel_aeq ^ ")"

let prrelation_class =
 function
    Relation eq  ->
     (try prrelation (relation_table_find eq)
      with Not_found ->
       "[[ Error: " ^ CicPp.ppterm eq ^
        " is not registered as a relation ]]")
  | Leibniz (Some ty) -> CicPp.ppterm ty
  | Leibniz None -> "_"

let prmorphism_argument_gen prrelation (variance,rel) =
 prrelation rel ^
  match variance with
     None -> " ==> "
   | Some true -> " ++> "
   | Some false -> " --> "

let prargument_class = prmorphism_argument_gen prrelation_class

let pr_morphism_signature (l,c) =
 String.concat "" (List.map (prmorphism_argument_gen CicPp.ppterm) l) ^
  CicPp.ppterm c

let prmorphism k m =
  CicPp.ppterm k ^ ": " ^
  String.concat "" (List.map prargument_class m.args) ^
  prrelation_class m.output

(* A function that gives back the only relation_class on a given carrier *)
(*CSC: this implementation is really inefficient. I should define a new
  map to make it efficient. However, is this really worth of? *)
let default_relation_for_carrier ?(filter=fun _ -> true) a =
 let rng =  Gmap.fold (fun _ y acc -> y::acc) !relation_table [] in
 match List.filter (fun ({rel_a=rel_a} as r) -> rel_a = a && filter r) rng with
    [] -> Leibniz (Some a)
  | relation::tl ->
(*COQ
     if tl <> [] then
      prerr_endline
       ("Warning: There are several relations on the carrier \"" ^
         CicPp.ppterm a ^ "\". The relation " ^ prrelation relation ^
         " is chosen.") ;
*)
     Relation relation

let find_relation_class rel =
 try Relation (relation_table_find rel)
 with
  Not_found ->
   let default_eq = default_eq () in
    match CicReduction.whd [] rel with
       Cic.Appl [Cic.MutInd(uri,0,[]);ty]
        when UriManager.eq uri default_eq -> Leibniz (Some ty)
     | Cic.MutInd(uri,0,[]) when UriManager.eq uri default_eq -> Leibniz None
     | _ -> raise Not_found

(*COQ
let coq_iff_relation = lazy (find_relation_class (Lazy.force coq_iff))
let coq_impl_relation = lazy (find_relation_class (Lazy.force coq_impl))
*) let coq_iff_relation = Obj.magic 0 let coq_impl_relation = Obj.magic 0

let relation_morphism_of_constr_morphism =
 let relation_relation_class_of_constr_relation_class =
  function
     Leibniz t -> Leibniz t
   | Relation aeq ->
      Relation (try relation_table_find aeq with Not_found -> assert false)
 in
  function mor ->
   let args' =
    List.map
     (fun (variance,rel) ->
       variance, relation_relation_class_of_constr_relation_class rel
     ) mor.args in
   let output' = relation_relation_class_of_constr_relation_class mor.output in
    {mor with args=args' ; output=output'}

let equiv_list () =
 Gmap.fold (fun _ y acc -> y.rel_aeq::acc) !relation_table []

(* Declare a new type of object in the environment : "relation-theory". *)

let relation_to_obj (s, th) =
   let th' =
    if relation_table_mem s then
     begin
      let old_relation = relation_table_find s in
       let th' =
        {th with rel_sym =
          match th.rel_sym with
             None -> old_relation.rel_sym
           | Some t -> Some t}
       in
        prerr_endline
         ("Warning: The relation " ^ prrelation th' ^
          " is redeclared. The new declaration" ^
           (match th'.rel_refl with
              None -> ""
            | Some t -> " (reflevity proved by " ^ CicPp.ppterm t) ^
           (match th'.rel_sym with
               None -> ""
             | Some t ->
                (if th'.rel_refl = None then " (" else " and ") ^
                "symmetry proved by " ^ CicPp.ppterm t) ^
           (if th'.rel_refl <> None && th'.rel_sym <> None then
             ")" else "") ^
           " replaces the old declaration" ^
           (match old_relation.rel_refl with
              None -> ""
            | Some t -> " (reflevity proved by " ^ CicPp.ppterm t) ^
           (match old_relation.rel_sym with
               None -> ""
             | Some t ->
                (if old_relation.rel_refl = None then
                  " (" else " and ") ^
                "symmetry proved by " ^ CicPp.ppterm t) ^
           (if old_relation.rel_refl <> None && old_relation.rel_sym <> None
            then ")" else "") ^
           ".");
        th'
     end
    else
     th
   in
    relation_table_add (s,th')

(******************************* Table of declared morphisms ********************)

(* Setoids are stored in a table which is synchronised with the Reset mechanism. *)

let morphism_table = ref Gmap.empty

let morphism_table_find m = Gmap.find m !morphism_table
let morphism_table_add (m,c) =
 let old =
  try
   morphism_table_find m
  with
   Not_found -> []
 in
  try
(*COQ
   let old_morph =
    List.find
     (function mor -> mor.args = c.args && mor.output = c.output) old
   in
    prerr_endline
     ("Warning: The morphism " ^ prmorphism m old_morph ^
      " is redeclared. " ^
      "The new declaration whose compatibility is proved by " ^
       CicPp.ppterm c.lem ^ " replaces the old declaration whose" ^
       " compatibility was proved by " ^
       CicPp.ppterm old_morph.lem ^ ".")
*) ()
  with
   Not_found -> morphism_table := Gmap.add m (c::old) !morphism_table

let default_morphism ?(filter=fun _ -> true) m =
  match List.filter filter (morphism_table_find m) with
      [] -> raise Not_found
    | m1::ml ->
(*COQ
        if ml <> [] then
          prerr_endline
            ("Warning: There are several morphisms associated to \"" ^
            CicPp.ppterm m ^ "\". Morphism " ^ prmorphism m m1 ^
            " is randomly chosen.");
*)
        relation_morphism_of_constr_morphism m1

(************************** Printing relations and morphisms **********************)

let print_setoids () =
  Gmap.iter
   (fun k relation ->
     assert (k=relation.rel_aeq) ;
     prerr_endline ("Relation " ^ prrelation relation ^ ";" ^
      (match relation.rel_refl with
          None -> ""
        | Some t -> " reflexivity proved by " ^ CicPp.ppterm t) ^
      (match relation.rel_sym with
          None -> ""
        | Some t -> " symmetry proved by " ^ CicPp.ppterm t) ^
      (match relation.rel_trans with
          None -> ""
        | Some t -> " transitivity proved by " ^ CicPp.ppterm t)))
   !relation_table ;
  Gmap.iter
   (fun k l ->
     List.iter
      (fun ({lem=lem} as mor) ->
        prerr_endline ("Morphism " ^ prmorphism k mor ^
        ". Compatibility proved by " ^
        CicPp.ppterm lem ^ "."))
      l) !morphism_table
;;

(***************** Adding a morphism to the database ****************************)

(* We maintain a table of the currently edited proofs of morphism lemma
   in order to add them in the morphism_table when the user does Save *)

let edited = ref Gmap.empty

let new_edited id m = 
  edited := Gmap.add id m !edited

let is_edited id =
  Gmap.mem id !edited

let no_more_edited id =
  edited := Gmap.remove id !edited

let what_edited id =
  Gmap.find id !edited

let list_chop n l =
  let rec chop_aux acc = function
    | (0, l2) -> (List.rev acc, l2)
    | (n, (h::t)) -> chop_aux (h::acc) (pred n, t)
    | (_, []) -> assert false
  in
  chop_aux [] (n,l)

let compose_thing f l b =
 let rec aux =
  function
     (0, env, b) -> b
   | (n, ((v,t)::l), b) -> aux (n-1,  l, f v t b)
   | _ -> assert false
 in
  aux (List.length l,l,b)

let compose_prod = compose_thing (fun v t b -> Cic.Prod (v,t,b))
let compose_lambda = compose_thing (fun v t b -> Cic.Lambda (v,t,b))

(* also returns the triple (args_ty_quantifiers_rev,real_args_ty,real_output)
   where the args_ty and the output are delifted *)
let check_is_dependent n args_ty output =
 let m = List.length args_ty - n in
 let args_ty_quantifiers, args_ty = list_chop n args_ty in
  let rec aux m t =
   match t with
      Cic.Prod (n,s,t) when m > 0 ->
       let t' = CicSubstitution.subst (Cic.Implicit None) (* dummy *) t in
       if t' <> t then
        let args,out = aux (m - 1) t' in s::args,out
       else
        raise (ProofEngineTypes.Fail (lazy
         "The morphism is not a quantified non dependent product."))
    | _ -> [],t
  in
   let ty = compose_prod (List.rev args_ty) output in
   let args_ty, output = aux m ty in
   List.rev args_ty_quantifiers, args_ty, output

let cic_relation_class_of_X_relation typ value =
 function
    {rel_a=rel_a; rel_aeq=rel_aeq; rel_refl=Some refl; rel_sym=None} ->
     Cic.Appl [coq_AsymmetricReflexive ; typ ; value ; rel_a ; rel_aeq; refl]
  | {rel_a=rel_a; rel_aeq=rel_aeq; rel_refl=Some refl; rel_sym=Some sym} ->
     Cic.Appl [coq_SymmetricReflexive ; typ ; rel_a ; rel_aeq; sym ; refl]
  | {rel_a=rel_a; rel_aeq=rel_aeq; rel_refl=None; rel_sym=None} ->
     Cic.Appl [coq_AsymmetricAreflexive ; typ ; value ; rel_a ; rel_aeq]
  | {rel_a=rel_a; rel_aeq=rel_aeq; rel_refl=None; rel_sym=Some sym} ->
     Cic.Appl [coq_SymmetricAreflexive ; typ ; rel_a ; rel_aeq; sym]

let cic_relation_class_of_X_relation_class typ value =
 function
    Relation {rel_X_relation_class=x_relation_class} ->
     Cic.Appl [x_relation_class ; typ ; value]
  | Leibniz (Some t) ->
     Cic.Appl [coq_Leibniz ; typ ; t]
  | Leibniz None -> assert false


let cic_precise_relation_class_of_relation =
 function
    {rel_a=rel_a; rel_aeq=rel_aeq; rel_refl=Some refl; rel_sym=None} ->
      Cic.Appl [coq_RAsymmetric ; rel_a ; rel_aeq; refl]
  | {rel_a=rel_a; rel_aeq=rel_aeq; rel_refl=Some refl; rel_sym=Some sym} ->
      Cic.Appl [coq_RSymmetric ; rel_a ; rel_aeq; sym ; refl]
  | {rel_a=rel_a; rel_aeq=rel_aeq; rel_refl=None; rel_sym=None} ->
      Cic.Appl [coq_AAsymmetric ; rel_a ; rel_aeq]
  | {rel_a=rel_a; rel_aeq=rel_aeq; rel_refl=None; rel_sym=Some sym} ->
      Cic.Appl [coq_ASymmetric ; rel_a ; rel_aeq; sym]

let cic_precise_relation_class_of_relation_class =
 function
    Relation
     {rel_aeq=rel_aeq; rel_Xreflexive_relation_class=lem; rel_refl=rel_refl }
     ->
      rel_aeq,lem,not(rel_refl=None)
  | Leibniz (Some t) ->
     Cic.Appl [coq_eq ; t], Cic.Appl [coq_RLeibniz ; t], true
  | Leibniz None -> assert false

let cic_relation_class_of_relation_class rel =
 cic_relation_class_of_X_relation_class
  coq_unit coq_tt rel

let cic_argument_class_of_argument_class (variance,arg) =
 let coq_variant_value =
  match variance with
     None -> coq_Covariant (* dummy value, it won't be used *)
   | Some true -> coq_Covariant
   | Some false -> coq_Contravariant
 in
  cic_relation_class_of_X_relation_class coq_variance
   coq_variant_value arg

let cic_arguments_of_argument_class_list args =
 let rec aux =
  function
     [] -> assert false
   | [last] ->
      Cic.Appl [coq_singl ; coq_Argument_Class ; last]
   | he::tl ->
      Cic.Appl [coq_cons ; coq_Argument_Class ; he ; aux tl]
 in
  aux (List.map cic_argument_class_of_argument_class args)

let gen_compat_lemma_statement quantifiers_rev output args m =
 let output = cic_relation_class_of_relation_class output in
 let args = cic_arguments_of_argument_class_list args in
  args, output,
   compose_prod quantifiers_rev
    (Cic.Appl [coq_make_compatibility_goal ; args ; output ; m])

let morphism_theory_id_of_morphism_proof_id id =
 id ^ "_morphism_theory"

let list_map_i f =
  let rec map_i_rec i = function
    | [] -> []
    | x::l -> let v = f i x in v :: map_i_rec (i+1) l
  in
  map_i_rec

(* apply_to_rels c [l1 ; ... ; ln] returns (c Rel1 ... reln) *)
let apply_to_rels c l =
 if l = [] then c
 else
  let len = List.length l in
   Cic.Appl (c::(list_map_i (fun i _ -> Cic.Rel (len - i)) 0 l))

let apply_to_relation subst rel =
 if subst = [] then rel
 else
  let new_quantifiers_no = rel.rel_quantifiers_no - List.length subst in
   assert (new_quantifiers_no >= 0) ;
   { rel_a = Cic.Appl (rel.rel_a :: subst) ;
     rel_aeq = Cic.Appl (rel.rel_aeq :: subst) ;
     rel_refl = HExtlib.map_option (fun c -> Cic.Appl (c::subst)) rel.rel_refl ; 
     rel_sym = HExtlib.map_option (fun c -> Cic.Appl (c::subst)) rel.rel_sym;
     rel_trans = HExtlib.map_option (fun c -> Cic.Appl (c::subst)) rel.rel_trans;
     rel_quantifiers_no = new_quantifiers_no;
     rel_X_relation_class = Cic.Appl (rel.rel_X_relation_class::subst);
     rel_Xreflexive_relation_class =
      Cic.Appl (rel.rel_Xreflexive_relation_class::subst) }

let add_morphism lemma_infos mor_name (m,quantifiers_rev,args,output) =
 let lem =
  match lemma_infos with
     None ->
      (* the Morphism_Theory object has already been created *)
      let applied_args =
       let len = List.length quantifiers_rev in
       let subst =
        list_map_i (fun i _ -> Cic.Rel (len - i)) 0 quantifiers_rev
       in
        List.map
         (fun (v,rel) ->
           match rel with
              Leibniz (Some t) ->
               assert (subst=[]);
               v, Leibniz (Some t)
            | Leibniz None ->
               (match subst with
                   [e] -> v, Leibniz (Some e)
                 | _ -> assert false)
            | Relation rel -> v, Relation (apply_to_relation subst rel)) args
      in
       compose_lambda quantifiers_rev
        (Cic.Appl
          [coq_Compat ;
           cic_arguments_of_argument_class_list applied_args;
           cic_relation_class_of_relation_class output;
           apply_to_rels (current_constant mor_name) quantifiers_rev])
   | Some (lem_name,argsconstr,outputconstr) ->
      (* only the compatibility has been proved; we need to declare the
         Morphism_Theory object *)
     let mext = current_constant lem_name in
(*COQ
     ignore (
      Declare.declare_internal_constant mor_name
       (DefinitionEntry
         {const_entry_body =
           compose_lambda quantifiers_rev
            (Cic.Appl
              [coq_Build_Morphism_Theory;
               argsconstr; outputconstr; apply_to_rels m quantifiers_rev ;
               apply_to_rels mext quantifiers_rev]);
          const_entry_boxed = Options.boxed_definitions()},
	IsDefinition Definition)) ;
*)ignore (assert false);
     mext 
 in
  let mmor = current_constant mor_name in
  let args_constr =
   List.map
    (fun (variance,arg) ->
      variance, constr_relation_class_of_relation_relation_class arg) args in
  let output_constr = constr_relation_class_of_relation_relation_class output in
(*COQ
   Lib.add_anonymous_leaf
    (morphism_to_obj (m, 
      { args = args_constr;
        output = output_constr;
        lem = lem;
        morphism_theory = mmor }));
*)let _ = mmor,args_constr,output_constr,lem in ignore (assert false);
   (*COQ Options.if_verbose prerr_endline (CicPp.ppterm m ^ " is registered as a morphism")   *) ()

let list_sub _ _ _ = assert false

(* first order matching with a bit of conversion *)
let unify_relation_carrier_with_type env rel t =
 let raise_error quantifiers_no =
  raise (ProofEngineTypes.Fail (lazy
   ("One morphism argument or its output has type " ^ CicPp.ppterm t ^
    " but the signature requires an argument of type \"" ^
    CicPp.ppterm rel.rel_a ^ " " ^ String.concat " " (List.map (fun _ ->  "?")
     (Array.to_list (Array.make quantifiers_no 0))) ^ "\""))) in
 let args =
  match t with
     Cic.Appl (he'::args') ->
      let argsno = List.length args' - rel.rel_quantifiers_no in
      let args1 = list_sub args' 0 argsno in
      let args2 = list_sub args' argsno rel.rel_quantifiers_no in
       if fst (CicReduction.are_convertible [] rel.rel_a (Cic.Appl (he'::args1))
       CicUniv.oblivion_ugraph) then
        args2
       else
        raise_error rel.rel_quantifiers_no
   | _  ->
     if rel.rel_quantifiers_no = 0 && fst (CicReduction.are_convertible []
     rel.rel_a t CicUniv.oblivion_ugraph) then
      [] 
     else
      begin
(*COQ
        let evars,args,instantiated_rel_a =
         let ty = CicTypeChecker.type_of_aux' [] [] rel.rel_a
         CicUniv.oblivion_ugraph in
         let evd = Evd.create_evar_defs Evd.empty in
         let evars,args,concl =
          Clenv.clenv_environments_evars env evd
           (Some rel.rel_quantifiers_no) ty
         in
          evars, args,
          nf_betaiota
           (match args with [] -> rel.rel_a | _ -> applist (rel.rel_a,args))
        in
         let evars' =
          w_unify true (*??? or false? *) env Reduction.CONV (*??? or cumul? *)
           ~mod_delta:true (*??? or true? *) t instantiated_rel_a evars in
         let args' =
          List.map (Reductionops.nf_evar (Evd.evars_of evars')) args
         in
          args'
*) assert false
      end
 in
  apply_to_relation args rel

let unify_relation_class_carrier_with_type env rel t =
 match rel with
    Leibniz (Some t') ->
     if fst (CicReduction.are_convertible [] t t' CicUniv.oblivion_ugraph) then
      rel
     else
      raise (ProofEngineTypes.Fail (lazy
       ("One morphism argument or its output has type " ^ CicPp.ppterm t ^
        " but the signature requires an argument of type " ^
        CicPp.ppterm t')))
  | Leibniz None -> Leibniz (Some t)
  | Relation rel -> Relation (unify_relation_carrier_with_type env rel t)

exception Impossible

(*COQ
(* first order matching with a bit of conversion *)
(* Note: the type checking operations performed by the function could  *)
(* be done once and for all abstracting the morphism structure using   *)
(* the quantifiers. Would the new structure be more suited than the    *)
(* existent one for other tasks to? (e.g. pretty printing would expose *)
(* much more information: is it ok or is it too much information?)     *)
let unify_morphism_with_arguments gl (c,al)
     {args=args; output=output; lem=lem; morphism_theory=morphism_theory} t
=
 let allen = List.length al in 
 let argsno = List.length args in
 if allen < argsno then raise Impossible; (* partial application *)
 let quantifiers,al' = Util.list_chop (allen - argsno) al in
 let c' = Cic.Appl (c::quantifiers) in
 if dependent t c' then raise Impossible; 
 (* these are pf_type_of we could avoid *)
 let al'_type = List.map (Tacmach.pf_type_of gl) al' in
 let args' =
   List.map2
     (fun (var,rel) ty ->
	var,unify_relation_class_carrier_with_type (pf_env gl) rel ty)
     args al'_type in
 (* this is another pf_type_of we could avoid *)
 let ty = Tacmach.pf_type_of gl (Cic.Appl (c::al)) in
 let output' = unify_relation_class_carrier_with_type (pf_env gl) output ty in
 let lem' = Cic.Appl (lem::quantifiers) in
 let morphism_theory' = Cic.Appl (morphism_theory::quantifiers) in
 ({args=args'; output=output'; lem=lem'; morphism_theory=morphism_theory'},
  c',al')
*) let unify_morphism_with_arguments _ _ _ _ = assert false

let new_morphism m signature id hook =
(*COQ
 if Nametab.exists_cci (Lib.make_path id) or is_section_variable id then
  raise (ProofEngineTypes.Fail (lazy (pr_id id ^ " already exists")))
 else
  let env = Global.env() in
  let typeofm = Typing.type_of env Evd.empty m in
  let typ = clos_norm_flags Closure.betaiotazeta empty_env Evd.empty typeofm in
  let argsrev, output =
   match signature with
      None -> decompose_prod typ
    | Some (_,output') ->
       (* the carrier of the relation output' can be a Prod ==>
          we must uncurry on the fly output.
          E.g: A -> B -> C vs        A -> (B -> C)
                args   output     args     output
       *)
       let rel = find_relation_class output' in
       let rel_a,rel_quantifiers_no =
        match rel with
           Relation rel -> rel.rel_a, rel.rel_quantifiers_no
         | Leibniz (Some t) -> t, 0
         | Leibniz None -> assert false in
       let rel_a_n =
        clos_norm_flags Closure.betaiotazeta empty_env Evd.empty rel_a in
       try
        let _,output_rel_a_n = decompose_lam_n rel_quantifiers_no rel_a_n in
        let argsrev,_ = decompose_prod output_rel_a_n in
        let n = List.length argsrev in
        let argsrev',_ = decompose_prod typ in
        let m = List.length argsrev' in
         decompose_prod_n (m - n) typ
       with UserError(_,_) ->
        (* decompose_lam_n failed. This may happen when rel_a is an axiom,
           a constructor, an inductive type, etc. *)
        decompose_prod typ
  in
  let args_ty = List.rev argsrev in
  let args_ty_len = List.length (args_ty) in
  let args_ty_quantifiers_rev,args,args_instance,output,output_instance =
   match signature with
      None ->
       if args_ty = [] then
        raise (ProofEngineTypes.Fail (lazy
         ("The term " ^ CicPp.ppterm m ^ " has type " ^
          CicPp.ppterm typeofm ^ " that is not a product."))) ;
       ignore (check_is_dependent 0 args_ty output) ;
       let args =
        List.map
         (fun (_,ty) -> None,default_relation_for_carrier ty) args_ty in
       let output = default_relation_for_carrier output in
        [],args,args,output,output
    | Some (args,output') ->
       assert (args <> []);
       let number_of_arguments = List.length args in
       let number_of_quantifiers = args_ty_len - number_of_arguments in
       if number_of_quantifiers < 0 then
        raise (ProofEngineTypes.Fail (lazy
         ("The morphism " ^ CicPp.ppterm m ^ " has type " ^
          CicPp.ppterm typeofm ^ " that attends at most " ^ int args_ty_len ^
          " arguments. The signature that you specified requires " ^
          int number_of_arguments ^ " arguments.")))
       else
        begin
         (* the real_args_ty returned are already delifted *)
         let args_ty_quantifiers_rev, real_args_ty, real_output =
          check_is_dependent number_of_quantifiers args_ty output in
         let quantifiers_rel_context =
          List.map (fun (n,t) -> n,None,t) args_ty_quantifiers_rev in
         let env = push_rel_context quantifiers_rel_context env in
         let find_relation_class t real_t =
          try
           let rel = find_relation_class t in
            rel, unify_relation_class_carrier_with_type env rel real_t
          with Not_found ->
           raise (ProofEngineTypes.Fail (lazy
            ("Not a valid signature: " ^ CicPp.ppterm t ^
             " is neither a registered relation nor the Leibniz " ^
             " equality.")))
         in
         let find_relation_class_v (variance,t) real_t =
          let relation,relation_instance = find_relation_class t real_t in
           match relation, variance with
              Leibniz _, None
            | Relation {rel_sym = Some _}, None
            | Relation {rel_sym = None}, Some _ ->
               (variance, relation), (variance, relation_instance)
            | Relation {rel_sym = None},None ->
               raise (ProofEngineTypes.Fail (lazy
                ("You must specify the variance in each argument " ^
                 "whose relation is asymmetric.")))
            | Leibniz _, Some _
            | Relation {rel_sym = Some _}, Some _ ->
               raise (ProofEngineTypes.Fail (lazy
                ("You cannot specify the variance of an argument " ^
                 "whose relation is symmetric.")))
         in
          let args, args_instance =
           List.split
            (List.map2 find_relation_class_v args real_args_ty) in
          let output,output_instance= find_relation_class output' real_output in
           args_ty_quantifiers_rev, args, args_instance, output, output_instance
        end
  in
   let argsconstr,outputconstr,lem =
    gen_compat_lemma_statement args_ty_quantifiers_rev output_instance
     args_instance (apply_to_rels m args_ty_quantifiers_rev) in
   (* "unfold make_compatibility_goal" *)
   let lem =
    Reductionops.clos_norm_flags
     (Closure.unfold_red (coq_make_compatibility_goal_eval_ref))
     env Evd.empty lem in
   (* "unfold make_compatibility_goal_aux" *)
   let lem =
    Reductionops.clos_norm_flags
     (Closure.unfold_red(coq_make_compatibility_goal_aux_eval_ref))
     env Evd.empty lem in
   (* "simpl" *)
   let lem = Tacred.nf env Evd.empty lem in
    if Lib.is_modtype () then
     begin
      ignore
       (Declare.declare_internal_constant id
        (ParameterEntry lem, IsAssumption Logical)) ;
      let mor_name = morphism_theory_id_of_morphism_proof_id id in
      let lemma_infos = Some (id,argsconstr,outputconstr) in
       add_morphism lemma_infos mor_name
        (m,args_ty_quantifiers_rev,args,output)
     end
    else
     begin
      new_edited id
       (m,args_ty_quantifiers_rev,args,argsconstr,output,outputconstr);
      Pfedit.start_proof id (Global, Proof Lemma) 
       (Declare.clear_proofs (Global.named_context ()))
       lem hook;
      Options.if_verbose msg (Printer.pr_open_subgoals ());
     end
*) assert false

let morphism_hook _ ref =
(*COQ
  let pf_id = id_of_global ref in
  let mor_id = morphism_theory_id_of_morphism_proof_id pf_id in
  let (m,quantifiers_rev,args,argsconstr,output,outputconstr) =
   what_edited pf_id in
  if (is_edited pf_id)
  then 
   begin
    add_morphism (Some (pf_id,argsconstr,outputconstr)) mor_id
     (m,quantifiers_rev,args,output) ;
    no_more_edited pf_id
   end
*) assert false

type morphism_signature =
 (bool option * Cic.term) list * Cic.term

let new_named_morphism id m sign =
 new_morphism m sign id morphism_hook

(************************** Adding a relation to the database *********************)

let check_a a =
(*COQ
 let typ = Typing.type_of env Evd.empty a in
 let a_quantifiers_rev,_ = Reduction.dest_arity env typ in
  a_quantifiers_rev
*) assert false

let check_eq a_quantifiers_rev a aeq =
(*COQ
 let typ =
  Sign.it_mkProd_or_LetIn
   (Cic.Appl [coq_relation ; apply_to_rels a a_quantifiers_rev])
   a_quantifiers_rev in
 if
  not
   (is_conv env Evd.empty (Typing.type_of env Evd.empty aeq) typ)
 then
  raise (ProofEngineTypes.Fail (lazy
   (CicPp.ppterm aeq ^ " should have type (" ^ CicPp.ppterm typ ^ ")")))
*) (assert false : unit)

let check_property a_quantifiers_rev a aeq strprop coq_prop t =
(*COQ
 if
  not
   (is_conv env Evd.empty (Typing.type_of env Evd.empty t)
    (Sign.it_mkProd_or_LetIn
     (Cic.Appl
       [coq_prop ;
        apply_to_rels a a_quantifiers_rev ;
        apply_to_rels aeq a_quantifiers_rev]) a_quantifiers_rev))
 then
  raise (ProofEngineTypes.Fail (lazy
   ("Not a valid proof of " ^ strprop ^ ".")))
*) assert false

let check_refl a_quantifiers_rev a aeq refl =
 check_property a_quantifiers_rev a aeq "reflexivity" coq_reflexive refl

let check_sym a_quantifiers_rev a aeq sym =
 check_property a_quantifiers_rev a aeq "symmetry" coq_symmetric sym

let check_trans a_quantifiers_rev a aeq trans =
 check_property a_quantifiers_rev a aeq "transitivity" coq_transitive trans
;;

let int_add_relation id a aeq refl sym trans =
(*COQ
 let env = Global.env () in
*)
 let a_quantifiers_rev = check_a a in
  check_eq a_quantifiers_rev a aeq  ;
  HExtlib.iter_option (check_refl a_quantifiers_rev a aeq) refl ;
  HExtlib.iter_option (check_sym a_quantifiers_rev a aeq) sym ;
  HExtlib.iter_option (check_trans a_quantifiers_rev a aeq) trans ;
  let quantifiers_no = List.length a_quantifiers_rev in
  let aeq_rel =
   { rel_a = a;
     rel_aeq = aeq;
     rel_refl = refl;
     rel_sym = sym;
     rel_trans = trans;
     rel_quantifiers_no = quantifiers_no;
     rel_X_relation_class = Cic.Sort Cic.Prop; (* dummy value, overwritten below *)
     rel_Xreflexive_relation_class = Cic.Sort Cic.Prop (* dummy value, overwritten below *)
   } in
  let _x_relation_class =
   let subst =
    let len = List.length a_quantifiers_rev in
     list_map_i (fun i _ -> Cic.Rel (len - i + 2)) 0 a_quantifiers_rev in
   cic_relation_class_of_X_relation
    (Cic.Rel 2) (Cic.Rel 1) (apply_to_relation subst aeq_rel) in
  let _ =
(*COQ
   Declare.declare_internal_constant id
    (DefinitionEntry
      {const_entry_body =
        Sign.it_mkLambda_or_LetIn x_relation_class
         ([ Name "v",None,Cic.Rel 1;
            Name "X",None,Cic.Sort (Cic.Type (CicUniv.fresh ()))] @
            a_quantifiers_rev);
       const_entry_type = None;
       const_entry_opaque = false;
       const_entry_boxed = Options.boxed_definitions()},
      IsDefinition Definition) in
*) () in
  let id_precise = id ^ "_precise_relation_class" in
  let _xreflexive_relation_class =
   let subst =
    let len = List.length a_quantifiers_rev in
     list_map_i (fun i _ -> Cic.Rel (len - i)) 0 a_quantifiers_rev
   in
    cic_precise_relation_class_of_relation (apply_to_relation subst aeq_rel) in
  let _ =
(*COQ
   Declare.declare_internal_constant id_precise
    (DefinitionEntry
      {const_entry_body =
        Sign.it_mkLambda_or_LetIn xreflexive_relation_class a_quantifiers_rev;
       const_entry_type = None;
       const_entry_opaque = false;
       const_entry_boxed = Options.boxed_definitions() },
      IsDefinition Definition) in
*) () in
  let aeq_rel =
   { aeq_rel with
      rel_X_relation_class = current_constant id;
      rel_Xreflexive_relation_class = current_constant id_precise } in
  relation_to_obj (aeq, aeq_rel) ;
  prerr_endline (CicPp.ppterm aeq ^ " is registered as a relation");
  match trans with
     None -> ()
   | Some trans ->
      let mor_name = id ^ "_morphism" in
      let a_instance = apply_to_rels a a_quantifiers_rev in
      let aeq_instance = apply_to_rels aeq a_quantifiers_rev in
      let sym_instance =
       HExtlib.map_option (fun x -> apply_to_rels x a_quantifiers_rev) sym in
      let refl_instance =
       HExtlib.map_option (fun x -> apply_to_rels x a_quantifiers_rev) refl in
      let trans_instance = apply_to_rels trans a_quantifiers_rev in
      let aeq_rel_class_and_var1, aeq_rel_class_and_var2, lemma, output =
       match sym_instance, refl_instance with
          None, None ->
           (Some false, Relation aeq_rel),
           (Some true, Relation aeq_rel),
            Cic.Appl
             [coq_equality_morphism_of_asymmetric_areflexive_transitive_relation;
              a_instance ; aeq_instance ; trans_instance],
            coq_impl_relation
        | None, Some refl_instance ->
           (Some false, Relation aeq_rel),
           (Some true, Relation aeq_rel),
            Cic.Appl
             [coq_equality_morphism_of_asymmetric_reflexive_transitive_relation;
              a_instance ; aeq_instance ; refl_instance ; trans_instance],
            coq_impl_relation
        | Some sym_instance, None ->
           (None, Relation aeq_rel),
           (None, Relation aeq_rel),
            Cic.Appl
             [coq_equality_morphism_of_symmetric_areflexive_transitive_relation;
              a_instance ; aeq_instance ; sym_instance ; trans_instance],
            coq_iff_relation
        | Some sym_instance, Some refl_instance ->
           (None, Relation aeq_rel),
           (None, Relation aeq_rel),
            Cic.Appl
             [coq_equality_morphism_of_symmetric_reflexive_transitive_relation;
              a_instance ; aeq_instance ; refl_instance ; sym_instance ;
              trans_instance],
            coq_iff_relation in
      let _ =
(*COQ
       Declare.declare_internal_constant mor_name
        (DefinitionEntry
          {const_entry_body = Sign.it_mkLambda_or_LetIn lemma a_quantifiers_rev;
           const_entry_type = None;
           const_entry_opaque = false;
          const_entry_boxed = Options.boxed_definitions()},
          IsDefinition Definition)
*) ()
      in
       let a_quantifiers_rev =
        List.map (fun (n,b,t) -> assert (b = None); n,t) a_quantifiers_rev in
       add_morphism None mor_name
        (aeq,a_quantifiers_rev,[aeq_rel_class_and_var1; aeq_rel_class_and_var2],
          output)

(* The vernac command "Add Relation ..." *)
let add_relation id a aeq refl sym trans =
 int_add_relation id a aeq refl sym trans

(****************************** The tactic itself *******************************)

type direction =
   Left2Right
 | Right2Left

let prdirection =
 function
    Left2Right -> "->"
  | Right2Left -> "<-"

type constr_with_marks =
  | MApp of Cic.term * morphism_class * constr_with_marks list * direction
  | ToReplace
  | ToKeep of Cic.term * relation relation_class * direction

let is_to_replace = function
 | ToKeep _ -> false
 | ToReplace -> true
 | MApp _ -> true

let get_mark a = 
  List.fold_left (||) false (List.map is_to_replace a)

let cic_direction_of_direction =
 function
    Left2Right -> coq_Left2Right
  | Right2Left -> coq_Right2Left

let opposite_direction =
 function
    Left2Right -> Right2Left
  | Right2Left -> Left2Right

let direction_of_constr_with_marks hole_direction =
 function
    MApp (_,_,_,dir) -> cic_direction_of_direction dir
  | ToReplace -> hole_direction
  | ToKeep (_,_,dir) -> cic_direction_of_direction dir

type argument =
   Toapply of Cic.term         (* apply the function to the argument *)
 | Toexpand of Cic.name * Cic.term  (* beta-expand the function w.r.t. an argument
                                of this type *)
let beta_expand c args_rev =
 let rec to_expand =
  function
     [] -> []
   | (Toapply _)::tl -> to_expand tl
   | (Toexpand (name,s))::tl -> (name,s)::(to_expand tl) in
 let rec aux n =
  function
     [] -> []
   | (Toapply arg)::tl -> arg::(aux n tl)
   | (Toexpand _)::tl -> (Cic.Rel n)::(aux (n + 1) tl)
 in
  compose_lambda (to_expand args_rev)
   (Cic.Appl (c :: List.rev (aux 1 args_rev)))

exception Optimize (* used to fall-back on the tactic for Leibniz equality *)

let rec list_sep_last = function
  | [] -> assert false
  | hd::[] -> (hd,[])
  | hd::tl -> let (l,tl) = list_sep_last tl in (l,hd::tl)

let relation_class_that_matches_a_constr caller_name new_goals hypt =
 let heq, hargs =
  match hypt with
     Cic.Appl (heq::hargs) -> heq,hargs
   | _ -> hypt,[]
 in
 let rec get_all_but_last_two =
  function
     []
   | [_] ->
      raise (ProofEngineTypes.Fail (lazy (CicPp.ppterm hypt ^
       " is not a registered relation.")))
   | [_;_] -> []
   | he::tl -> he::(get_all_but_last_two tl) in
 let all_aeq_args = get_all_but_last_two hargs in
 let rec find_relation l subst =
  let aeq = Cic.Appl (heq::l) in
  try
   let rel = find_relation_class aeq in
   match rel,new_goals with
      Leibniz _,[] ->
       assert (subst = []);
       raise Optimize (* let's optimize the proof term size *)
    | Leibniz (Some _), _ ->
       assert (subst = []);
       rel
    | Leibniz None, _ ->
       (* for well-typedness reasons it should have been catched by the
          previous guard in the previous iteration. *)
       assert false
    | Relation rel,_ -> Relation (apply_to_relation subst rel)
  with Not_found ->
   if l = [] then
    raise (ProofEngineTypes.Fail (lazy
     (CicPp.ppterm (Cic.Appl (aeq::all_aeq_args)) ^
      " is not a registered relation.")))
   else
    let last,others = list_sep_last l in
    find_relation others (last::subst)
 in
  find_relation all_aeq_args []

(* rel1 is a subrelation of rel2 whenever 
    forall x1 x2, rel1 x1 x2 -> rel2 x1 x2
   The Coq part of the tactic, however, needs rel1 == rel2.
   Hence the third case commented out.
   Note: accepting user-defined subtrelations seems to be the last
   useful generalization that does not go against the original spirit of
   the tactic.
*)
let subrelation gl rel1 rel2 =
 match rel1,rel2 with
    Relation {rel_aeq=rel_aeq1}, Relation {rel_aeq=rel_aeq2} ->
     (*COQ Tacmach.pf_conv_x gl rel_aeq1 rel_aeq2*) assert false
  | Leibniz (Some t1), Leibniz (Some t2) ->
     (*COQ Tacmach.pf_conv_x gl t1 t2*) assert false
  | Leibniz None, _
  | _, Leibniz None -> assert false
(* This is the commented out case (see comment above)
  | Leibniz (Some t1), Relation {rel_a=t2; rel_refl = Some _} ->
     Tacmach.pf_conv_x gl t1 t2
*)
  | _,_ -> false

(* this function returns the list of new goals opened by a constr_with_marks *)
let rec collect_new_goals =
 function
   MApp (_,_,a,_) -> List.concat (List.map collect_new_goals a)
 | ToReplace
 | ToKeep (_,Leibniz _,_)
 | ToKeep (_,Relation {rel_refl=Some _},_) -> []
 | ToKeep (c,Relation {rel_aeq=aeq; rel_refl=None},_) -> [Cic.Appl[aeq;c;c]]

(* two marked_constr are equivalent if they produce the same set of new goals *)
let marked_constr_equiv_or_more_complex to_marked_constr gl c1 c2 =
  let glc1 = collect_new_goals (to_marked_constr c1) in
  let glc2 = collect_new_goals (to_marked_constr c2) in
   List.for_all (fun c -> List.exists (fun c' -> (*COQ pf_conv_x gl c c'*) assert false) glc1) glc2

let pr_new_goals i c =
 let glc = collect_new_goals c in
  " " ^ string_of_int i ^ ") side conditions:" ^
   (if glc = [] then " no side conditions"
    else
     ("\n   " ^
       String.concat "\n   "
        (List.map (fun c -> " ... |- " ^ CicPp.ppterm c) glc)))

(* given a list of constr_with_marks, it returns the list where
   constr_with_marks than open more goals than simpler ones in the list
   are got rid of *)
let elim_duplicates gl to_marked_constr =
 let rec aux =
  function
     [] -> []
   | he:: tl ->
      if List.exists
          (marked_constr_equiv_or_more_complex to_marked_constr gl he) tl
      then aux tl
      else he::aux tl
 in
  aux

let filter_superset_of_new_goals gl new_goals l =
 List.filter
  (fun (_,_,c) ->
    List.for_all
     (fun g -> List.exists ((*COQ pf_conv_x gl g*)assert false) (collect_new_goals c)) new_goals) l

(* given the list of lists [ l1 ; ... ; ln ] it returns the list of lists
   [ c1 ; ... ; cn ] that is the cartesian product of the sets l1, ..., ln *)
let cartesian_product gl a =
 let rec aux =
  function
     [] -> assert false
   | [he] -> List.map (fun e -> [e]) he
   | he::tl ->
      let tl' = aux tl in
       List.flatten
        (List.map (function e -> List.map (function l -> e :: l) tl') he)
 in
  aux (List.map (elim_duplicates gl (fun x -> x)) a)

let does_not_occur n t = assert false

let mark_occur gl ~new_goals t in_c input_relation input_direction =
 let rec aux output_relation output_direction in_c =
  if t = in_c then
   if input_direction = output_direction
   && subrelation gl input_relation output_relation then
    [ToReplace]
   else []
  else
    match in_c with
      | Cic.Appl (c::al) -> 
         let mors_and_cs_and_als =
          let mors_and_cs_and_als =
           let morphism_table_find c =
            try morphism_table_find c with Not_found -> [] in
           let rec aux acc =
            function
               [] ->
                let c' = Cic.Appl (c::acc) in
                let al' = [] in
                List.map (fun m -> m,c',al') (morphism_table_find c')
             | (he::tl) as l ->
                let c' = Cic.Appl (c::acc) in
                let acc' = acc @ [he] in
                 (List.map (fun m -> m,c',l) (morphism_table_find c')) @
                  (aux acc' tl)
           in
            aux [] al in
          let mors_and_cs_and_als =
           List.map
            (function (m,c,al) ->
              relation_morphism_of_constr_morphism m, c, al)
             mors_and_cs_and_als in
          let mors_and_cs_and_als =
           List.fold_left
            (fun l (m,c,al) ->
	       try (unify_morphism_with_arguments gl (c,al) m t) :: l
	       with Impossible -> l
	    ) [] mors_and_cs_and_als
          in
           List.filter
            (fun (mor,_,_) -> subrelation gl mor.output output_relation)
            mors_and_cs_and_als
         in
          (* First we look for well typed morphisms *)
          let res_mors =
           List.fold_left
            (fun res (mor,c,al) ->
              let a =
               let arguments = mor.args in
               let apply_variance_to_direction default_dir =
                function
                   None -> default_dir
                 | Some true -> output_direction
                 | Some false -> opposite_direction output_direction
               in
                List.map2
                 (fun a (variance,relation) ->
                   (aux relation
                     (apply_variance_to_direction Left2Right variance) a) @
                   (aux relation
                     (apply_variance_to_direction Right2Left variance) a)
                 ) al arguments
              in
               let a' = cartesian_product gl a in
                (List.map
                  (function a ->
                    if not (get_mark a) then
                     ToKeep (in_c,output_relation,output_direction)
                    else
                     MApp (c,ACMorphism mor,a,output_direction)) a') @ res
            ) [] mors_and_cs_and_als in
          (* Then we look for well typed functions *)
          let res_functions =
           (* the tactic works only if the function type is
               made of non-dependent products only. However, here we
               can cheat a bit by partially istantiating c to match
               the requirement when the arguments to be replaced are
               bound by non-dependent products only. *)
            let typeofc = (*COQ Tacmach.pf_type_of gl c*) assert false in
            let typ = (*COQ nf_betaiota typeofc*) let _ = typeofc in assert false in
            let rec find_non_dependent_function context c c_args_rev typ
             f_args_rev a_rev
            =
             function
                [] ->
                 if a_rev = [] then
                  [ToKeep (in_c,output_relation,output_direction)]
                 else
                  let a' =
                   cartesian_product gl (List.rev a_rev)
                  in
                   List.fold_left
                    (fun res a ->
                      if not (get_mark a) then
                       (ToKeep (in_c,output_relation,output_direction))::res
                      else
                       let err =
                        match output_relation with
                           Leibniz (Some typ') when (*COQ pf_conv_x gl typ typ'*) assert false ->
                            false
                         | Leibniz None -> assert false
                         | _ when output_relation = coq_iff_relation
                             -> false
                         | _ -> true
                       in
                        if err then res
                        else
                         let mor =
                          ACFunction{f_args=List.rev f_args_rev;f_output=typ} in
                         let func = beta_expand c c_args_rev in
                          (MApp (func,mor,a,output_direction))::res
                    ) [] a'
              | (he::tl) as a->
                 let typnf = (*COQ Reduction.whd_betadeltaiota env typ*) assert false in
                  match typnf with
                    Cic.Cast (typ,_) ->
                     find_non_dependent_function context c c_args_rev typ
                      f_args_rev a_rev a
                  | Cic.Prod (name,s,t) ->
                     let context' = Some (name, Cic.Decl s)::context in
                     let he =
                      (aux (Leibniz (Some s)) Left2Right he) @
                      (aux (Leibniz (Some s)) Right2Left he) in
                     if he = [] then []
                     else
                      let he0 = List.hd he in
                      begin
                       match does_not_occur 1 t, he0 with
                          _, ToKeep (arg,_,_) ->
                           (* invariant: if he0 = ToKeep (t,_,_) then every
                              element in he is = ToKeep (t,_,_) *)
                           assert
                            (List.for_all
                              (function
                                  ToKeep(arg',_,_) when (*COQpf_conv_x gl arg arg'*) assert false ->
                                    true
                                | _ -> false) he) ;
                           (* generic product, to keep *)
                           find_non_dependent_function
                            context' c ((Toapply arg)::c_args_rev)
                            (CicSubstitution.subst arg t) f_args_rev a_rev tl
                        | true, _ ->
                           (* non-dependent product, to replace *)
                           find_non_dependent_function
                            context' c ((Toexpand (name,s))::c_args_rev)
                             (CicSubstitution.lift 1 t) (s::f_args_rev) (he::a_rev) tl
                        | false, _ ->
                           (* dependent product, to replace *)
                           (* This limitation is due to the reflexive
                             implementation and it is hard to lift *)
                           raise (ProofEngineTypes.Fail (lazy
                            ("Cannot rewrite in the argument of a " ^
                             "dependent product. If you need this " ^
                             "feature, please report to the author.")))
                      end
                  | _ -> assert false
            in
             find_non_dependent_function (*COQ (Tacmach.pf_env gl) ci vuole il contesto*)(assert false) c [] typ [] []
              al
          in
           elim_duplicates gl (fun x -> x) (res_functions @ res_mors)
      | Cic.Prod (_, c1, c2) -> 
          if (*COQ (dependent (Cic.Rel 1) c2)*) assert false
          then
           raise (ProofEngineTypes.Fail (lazy
            ("Cannot rewrite in the type of a variable bound " ^
             "in a dependent product.")))
          else 
           let typeofc1 = (*COQ Tacmach.pf_type_of gl c1*) assert false in
            if not (*COQ (Tacmach.pf_conv_x gl typeofc1 (Cic.Sort Cic.Prop))*) (assert false) then
             (* to avoid this error we should introduce an impl relation
                whose first argument is Type instead of Prop. However,
                the type of the new impl would be Type -> Prop -> Prop
                that is no longer a Relation_Definitions.relation. Thus
                the Coq part of the tactic should be heavily modified. *)
             raise (ProofEngineTypes.Fail (lazy
              ("Rewriting in a product A -> B is possible only when A " ^
               "is a proposition (i.e. A is of type Prop). The type " ^
               CicPp.ppterm c1 ^ " has type " ^ CicPp.ppterm typeofc1 ^
               " that is not convertible to Prop.")))
            else
             aux output_relation output_direction
              (Cic.Appl [coq_impl; c1 ; CicSubstitution.subst (Cic.Rel 1 (*dummy*)) c2])
      | _ ->
        if (*COQ occur_term t in_c*) assert false then
         raise (ProofEngineTypes.Fail (lazy
          ("Trying to replace " ^ CicPp.ppterm t ^ " in " ^ CicPp.ppterm in_c ^
           " that is not an applicative context.")))
        else
         [ToKeep (in_c,output_relation,output_direction)]
 in
  let aux2 output_relation output_direction =
   List.map
    (fun res -> output_relation,output_direction,res)
     (aux output_relation output_direction in_c) in
  let res =
   (aux2 coq_iff_relation Right2Left) @
   (* This is the case of a proposition of signature A ++> iff or B --> iff *)
   (aux2 coq_iff_relation Left2Right) @
   (aux2 coq_impl_relation Right2Left) in
  let res = elim_duplicates gl (function (_,_,t) -> t) res in
  let res' = filter_superset_of_new_goals gl new_goals res in
  match res' with
     [] when res = [] ->
      raise (ProofEngineTypes.Fail (lazy
       ("Either the term " ^ CicPp.ppterm t ^ " that must be " ^
        "rewritten occurs in a covariant position or the goal is not " ^
        "made of morphism applications only. You can replace only " ^
        "occurrences that are in a contravariant position and such that " ^
        "the context obtained by abstracting them is made of morphism " ^
        "applications only.")))
   | [] ->
      raise (ProofEngineTypes.Fail (lazy
       ("No generated set of side conditions is a superset of those " ^
        "requested by the user. The generated sets of side conditions " ^
        "are:\n" ^
         prlist_with_sepi "\n"
          (fun i (_,_,mc) -> pr_new_goals i mc) res)))
   | [he] -> he
   | he::_ ->
      prerr_endline
       ("Warning: The application of the tactic is subject to one of " ^
        "the \nfollowing set of side conditions that the user needs " ^
        "to prove:\n" ^
         prlist_with_sepi "\n"
          (fun i (_,_,mc) -> pr_new_goals i mc) res' ^
         "\nThe first set is randomly chosen. Use the syntax " ^
         "\"setoid_rewrite ... generate side conditions ...\" to choose " ^
         "a different set.") ;
      he

let cic_morphism_context_list_of_list hole_relation hole_direction out_direction
=
 let check =
  function
     (None,dir,dir') -> 
      Cic.Appl [coq_MSNone ; dir ; dir']
   | (Some true,dir,dir') ->
      assert (dir = dir');
      Cic.Appl [coq_MSCovariant ; dir]
   | (Some false,dir,dir') ->
      assert (dir <> dir');
      Cic.Appl [coq_MSContravariant ; dir] in
 let rec aux =
  function
     [] -> assert false
   | [(variance,out),(value,direction)] ->
      Cic.Appl [coq_singl ; coq_Argument_Class ; out],
      Cic.Appl 
       [coq_fcl_singl;
        hole_relation; hole_direction ; out ;
        direction ; out_direction ;
        check (variance,direction,out_direction) ; value]
   | ((variance,out),(value,direction))::tl ->
      let outtl, valuetl = aux tl in
       Cic.Appl
        [coq_cons; coq_Argument_Class ; out ; outtl],
       Cic.Appl
        [coq_fcl_cons;
         hole_relation ; hole_direction ; out ; outtl ;
         direction ; out_direction ;
         check (variance,direction,out_direction) ;
         value ; valuetl]
 in aux

let rec cic_type_nelist_of_list =
 function
    [] -> assert false
  | [value] ->
      Cic.Appl [coq_singl; Cic.Sort (Cic.Type (CicUniv.fresh ())) ; value]
  | value::tl ->
     Cic.Appl
      [coq_cons; Cic.Sort (Cic.Type (CicUniv.fresh ())); value;
       cic_type_nelist_of_list tl]

let syntactic_but_representation_of_marked_but hole_relation hole_direction =
 let rec aux out (rel_out,precise_out,is_reflexive) =
  function
     MApp (f, m, args, direction) ->
      let direction = cic_direction_of_direction direction in
      let morphism_theory, relations =
       match m with
          ACMorphism { args = args ; morphism_theory = morphism_theory } ->
           morphism_theory,args
        | ACFunction { f_args = f_args ; f_output = f_output } ->
           let mt =
            if (*COQ eq_constr out (cic_relation_class_of_relation_class
              coq_iff_relation)*) assert false
            then
              Cic.Appl
               [coq_morphism_theory_of_predicate;
                cic_type_nelist_of_list f_args; f]
            else
              Cic.Appl
               [coq_morphism_theory_of_function;
                cic_type_nelist_of_list f_args; f_output; f]
           in
            mt,List.map (fun x -> None,Leibniz (Some x)) f_args in
      let cic_relations =
       List.map
        (fun (variance,r) ->
          variance,
          r,
          cic_relation_class_of_relation_class r,
          cic_precise_relation_class_of_relation_class r
        ) relations in
      let cic_args_relations,argst =
       cic_morphism_context_list_of_list hole_relation hole_direction direction
        (List.map2
         (fun (variance,trel,t,precise_t) v ->
           (variance,cic_argument_class_of_argument_class (variance,trel)),
             (aux t precise_t v,
               direction_of_constr_with_marks hole_direction v)
         ) cic_relations args)
      in
       Cic.Appl
        [coq_App;
         hole_relation ; hole_direction ;
         cic_args_relations ; out ; direction ;
         morphism_theory ; argst]
   | ToReplace ->
      Cic.Appl [coq_ToReplace ; hole_relation ; hole_direction]
   | ToKeep (c,_,direction) ->
      let direction = cic_direction_of_direction direction in
       if is_reflexive then
        Cic.Appl
         [coq_ToKeep ; hole_relation ; hole_direction ; precise_out ;
          direction ; c]
       else
        let c_is_proper =
         let typ = Cic.Appl [rel_out ; c ; c] in
          Cic.Cast ((*COQ Evarutil.mk_new_meta ()*)assert false, typ)
        in
         Cic.Appl
          [coq_ProperElementToKeep ;
           hole_relation ; hole_direction; precise_out ;
           direction; c ; c_is_proper]
 in aux

let apply_coq_setoid_rewrite hole_relation prop_relation c1 c2 (direction,h)
 prop_direction m
=
 let hole_relation = cic_relation_class_of_relation_class hole_relation in
 let hyp,hole_direction = h,cic_direction_of_direction direction in
 let cic_prop_relation = cic_relation_class_of_relation_class prop_relation in
 let precise_prop_relation =
  cic_precise_relation_class_of_relation_class prop_relation
 in
  Cic.Appl
   [coq_setoid_rewrite;
    hole_relation ; hole_direction ; cic_prop_relation ;
    prop_direction ; c1 ; c2 ;
    syntactic_but_representation_of_marked_but hole_relation hole_direction
    cic_prop_relation precise_prop_relation m ; hyp]

(*COQ
let check_evar_map_of_evars_defs evd =
 let metas = Evd.meta_list evd in
 let check_freemetas_is_empty rebus =
  Evd.Metaset.iter
   (fun m ->
     if Evd.meta_defined evd m then () else
      raise (Logic.RefinerError (Logic.OccurMetaGoal rebus)))
 in
  List.iter
   (fun (_,binding) ->
     match binding with
        Evd.Cltyp (_,{Evd.rebus=rebus; Evd.freemetas=freemetas}) ->
         check_freemetas_is_empty rebus freemetas
      | Evd.Clval (_,{Evd.rebus=rebus1; Evd.freemetas=freemetas1},
                 {Evd.rebus=rebus2; Evd.freemetas=freemetas2}) ->
         check_freemetas_is_empty rebus1 freemetas1 ;
         check_freemetas_is_empty rebus2 freemetas2
   ) metas
*)

(* For a correct meta-aware "rewrite in", we split unification 
   apart from the actual rewriting (Pierre L, 05/04/06) *)
   
(* [unification_rewrite] searchs a match for [c1] in [but] and then 
   returns the modified objects (in particular [c1] and [c2]) *)  

let unification_rewrite c1 c2 cl but gl = 
(*COQ
  let (env',c1) =
    try
      (* ~mod_delta:false to allow to mark occurences that must not be
         rewritten simply by replacing them with let-defined definitions
         in the context *)
      w_unify_to_subterm ~mod_delta:false (pf_env gl) (c1,but) cl.env
    with
	Pretype_errors.PretypeError _ ->
	  (* ~mod_delta:true to make Ring work (since it really
             exploits conversion) *)
	  w_unify_to_subterm ~mod_delta:true (pf_env gl) (c1,but) cl.env
  in
  let cl' = {cl with env = env' } in
  let c2 = Clenv.clenv_nf_meta cl' c2 in
  check_evar_map_of_evars_defs env' ;
  env',Clenv.clenv_value cl', c1, c2
*) assert false

(* no unification is performed in this function. [sigma] is the 
 substitution obtained from an earlier unification. *)

let relation_rewrite_no_unif c1 c2 hyp ~new_goals sigma gl = 
  let but = (*COQ pf_concl gl*) assert false in 
  try
   let input_relation =
    relation_class_that_matches_a_constr "Setoid_rewrite"
     new_goals ((*COQTyping.mtype_of (pf_env gl) sigma (snd hyp)*) assert false) in
   let output_relation,output_direction,marked_but =
    mark_occur gl ~new_goals c1 but input_relation (fst hyp) in
   let cic_output_direction = cic_direction_of_direction output_direction in
   let if_output_relation_is_iff gl =
    let th =
     apply_coq_setoid_rewrite input_relation output_relation c1 c2 hyp
      cic_output_direction marked_but
    in
     let new_but = (*COQ Termops.replace_term c1 c2 but*) assert false in
     let hyp1,hyp2,proj =
      match output_direction with
         Right2Left -> new_but, but, coq_proj1
       | Left2Right -> but, new_but, coq_proj2
     in
     let impl1 = Cic.Prod (Cic.Anonymous, hyp2, CicSubstitution.lift 1 hyp1) in
     let impl2 = Cic.Prod (Cic.Anonymous, hyp1, CicSubstitution.lift 1 hyp2) in
      let th' = Cic.Appl [proj; impl2; impl1; th] in
       (*COQ Tactics.refine
        (Cic.Appl [th'; mkCast (Evarutil.mk_new_meta(), DEFAULTcast, new_but)])
	gl*) let _ = th' in assert false in
   let if_output_relation_is_if gl =
    let th =
     apply_coq_setoid_rewrite input_relation output_relation c1 c2 hyp
      cic_output_direction marked_but
    in
     let new_but = (*COQ Termops.replace_term c1 c2 but*) assert false in
      (*COQ Tactics.refine
       (Cic.Appl [th ; mkCast (Evarutil.mk_new_meta(), DEFAULTcast, new_but)])
       gl*) let _ = new_but,th in assert false in
   if output_relation = coq_iff_relation then
     if_output_relation_is_iff gl
   else
     if_output_relation_is_if gl
  with
    Optimize ->
      (*COQ !general_rewrite (fst hyp = Left2Right) (snd hyp) gl*) assert false

let relation_rewrite c1 c2 (input_direction,cl) ~new_goals gl =
 let (sigma,cl,c1,c2) = unification_rewrite c1 c2 cl ((*COQ pf_concl gl*) assert false) gl in 
 relation_rewrite_no_unif c1 c2 (input_direction,cl) ~new_goals sigma gl 

let analyse_hypothesis gl c =
 let ctype = (*COQ pf_type_of gl c*) assert false in
 let eqclause  = (*COQ Clenv.make_clenv_binding gl (c,ctype) Rawterm.NoBindings*) let _ = ctype in assert false in
 let (equiv, args) = (*COQ decompose_app (Clenv.clenv_type eqclause)*) assert false in
 let rec split_last_two = function
   | [c1;c2] -> [],(c1, c2)
   | x::y::z ->
      let l,res = split_last_two (y::z) in x::l, res
   | _ -> raise (ProofEngineTypes.Fail (lazy "The term provided is not an equivalence")) in
 let others,(c1,c2) = split_last_two args in
  eqclause,Cic.Appl (equiv::others),c1,c2

let general_s_rewrite lft2rgt c ~new_goals (*COQgl*) =
(*COQ
  let eqclause,_,c1,c2 = analyse_hypothesis gl c in
  if lft2rgt then 
    relation_rewrite c1 c2 (Left2Right,eqclause) ~new_goals gl
  else 
    relation_rewrite c2 c1 (Right2Left,eqclause) ~new_goals gl
*) assert false

let relation_rewrite_in id c1 c2 (direction,eqclause) ~new_goals gl = 
 let hyp = (*COQ pf_type_of gl (mkVar id)*) assert false in
 (* first, we find a match for c1 in the hyp *)
 let (sigma,cl,c1,c2) = unification_rewrite c1 c2 eqclause hyp gl in 
 (* since we will actually rewrite in the opposite direction, we also need
    to replace every occurrence of c2 (resp. c1) in hyp with something that
    is convertible but not syntactically equal. To this aim we introduce a
    let-in and then we will use the intro tactic to get rid of it.
    Quite tricky to do properly since c1 can occur in c2 or vice-versa ! *)
 let mangled_new_hyp = 
   let hyp = CicSubstitution.lift 2 hyp in 
   (* first, we backup every occurences of c1 in newly allocated (Rel 1) *)
   let hyp = (*COQ Termops.replace_term (CicSubstitution.lift 2 c1) (Cic.Rel 1) hyp*) let _ = hyp in assert false in 
   (* then, we factorize every occurences of c2 into (Rel 2) *)
   let hyp = (*COQ Termops.replace_term (CicSubstitution.lift 2 c2) (Cic.Rel 2) hyp*) let _ = hyp in assert false in 
   (* Now we substitute (Rel 1) (i.e. c1) for c2 *)
   let hyp = CicSubstitution.subst (CicSubstitution.lift 1 c2) hyp in 
   (* Since CicSubstitution.subst has killed Rel 1 and decreased the other Rels, 
      Rel 1 is now coding for c2, we can build the let-in factorizing c2 *)
   Cic.LetIn (Cic.Anonymous,c2,assert false,hyp) 
 in 
 let new_hyp = (*COQ Termops.replace_term c1 c2 hyp*) assert false in 
 let oppdir = opposite_direction direction in 
(*COQ
 cut_replacing id new_hyp
   (tclTHENLAST
      (tclTHEN (change_in_concl None mangled_new_hyp)
         (tclTHEN intro
            (relation_rewrite_no_unif c2 c1 (oppdir,cl) ~new_goals sigma))))
   gl
*) let _ = oppdir,new_hyp,mangled_new_hyp in assert false

let general_s_rewrite_in id lft2rgt c ~new_goals (*COQgl*) =
(*COQ
  let eqclause,_,c1,c2 = analyse_hypothesis gl c in
  if lft2rgt then 
    relation_rewrite_in id c1 c2 (Left2Right,eqclause) ~new_goals gl
  else 
    relation_rewrite_in id c2 c1 (Right2Left,eqclause) ~new_goals gl
*) assert false

let setoid_replace relation c1 c2 ~new_goals (*COQgl*) =
 try
  let relation =
   match relation with
      Some rel ->
       (try
         match find_relation_class rel with
            Relation sa -> sa
          | Leibniz _ -> raise Optimize
        with
         Not_found ->
          raise (ProofEngineTypes.Fail (lazy
           (CicPp.ppterm rel ^ " is not a registered relation."))))
    | None ->
       match default_relation_for_carrier ((*COQ pf_type_of gl c1*) assert false) with
          Relation sa -> sa
        | Leibniz _ -> raise Optimize
  in
   let eq_left_to_right = Cic.Appl [relation.rel_aeq; c1 ; c2] in
   let eq_right_to_left = Cic.Appl [relation.rel_aeq; c2 ; c1] in
(*COQ
   let replace dir eq =
    tclTHENS (assert_tac false Cic.Anonymous eq)
      [onLastHyp (fun id ->
        tclTHEN
          (general_s_rewrite dir (mkVar id) ~new_goals)
          (clear [id]));
       Tacticals.tclIDTAC]
   in
    tclORELSE
     (replace true eq_left_to_right) (replace false eq_right_to_left) gl
*) let _ = eq_left_to_right,eq_right_to_left in assert false
 with
  Optimize -> (*COQ (!replace c1 c2) gl*) assert false

let setoid_replace_in id relation c1 c2 ~new_goals (*COQgl*) =
(*COQ
 let hyp = pf_type_of gl (mkVar id) in
 let new_hyp = Termops.replace_term c1 c2 hyp in
 cut_replacing id new_hyp
   (fun exact -> tclTHENLASTn
     (setoid_replace relation c2 c1 ~new_goals)
     [| exact; tclIDTAC |]) gl
*) assert false

(* [setoid_]{reflexivity,symmetry,transitivity} tactics *)

let setoid_reflexivity_tac =
 let tac ((proof,goal) as status) =
  let (_,metasenv,_subst,_,_, _) = proof in
  let metano,context,ty = CicUtil.lookup_meta goal metasenv in
   try
    let relation_class =
     relation_class_that_matches_a_constr "Setoid_reflexivity" [] ty in
    match relation_class with
       Leibniz _ -> assert false (* since [] is empty *)
     | Relation rel ->
        match rel.rel_refl with
           None ->
            raise (ProofEngineTypes.Fail (lazy
             ("The relation " ^ prrelation rel ^ " is not reflexive.")))
         | Some refl ->
            ProofEngineTypes.apply_tactic (PrimitiveTactics.apply_tac refl)
             status
   with
    Optimize ->
     ProofEngineTypes.apply_tactic EqualityTactics.reflexivity_tac status
 in
  ProofEngineTypes.mk_tactic tac

let setoid_reflexivity_tac =
   let start_tac = RT.whd_tac ~pattern:(PET.conclusion_pattern None) in
   let fail_tac = T.then_ ~start:start_tac ~continuation:setoid_reflexivity_tac in 
   T.if_ ~start:setoid_reflexivity_tac ~continuation:T.id_tac ~fail:fail_tac

let setoid_symmetry  =
 let tac status =
  try
   let relation_class =
    relation_class_that_matches_a_constr "Setoid_symmetry"
     [] ((*COQ pf_concl gl*) assert false) in
   match relation_class with
      Leibniz _ -> assert false (* since [] is empty *)
    | Relation rel ->
       match rel.rel_sym with
          None ->
           raise (ProofEngineTypes.Fail (lazy
            ("The relation " ^ prrelation rel ^ " is not symmetric.")))
        | Some sym -> (*COQ apply sym gl*) assert false
  with
   Optimize -> (*COQ symmetry gl*) assert false
 in
  ProofEngineTypes.mk_tactic tac

let setoid_symmetry_in id (*COQgl*) =
(*COQ
 let new_hyp =
  let _,he,c1,c2 = analyse_hypothesis gl (mkVar id) in
   Cic.Appl [he ; c2 ; c1]
 in
 cut_replacing id new_hyp (tclTHEN setoid_symmetry) gl
*) assert false

let setoid_transitivity c (*COQgl*) =
 try
  let relation_class =
   relation_class_that_matches_a_constr "Setoid_transitivity"
    [] ((*COQ pf_concl gl*) assert false) in
  match relation_class with
     Leibniz _ -> assert false (* since [] is empty *)
   | Relation rel ->
(*COQ
      let ctyp = pf_type_of gl c in
      let rel' = unify_relation_carrier_with_type (pf_env gl) rel ctyp in
       match rel'.rel_trans with
          None ->
           raise (ProofEngineTypes.Fail (lazy
            ("The relation " ^ prrelation rel ^ " is not transitive.")))
        | Some trans ->
           let transty = nf_betaiota (pf_type_of gl trans) in
           let argsrev, _ =
            Reductionops.decomp_n_prod (pf_env gl) Evd.empty 2 transty in
           let binder =
            match List.rev argsrev with
               _::(Name n2,None,_)::_ -> Rawterm.NamedHyp n2
             | _ -> assert false
           in
            apply_with_bindings
             (trans, Rawterm.ExplicitBindings [ dummy_loc, binder, c ]) gl
*) assert false
 with
  Optimize -> (*COQ transitivity c gl*) assert false
;;

(*COQ
Tactics.register_setoid_reflexivity setoid_reflexivity;;
Tactics.register_setoid_symmetry setoid_symmetry;;
Tactics.register_setoid_symmetry_in setoid_symmetry_in;;
Tactics.register_setoid_transitivity setoid_transitivity;;
*)
