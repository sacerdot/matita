(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id: setoid_replace.mli 8779 2006-05-02 20:59:21Z letouzey $ i*)

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
   Relation of 'a    (* the [rel_aeq] of the relation or the relation*)
 | Leibniz of Cic.term option  (* the [carrier] (if [eq] is partially instantiated)*)

type 'a morphism =
    { args : (bool option * 'a relation_class) list;
      output : 'a relation_class;
      lem : Cic.term;
      morphism_theory : Cic.term
    }

type morphism_signature = (bool option * Cic.term) list * Cic.term

val register_replace : (Cic.term -> Cic.term -> ProofEngineTypes.tactic) -> unit
val register_general_rewrite : (bool -> Cic.term -> ProofEngineTypes.tactic) -> unit

val print_setoids : unit -> unit

val equiv_list : unit -> Cic.term list
val default_relation_for_carrier :
  ?filter:(relation -> bool) -> Cic.term -> relation relation_class 
(* [default_morphism] raises [Not_found] *)
val default_morphism :
  ?filter:(Cic.term morphism -> bool) -> Cic.term -> relation morphism

val setoid_replace :
 Cic.term option -> Cic.term -> Cic.term -> new_goals:Cic.term list -> ProofEngineTypes.tactic
val setoid_replace_in :
 string -> Cic.term option -> Cic.term -> Cic.term -> new_goals:Cic.term list ->
  ProofEngineTypes.tactic

val general_s_rewrite : bool -> Cic.term -> new_goals:Cic.term list -> ProofEngineTypes.tactic
val general_s_rewrite_in :
 string -> bool -> Cic.term -> new_goals:Cic.term list -> ProofEngineTypes.tactic

val setoid_reflexivity_tac : ProofEngineTypes.tactic
val setoid_symmetry : ProofEngineTypes.tactic
val setoid_symmetry_in : string -> ProofEngineTypes.tactic
val setoid_transitivity : Cic.term -> ProofEngineTypes.tactic

val add_relation :
 string -> Cic.term -> Cic.term -> Cic.term option ->
  Cic.term option -> Cic.term option -> unit

val new_named_morphism :
 string -> Cic.term -> morphism_signature option -> unit

val relation_table_find : Cic.term -> relation
val relation_table_mem : Cic.term -> bool
