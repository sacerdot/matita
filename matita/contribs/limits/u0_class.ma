(**************************************************************************)
(*       ___                                                              *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||         The HELM team.                                      *)
(*      ||A||         http://helm.cs.unibo.it                             *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU General Public License Version 2                  *)
(*                                                                        *)
(**************************************************************************)

include "notation/equiv_3.ma".
include "u0_preds.ma".
include "u0_apps.ma".

(* CLASS **************************************************************)
(* - a class is defined as a category in the sense of Per Martin-Lof 
   - a membership predicate defines the domain of the category
   - an equivalence relation on the domain defines equality in the category 
   - a function between classes is an application respecting
   -   both membership and equality
*)

record u0_class: Type[1] ≝ {
   u0_class_t :> Type[0];
   u0_class_in:  u0_predicate1 u0_class_t;
   u0_class_eq:  u0_predicate2 u0_class_t
}.

interpretation "u0 class membership" 'mem a D = (u0_class_in D a).

interpretation "u0 class equivalence" 'Equiv D a1 a2 = (u0_class_eq D a1 a2).

record is_u0_class (D:u0_class): Prop ≝ {
   u0_class_refl: u0_refl D (u0_class_in D) (u0_class_eq D);
   u0_class_repl: u0_repl2 D (u0_class_in D) (u0_class_eq D) (u0_class_eq D)
}.

record u0_fun (D,C:u0_class): Type[0] ≝ {
   u0_fun_a :1> D → C
}.

record is_u0_fun (D,C) (f:u0_fun D C): Prop ≝ {
   u0_fun_hom1: u0_hom1 D (u0_class_in D) C f (u0_class_in D) (u0_class_in C);
   u0_fun_hom2: u0_hom2 D (u0_class_in D) C f (u0_class_eq D) (u0_class_eq C)
}.

definition u0_id (D): u0_fun D D ≝
                 mk_u0_fun D D (u0_i D).

(* Basic properties ***************************************************)

(* auto width 7 in the next lemmas is due to automatic η expansion *)
lemma u0_class_sym: ∀D. is_u0_class D → u0_sym D (u0_class_in D) (u0_class_eq D).
#D #HD @u0_refl_repl_sym /2 width=7 by u0_class_repl, u0_class_refl/ qed-.

lemma u0_class_trans: ∀D. is_u0_class D → u0_trans D (u0_class_in D) (u0_class_eq D).
#D #HD @u0_refl_repl_trans /2 width=7 by u0_class_repl, u0_class_refl/ qed-.

lemma u0_class_conf: ∀D. is_u0_class D → u0_conf D (u0_class_in D) (u0_class_eq D).
#D #HD @u0_refl_repl_conf /2 width=7 by u0_class_repl, u0_class_refl/ qed-.

lemma u0_class_div: ∀D. is_u0_class D → u0_div D (u0_class_in D) (u0_class_eq D).
#D #HD @u0_refl_repl_div /2 width=7 by u0_class_repl, u0_class_refl/ qed-.

lemma u0_fun_id: ∀D. is_u0_class D → is_u0_fun D D (u0_id D).
/2 width=1 by mk_is_u0_fun/ qed.
