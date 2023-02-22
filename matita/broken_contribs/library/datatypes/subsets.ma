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

include "logic/cprop_connectives.ma".
include "datatypes/categories.ma".

record powerset_carrier (A: setoid) : Type ≝ { mem_operator: A ⇒ CPROP }.

definition subseteq_operator ≝
 λA:setoid.λU,V.∀a:A. mem_operator ? U a → mem_operator ? V a.

theorem transitive_subseteq_operator: ∀A. transitive ? (subseteq_operator A).
 intros 6; intros 2;
 apply s1; apply s;
 assumption.
qed.

(*

definition powerset_setoid: setoid → setoid1.
 intros (T);
 constructor 1;
  [ apply (powerset_carrier T)
  | constructor 1;
     [ apply (λU,V. subseteq_operator ? U V ∧ subseteq_operator ? V U)
     | simplify; intros; split; intros 2; assumption
     | simplify; intros (x y H); cases H; split; assumption
     | simplify; intros (x y z H H1); cases H; cases H1; split;
       apply transitive_subseteq_operator; [1,4: apply y ]
       assumption ]]
qed.

interpretation "powerset" 'powerset A = (powerset_setoid A).

interpretation "subset construction" 'subset \eta.x =
 (mk_powerset_carrier _ (mk_unary_morphism _ CPROP x _)).

definition mem: ∀A. binary_morphism1 A (Ω \sup A) CPROP.
 intros;
 constructor 1;
  [ apply (λx,S. mem_operator ? S x)
  | intros 5;
    cases b; clear b; cases b'; clear b'; simplify; intros;
    apply (trans1 ????? (prop_1 ?? u ?? H));
    cases H1; whd in s s1;
    split; intro;
     [ apply s; assumption
     | apply s1; assumption]]
qed.     

interpretation "mem" 'mem a S = (fun1 ??? (mem ?) a S).

definition subseteq: ∀A. binary_morphism1 (Ω \sup A) (Ω \sup A) CPROP.
 intros;
 constructor 1;
  [ apply (λU,V. subseteq_operator ? U V)
  | intros;
    cases H; cases H1;
    split; intros 1;
    [ apply (transitive_subseteq_operator ????? s2);
      apply (transitive_subseteq_operator ???? s1 s4)
    | apply (transitive_subseteq_operator ????? s3);
      apply (transitive_subseteq_operator ???? s s4) ]]
qed.

interpretation "subseteq" 'subseteq U V = (fun1 ??? (subseteq ?) U V).

theorem subseteq_refl: ∀A.∀S:Ω \sup A.S ⊆ S.
 intros 4; assumption.
qed.

theorem subseteq_trans: ∀A.∀S1,S2,S3: Ω \sup A. S1 ⊆ S2 → S2 ⊆ S3 → S1 ⊆ S3.
 intros; apply transitive_subseteq_operator; [apply S2] assumption.
qed.

definition overlaps: ∀A. binary_morphism1 (Ω \sup A) (Ω \sup A) CPROP.
 intros;
 constructor 1;
  [ apply (λA.λU,V:Ω \sup A.exT2 ? (λx:A.x ∈ U) (λx:A.x ∈ V))
  | intros;
    constructor 1; intro; cases H2; exists; [1,4: apply w]
     [ apply (. #‡H); assumption
     | apply (. #‡H1); assumption
     | apply (. #‡(H \sup -1)); assumption;
     | apply (. #‡(H1 \sup -1)); assumption]]
qed.

interpretation "overlaps" 'overlaps U V = (fun1 ??? (overlaps ?) U V).

definition intersects:
 ∀A. binary_morphism1 (powerset_setoid A) (powerset_setoid A) (powerset_setoid A).
 intros;
 constructor 1;
  [ apply (λU,V. {x | x ∈ U ∧ x ∈ V });
    intros; simplify; apply (.= (H‡#)‡(H‡#)); apply refl1;
  | intros;
    split; intros 2; simplify in f ⊢ %;
    [ apply (. (#‡H)‡(#‡H1)); assumption
    | apply (. (#‡(H \sup -1))‡(#‡(H1 \sup -1))); assumption]]
qed.

interpretation "intersects" 'intersects U V = (fun1 ??? (intersects ?) U V).

definition union:
 ∀A. binary_morphism1 (powerset_setoid A) (powerset_setoid A) (powerset_setoid A).
 intros;
 constructor 1;
  [ apply (λU,V. {x | x ∈ U ∨ x ∈ V });
    intros; simplify; apply (.= (H‡#)‡(H‡#)); apply refl1
  | intros;
    split; intros 2; simplify in f ⊢ %;
    [ apply (. (#‡H)‡(#‡H1)); assumption
    | apply (. (#‡(H \sup -1))‡(#‡(H1 \sup -1))); assumption]]
qed.

interpretation "union" 'union U V = (fun1 ??? (union ?) U V).

definition singleton: ∀A:setoid. unary_morphism A (Ω \sup A).
 intros; constructor 1;
  [ apply (λA:setoid.λa:A.{b | a=b});
    intros; simplify;
    split; intro;
    apply (.= H1);
     [ apply H | apply (H \sup -1) ]
  | intros; split; intros 2; simplify in f ⊢ %; apply trans;
     [ apply a |4: apply a'] try assumption; apply sym; assumption]
qed.

interpretation "singleton" 'singl a = (fun_1 ?? (singleton ?) a).

*)