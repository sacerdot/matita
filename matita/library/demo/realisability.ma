(**************************************************************************)
(*       ___	                                                              *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||       A.Asperti, C.Sacerdoti Coen,                          *)
(*      ||A||       E.Tassi, S.Zacchiroli                                 *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU Lesser General Public License Version 2.1         *)
(*                                                                        *)
(**************************************************************************)

include "logic/connectives.ma".
include "datatypes/constructors.ma".

(* The following is a stranslation in Matita of the initial part of
   Erik Palmgren, ``Internalizing Modified Realizability in Constructive Type
   Theory'', Logical Methods in Computer Science, Vol 1 (2:2), 2005, pp. 1--7
   
   The original Agda file realisability.agda can be found at
   
   http://www.math.uu.se/~palmgren/modif/realisability.agda
*)

inductive SP : Type ≝
   abs: SP
 | atom: ∀P:Prop.SP
 | sand: SP → SP → SP
 | sor: SP → SP → SP
 | simp: SP → SP → SP
 | forall: ∀A:Type. (A → SP) → SP
 | exist: ∀A:Type. (A → SP) → SP.

let rec Prop_OF_SP F ≝
 match F with
  [ abs ⇒ False
  | atom P ⇒ P
  | sand A B ⇒ Prop_OF_SP A ∧ Prop_OF_SP B
  | sor A B ⇒ Prop_OF_SP A ∨ Prop_OF_SP B
  | simp A B ⇒ Prop_OF_SP A → Prop_OF_SP B
  | forall A F ⇒ ∀x:A.Prop_OF_SP (F x)
  | exist A F ⇒ ∃x:A.Prop_OF_SP (F x)
  ].

inductive sigma (A:Type) (P:A → Type) : Type ≝
 sigma_intro: ∀x:A. P x → sigma A P.

definition pi1 ≝
 λA,P.λs:sigma A P.
  match s with
   [ sigma_intro a _ ⇒ a].

definition pi2 ≝
 λA,P.λs:sigma A P.
  match s return λs.P (pi1 ? ? s) with
   [ sigma_intro _ p ⇒ p].

notation "hvbox(\Sigma ident i opt (: ty) break . p)"
  right associative with precedence 20
for @{ 'sigma ${default
  @{\lambda ${ident i} : $ty. $p}
  @{\lambda ${ident i} . $p}}}.

interpretation "Sigma" 'sigma \eta.x = (sigma ? x).

let rec type_OF_SP F ≝
 match F return λF.Type with
  [ abs ⇒ unit
  | atom P ⇒ unit
  | sand A B ⇒ (type_OF_SP A) × (type_OF_SP B)
  | sor A B ⇒ type_OF_SP A + type_OF_SP B
  | simp A B ⇒ type_OF_SP A → type_OF_SP B
  | forall A F ⇒ Πx:A.type_OF_SP (F x)
  | exist A F ⇒ Σx:A.type_OF_SP (F x)
  ].

let rec modr F : type_OF_SP F → Prop ≝
 match F return λF.type_OF_SP F → Prop with
  [ abs ⇒ λr.False
  | atom P ⇒ λr.P
  | sand A B ⇒ λr.modr A (\fst r) ∧ modr B (\snd r)
  | sor A B ⇒
     λr.
      match r with
       [ inl a ⇒ modr A a
       | inr b ⇒ modr B b
       ]
  | simp A B ⇒
     λr.
      (Prop_OF_SP A → Prop_OF_SP B) ∧
      ∀a:type_OF_SP A. modr A a → modr B (r a)
  | forall A F ⇒
     λr:Πx:A.type_OF_SP (F x).∀a:A. modr (F a) (r a)
  | exist A F ⇒
     λr.
      modr (F (pi1 ? ? r)) (pi2 ? ? r)
  ].

theorem correct: ∀F:SP.∀r:type_OF_SP F.modr F r → Prop_OF_SP F.
 intro;
 elim F; simplify;
  [1,2: apply H
  | split; simplify in r H2; 
     [apply H;
       [ apply (\fst r)
       | apply (proj1 ? ? H2)
       ]
     | apply H1;simplify in r H2;
       [ apply (\snd r)
       | apply (proj2 ? ? H2)
       ]
     ]
  | change in r with (type_OF_SP s + type_OF_SP s1);
    elim r in H2 ⊢ %; simplify in H2;
     [ left; apply H; assumption
     | right; apply H1; assumption
     ]
  | simplify in H2;
    apply (proj1 ? ? H2)
  | simplify in H1;
    intro;
    apply H;
    [2: apply H1
    | skip
    ]
  | simplify in r;
    elim r in H1 ⊢ %;
    apply (ex_intro ? ? a);
    apply H;
    assumption
  ]
qed.

definition realized ≝
 λF:SP.∃r:type_OF_SP F.modr F r.

theorem correct2: ∀F:SP. realized F → Prop_OF_SP F.
 intros;
 elim H;
 apply correct;
 assumption.
qed.

theorem extraction:
 ∀A,B:Type.∀P: A → B → SP.
  realized (forall A (λa:A. exist B (λb:B. P a b))) →
   ∀a:A.∃b:B.Prop_OF_SP (P a b).
 intros;
 apply (correct2 (exist ? (λb:B. P a b)));
 simplify in H; elim H; clear H;
 simplify;
 apply (ex_intro ? ? (a1 a));
 apply H1.
qed.

lemma true_impl_realized:
 ∀A,B:Prop. (A → B) → realized (simp (atom A) (atom B)).
 intros;
 simplify;
 apply (ex_intro ? ? (λu.u));
 split;
  [ assumption
  | intro; assumption
  ]
qed.

(******** rules for first order logic **********************)

lemma elim_abs: ∀P:Prop. realized (simp abs (atom P)).
 intro;
 simplify;
 apply (ex_intro ? ? (λu.u));
 split;
  [ intro; cases H
  | intros; cases H
  ]
qed.

lemma id_axiom: ∀F:SP. realized (simp F F).
 intros;
 simplify;
 apply (ex_intro ? ? (λu.u));
 split;
  [ intro; assumption
  | intros; assumption
  ]
qed.

lemma cut:
 ∀F1,F2,F3:SP.
  realized (simp F1 F2) → realized (simp F2 F3) → realized (simp F1 F3).
 intros;
 elim H; clear H;
 elim H1; clear H1;
 simplify in a a1;
 apply (ex_intro ? ? (λx.a1 (a x)));
 simplify;
 simplify in H2 H;
 elim H2; clear H2;
 elim H; clear H;
 split;
  [ intro; apply (H2 (H1 H))
  | intros; apply (H4 ? (H3 ? H))
  ]
qed.

lemma and_i:
 ∀F1,F2,F3:SP.
  realized (simp F1 F2) → realized (simp F1 F3) → realized (simp F1 (sand F2 F3)).
 intros;
 elim H; clear H;
 elim H1; clear H1;
 simplify in a a1 ⊢ %;
 apply (ex_intro ? ? (λu.〈a u, a1 u〉));
 simplify in H2; cases H2; clear H2;
 simplify in H; cases H; clear H;
 split;
  [ intro; split; [ apply (H1 H) | apply (H2 H) ] 
  | intros;
    split;
     [ simplify; apply H3; assumption
     | simplify; apply H4; assumption
     ]
  ]
qed.

(* Many more rules and examples missing, but trivial. *)
