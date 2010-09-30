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

axiom daemon: False.

record iff (A,B: CProp) : CProp ≝
 { if: A → B;
   fi: B → A
 }.

notation > "hvbox(a break \liff b)"
  left associative with precedence 25
for @{ 'iff $a $b }.

notation "hvbox(a break \leftrightarrow b)"
  left associative with precedence 25
for @{ 'iff $a $b }.

interpretation "logical iff" 'iff x y = (iff x y).

definition reflexive1 ≝ λA:Type.λR:A→A→CProp.∀x:A.R x x.
definition symmetric1 ≝ λC:Type.λlt:C→C→CProp. ∀x,y:C.lt x y → lt y x.
definition transitive1 ≝ λA:Type.λR:A→A→CProp.∀x,y,z:A.R x y → R y z → R x z.

record setoid : Type ≝
 { carr:> Type;
   eq: carr → carr → CProp;
   refl: reflexive ? eq;
   sym: symmetric ? eq;
   trans: transitive ? eq
 }.

definition proofs: CProp → setoid.
 intro;
 constructor 1;
  [ apply A
  | intros;
    apply True
  | intro;
    constructor 1
  | intros 3;
    constructor 1
  | intros 5;
    constructor 1]
qed.

record setoid1 : Type ≝
 { carr1:> Type;
   eq1: carr1 → carr1 → CProp;
   refl1: reflexive1 ? eq1;
   sym1: symmetric1 ? eq1;
   trans1: transitive1 ? eq1
 }.

definition proofs1: CProp → setoid1.
 intro;
 constructor 1;
  [ apply A
  | intros;
    apply True
  | intro;
    constructor 1
  | intros 3;
    constructor 1
  | intros 5;
    constructor 1]
qed.

definition CCProp: setoid1.
 constructor 1;
  [ apply CProp
  | apply iff
  | intro;
    split;
    intro;
    assumption
  | intros 3;
    cases H; clear H;
    split;
    assumption
  | intros 5;
    cases H; cases H1; clear H H1;
    split;
    intros;
    [ apply (H4 (H2 H))
    | apply (H3 (H5 H))]]
qed.

record function_space (A,B: setoid): Type ≝
 { f:1> A → B;
   f_ok: ∀a,a':A. proofs (eq ? a a') → proofs (eq ? (f a) (f a'))
 }.
 
notation "hbox(a break ⇒ b)" right associative with precedence 20 for @{ 'Imply $a $b }.

record function_space1 (A: setoid1) (B: setoid1): Type ≝
 { f1:1> A → B;
   f1_ok: ∀a,a':A. proofs1 (eq1 ? a a') → proofs1 (eq1 ? (f1 a) (f1 a'))
 }.

definition function_space_setoid: setoid → setoid → setoid.
 intros (A B);
 constructor 1;
  [ apply (function_space A B);
  | intros;
    apply (∀a:A. proofs (eq ? (f a) (f1 a)));
  | simplify;
    intros;
    apply (f_ok ? ? x);
    unfold carr; unfold proofs; simplify;
    apply (refl A)
  | simplify;
    intros;
    unfold carr; unfold proofs; simplify;
    apply (sym B);
    apply (f a)
  | simplify;
    intros;
    unfold carr; unfold proofs; simplify;
    apply (trans B ? (y a));
    [ apply (f a)
    | apply (f1 a)]]
qed.

definition function_space_setoid1: setoid1 → setoid1 → setoid1.
 intros (A B);
 constructor 1;
  [ apply (function_space1 A B);
  | intros;
    apply (∀a:A. proofs1 (eq1 ? (f a) (f1 a)));
  |*: cases daemon] (* simplify;
    intros;
    apply (f1_ok ? ? x);
    unfold proofs; simplify;
    apply (refl1 A)
  | simplify;
    intros;
    unfold proofs; simplify;
    apply (sym1 B);
    apply (f a)
  | simplify;
    intros;
    unfold carr; unfold proofs; simplify;
    apply (trans1 B ? (y a));
    [ apply (f a)
    | apply (f1 a)]] *)
qed.

interpretation "function_space_setoid1" 'Imply a b = (function_space_setoid1 a b).

record isomorphism (A,B: setoid): Type ≝
 { map1:> function_space_setoid A B;
   map2:> function_space_setoid B A;
   inv1: ∀a:A. proofs (eq ? (map2 (map1 a)) a);
   inv2: ∀b:B. proofs (eq ? (map1 (map2 b)) b)
 }.

interpretation "isomorphism" 'iff x y = (isomorphism x y).

definition setoids: setoid1.
 constructor 1;
  [ apply setoid;
  | apply isomorphism;
  | intro;
    split;
     [1,2: constructor 1;
        [1,3: intro; assumption;
        |*: intros; assumption]
     |3,4:
       intros;
       simplify;
       unfold proofs; simplify;
       apply refl;]
  |*: cases daemon]
qed.

definition setoid1_of_setoid: setoid → setoid1.
 intro;
 constructor 1;
  [ apply (carr s)
  | apply (eq s)
  | apply (refl s)
  | apply (sym s)
  | apply (trans s)]
qed.

coercion setoid1_of_setoid.

(*
record dependent_product (A:setoid)  (B: A ⇒ setoids): Type ≝
 { dp:> ∀a:A.carr (B a);
   dp_ok: ∀a,a':A. ∀p:proofs1 (eq1 ? a a'). proofs1 (eq1 ? (dp a) (map2 ?? (f1_ok ?? B ?? p) (dp a')))
 }.*)

record forall (A:setoid)  (B: A ⇒ CCProp): CProp ≝
 { fo:> ∀a:A.proofs (B a) }.

record subset (A: setoid) : CProp ≝
 { mem: A ⇒ CCProp }.

definition ssubset: setoid → setoid1.
 intro;
 constructor 1;
  [ apply (subset s);
  | apply (λU,V:subset s. ∀a. mem ? U a \liff mem ? V a)
  | simplify;
    intros;
    split;
    intro;
    assumption
  | simplify;
    cases daemon
  | cases daemon]
qed.

definition mmem: ∀A:setoid. (ssubset A) ⇒ A ⇒ CCProp.
 intros;
 constructor 1;
  [ apply mem; 
  | unfold function_space_setoid1; simplify;
    intros (b b');
    change in ⊢ (? (? (?→? (? %)))) with (mem ? b a \liff mem ? b' a);
    unfold proofs1; simplify; intros;
    unfold proofs1 in c; simplify in c;
    unfold ssubset in c; simplify in c;
    cases (c a); clear c;
    split;
    assumption]
qed.

(*
definition sand: CCProp ⇒ CCProp.

definition intersection: ∀A. ssubset A ⇒ ssubset A ⇒ ssubset A.
 intro;
 constructor 1;
  [ intro;
    constructor 1;
     [ intro;
       constructor 1;
       constructor 1;
       intro;
       apply (mem ? c c2 ∧ mem ? c1 c2);
     |
  |
  |
*)
