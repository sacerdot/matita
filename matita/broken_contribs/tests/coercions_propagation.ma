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



include "logic/connectives.ma".
include "nat/orders.ma".

inductive sigma (A:Type) (P:A → Prop) : Type ≝
 sigma_intro: ∀a:A. P a → sigma A P.

interpretation "sigma" 'exists \eta.x =
  (cic:/matita/tests/coercions_propagation/sigma.ind#xpointer(1/1) _ x).
  
definition inject ≝ λP.λa:nat.λp:P a. sigma_intro ? P ? p.

coercion cic:/matita/tests/coercions_propagation/inject.con 0 1.

definition eject ≝ λP.λc: ∃n:nat.P n. match c with [ sigma_intro w _ ⇒ w].

coercion cic:/matita/tests/coercions_propagation/eject.con.

alias num (instance 0) = "natural number".
theorem test: ∃n. 0 ≤ n.
 apply (S O : ∃n. 0 ≤ n).
 autobatch.
qed.

theorem test2: nat → ∃n. 0 ≤ n.
 apply ((λn:nat. 0) : nat → ∃n. 0 ≤ n);
 autobatch.
qed.

theorem test3: (∃n. 0 ≤ n) → nat.
 apply ((λn:nat.n) : (∃n. 0 ≤ n) → nat).
qed.

theorem test4: (∃n. 1 ≤ n) → ∃n. 0 < n.
 apply ((λn:nat.n) : (∃n. 1 ≤ n) → ∃n. 0 < n);
 cases s;
 assumption.
qed.

theorem test5: nat → ∃n. 1 ≤ n.
apply (
 let rec aux n : nat ≝
  match n with
   [ O ⇒ 1
   | S m ⇒ S (aux m)
   ]
 in
  aux
: nat → ∃n. 1 ≤ n);
[ cases (aux n1); simplify; ] autobatch;
qed.

inductive NN (A:Type) : nat -> Type ≝
 | NO : NN A O
 | NS : ∀n:nat. NN A n → NN A (S n).
 
definition injectN ≝ λA,k.λP.λa:NN A k.λp:P a. sigma_intro ? P ? p.

coercion cic:/matita/tests/coercions_propagation/injectN.con 0 1.

definition ejectN ≝ λA,k.λP.λc: ∃n:NN A k.P n. match c with [ sigma_intro w _ ⇒ w].

coercion cic:/matita/tests/coercions_propagation/ejectN.con.

definition PN :=
 λA,k.λx:NN A k. 1 <= k.

theorem test51_byhand: ∀A,k. NN A k → ∃n:NN A (S k). PN ? ? n.
intros 1;
apply (
 let rec aux (w : nat) (n : NN A w) on n : ∃p:NN A (S w).PN ? ? p ≝
  match n in NN return λx.λm:NN A x.∃p:NN A (S x).PN ? ? p with
   [ NO ⇒ injectN ? ? ? (NS A ? (NO A)) ?
   | NS x m ⇒ injectN ? ? ? (NS A (S x) (ejectN ? ? ? (aux ? m))) ?  
   ]
 in
  aux
: ∀n:nat. NN A n → ∃m:NN A (S n). PN ? ? m);
[2: cases (aux x m); simplify; autobatch ] unfold PN; autobatch;
qed.

theorem f : nat -> nat -> ∃n:nat.O <= n.
apply (λx,y:nat.y : nat -> nat -> ∃n:nat. O <= n).
apply le_O_n; 
qed.

axiom F : nat -> nat -> nat.

theorem f1 : nat -> nat -> ∃n:nat.O <= n.
apply (F : nat -> nat -> ∃n:nat. O <= n).
apply le_O_n; 
qed.

theorem test51: ∀A,k. NN A k → ∃n:NN A (S k). PN ? ? n.
intros 1;
letin xxx ≝ (
 let rec aux (w : nat) (n : NN A w) on n : NN A (S w) ≝
  match n in NN return λx.λm:NN A x.NN A (S x) with
   [ NO ⇒ NS A ? (NO A)
   | NS x m ⇒ NS A (S x) (aux ? m)  
   ]
 in
  aux
: ∀n:nat. NN A n → ∃m:NN A (S n). PN ? ? m); [3: apply xxx];
unfold PN in aux ⊢ %; [cases (aux n2 n3)] autobatch;
qed.

(* guarded troppo debole *)
theorem test522: nat → ∃n. 1 ≤ n.
apply (
 let rec aux n : nat ≝
  match n with
   [ O ⇒ 1
   | S m ⇒ S (aux m)
   ]
 in
  aux
: nat → ∃n. 1 ≤ n);
[ cases (aux n1); simplify;
  autobatch
| autobatch].
qed.

