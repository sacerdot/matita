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

set "baseuri" "cic:/matita/test/coercions_propagation/".

include "logic/connectives.ma".
include "nat/orders.ma".
alias num (instance 0) = "natural number".

inductive sigma (A:Type) (P:A → Prop) : Type ≝
 sigma_intro: ∀a:A. P a → sigma A P.

interpretation "sigma" 'exists \eta.x =
  (cic:/matita/test/coercions_propagation/sigma.ind#xpointer(1/1) _ x).
  
definition inject ≝ λP.λa:nat.λp:P a. sigma_intro ? P ? p.

coercion cic:/matita/test/coercions_propagation/inject.con 0 1.

definition eject ≝ λP.λc: ∃n:nat.P n. match c with [ sigma_intro w _ ⇒ w].

coercion cic:/matita/test/coercions_propagation/eject.con.

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
 cases name_con;
 assumption.
qed.

(* guarded troppo debole 
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
cases name_con;
simplify;
 [ autobatch
 | cases (aux n);
   simplify;
   apply lt_O_S
 ]
qed.
*)

(*
theorem test5: nat → ∃n. 1 ≤ n.
apply (
 let rec aux (n : nat) : ∃n. 1 ≤ n ≝ 
   match n with
   [ O => (S O : ∃n. 1 ≤ n)
   | S m => (S (aux m) : ∃n. 1 ≤ n)
(*      
   inject ? (S (eject ? (aux m))) ? *)
   ]
 in
  aux
 : nat → ∃n. 1 ≤ n);
 [ autobatch
 | elim (aux m);
   simplify;
   autobatch
 ]
qed.

Re1: nat => nat |- body[Rel1] : nat => nat
Re1: nat => X |- body[Rel1] : nat => nat : nat => X
Re1: Y => X |- body[Rel1] : nat => nat : Y => X

nat => nat
nat => X

theorem test5: (∃n. 2 ≤ n) → ∃n. 1 ≤ n.
apply (
 λk: ∃n. 2 ≤ n.
 let rec aux n : eject ? n = eject ? k → ∃n. 1 ≤ n ≝
  match eject ? n return λx:nat. x = eject ? k → ∃n. 1 ≤ n with
   [ O ⇒ λH: 0 = eject ? k.
          sigma_intro ? ? 0 ?
   | S m ⇒ λH: S m = eject ? k.
          sigma_intro ? ? (S m) ?
   ]
 in
  aux k (refl_eq ? (eject ? k)));


intro;
cases s; clear s;
generalize in match H; clear H;
elim a;
 [ apply (sigma_intro ? ? 0);
 | apply (sigma_intro ? ? (S n));
 ].

apply (
 λk.
 let rec aux n : ∃n. 1 ≤ n ≝
  inject ?
   (match n with
     [ O ⇒ O
     | S m ⇒ S (eject ? (aux m))
     ]) ?
 in aux (eject ? k)).

   
apply (
 let rec aux n : nat ≝
  match n with
   [ O ⇒ O
   | S m ⇒ S (aux m)
   ]
 in
  aux
: (∃n. 2 ≤ n) → ∃n. 1 ≤ n);

qed.

(*
theorem test5: nat → ∃n. 0 ≤ n.
 apply (λn:nat.?);
 apply
  (match n return λ_.∃n.0 ≤ n with [O ⇒ (0 : ∃n.0 ≤ n) | S n' ⇒ ex_intro ? ? n' ?]
  : ∃n. 0 ≤ n);
 autobatch.
qed.
*)
*)