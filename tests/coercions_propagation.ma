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

(*
theorem test5: nat → ∃n. 0 ≤ n.
 apply (λn:nat.?);
 apply
  (match n return λ_.∃n.0 ≤ n with [O ⇒ (0 : ∃n.0 ≤ n) | S n' ⇒ ex_intro ? ? n' ?]
  : ∃n. 0 ≤ n);
 autobatch.
qed.
*)
