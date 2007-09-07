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

set "baseuri" "cic:/matita/test/russell/".

include "nat/orders.ma".
include "list/list.ma".

inductive sigma (A:Type) (P:A → Prop) : Type ≝
 sig_intro: ∀a:A. P a → sigma A P.

interpretation "sigma" 'exists \eta.x =
  (cic:/matita/test/russell/sigma.ind#xpointer(1/1) _ x).
 
definition inject ≝ λP.λa:list nat.λp:P a. sig_intro ? P ? p.

coercion cic:/matita/test/russell/inject.con 0 1.

definition eject ≝ λP.λc: ∃n:list nat.P n. match c with [ sig_intro w _ ⇒ w].

coercion cic:/matita/test/russell/eject.con.
  
alias symbol "exists" (instance 2) = "exists".
lemma tl : ∀l:list nat. l ≠ [] → ∃l1.∃a.a :: l1 = l.
letin program ≝ 
  (λl:list nat. λH:l ≠ [].match l with [ nil ⇒ λH.[] | cons x l1 ⇒ λH.l1] H);
letin program_spec ≝ (program : ∀l:list nat. l ≠ [] → ∃l1.∃a.a :: l1 = l);
 [ generalize in match H; cases l; [intros (h1); cases (h1 ?); reflexivity]
   intros; apply (ex_intro ? ? n); apply eq_f; reflexivity; ]
exact program_spec;
qed.

alias symbol "exists" (instance 3) = "exists".
lemma tl2 : ∀l:∃l:list nat. l ≠ []. ∃l1.∃a.a :: l1 = l.
letin program ≝ 
  (λl:list nat. match l with [ nil ⇒ [] | cons x l1 ⇒ l1]);
letin program_spec ≝ 
  (program : ∀l:∃l:list nat. l ≠ []. ∃l1.∃a.a :: l1 = l);
  [ autobatch; | generalize in match H; clear H; cases s; simplify;
    intros; cases (H H1); ]
exact program_spec.
qed.
