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



include "logic/equality.ma".

record R1 : Type := { C:> Type; plus: C \to C \to C}.
record R2 : Type := { K:> Type; mult: K \to K \to K}.

(* Missing syntactic sugar:
   record R : Type := { r1 :> R1; r2 :> R2 with C r1 = K r2}
*)
record R : Type := { r1 :> R1; r2_ : R2; with_: C r1 = K r2_ }.

(* This can be done automatically *)
lemma r2 : R → R2.
 intro;
 apply mk_R2;
 [ exact (C r)
 | rewrite > (with_ r); exact (mult (r2_ r))]
qed.
coercion cic:/matita/tests/multiple_inheritance/r2.con.

(* convertibility test *)
lemma conv_test : ∀r:R.C r -> K r.
  intros.
  change with (C (r1 r)).
  change with (K (r2 r)).
  change with (C (r1 r)).
  assumption.
qed.

(* Let's play with it *)
definition f ≝ λr:R.λx:r.plus ? (mult ? x x) x.

axiom plus_idempotent: ∀r1:R1.∀x:r1. plus ? x x = x.
axiom mult_idempotent: ∀r2:R2.∀x:r2. mult ? x x = x.

lemma test: ∀r:R. ∀x:r. f ? x = x.
 intros;
 unfold f;
 autobatch paramodulation.
qed.



