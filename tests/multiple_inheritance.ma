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

set "baseuri" "cic:/matita/test/".

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
 [ apply (C r)
 | apply (eq_rect ? ? (λx.x → x → x));
   [3: symmetry;
       [2: apply (with_ r)
       | skip
       ]
   | skip
   | apply (mult (r2_ r))
   ]
 ].
qed.
coercion cic:/matita/test/r2.con.

(* Let's play with it *)
definition f ≝ λr:R.λx:r.plus ? (mult ? x x) x.

axiom plus_idempotent: ∀r1:R1.∀x:r1. plus ? x x = x.
axiom mult_idempotent: ∀r2:R2.∀x:r2. mult ? x x = x.

lemma test: ∀r:R. ∀x:r. f ? x = x.
 intros;
 unfold f;
 auto paramodulation.
qed.