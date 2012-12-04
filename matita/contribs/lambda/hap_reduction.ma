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

include "labelled_sequential_reduction.ma".

(* KASHIMA'S "HAP" COMPUTATION (SINGLE STEP) ********************************)

(* Note: this is one step of the "head in application" computation of:
         R. Kashima: "A proof of the Standization Theorem in λ-Calculus". Typescript note, (2000).
*)
inductive hap1: relation term ≝
| hap1_beta: ∀B,A. hap1 (@B.𝛌.A) ([⬐B]A)
| hap1_appl: ∀B,A1,A2. hap1 A1 A2 → hap1 (@B.A1) (@B.A2)
.

lemma hap1_lift: liftable hap1.
#h #M1 #M2 #H elim H -M1 -M2 normalize /2 width=1/
#B #A #d <dsubst_lift_le //
qed.

lemma hap1_inv_lift: deliftable hap1.
#h #N1 #N2 #H elim H -N1 -N2
[ #D #C #d #M1 #H
  elim (lift_inv_appl … H) -H #B #M #H0 #HM #H destruct
  elim (lift_inv_abst … HM) -HM #A #H0 #H destruct /3 width=3/
| #D1 #C1 #C2 #_ #IHC12 #d #M1 #H
  elim (lift_inv_appl … H) -H #B #A1 #H1 #H2 #H destruct
  elim (IHC12 ???) -IHC12 [4: // |2,3: skip ] #A2 #HA12 #H destruct (**) (* simplify line *)
  @(ex2_1_intro … (@B.A2)) // /2 width=1/
]
qed-.

lemma hap1_dsubstable: dsubstable_dx hap1.
#D1 #M1 #M2 #H elim H -M1 -M2 normalize /2 width=1/
#D2 #A #d >dsubst_dsubst_ge //
qed.

lemma hap1_lsred: ∀M,N. hap1 M N →
                  ∃∃p. in_spine p & M ⇀[p] N.
#M #N #H elim H -M -N /2 width=3/
#B #A1 #A2 #_ * /3 width=3/
qed-.
