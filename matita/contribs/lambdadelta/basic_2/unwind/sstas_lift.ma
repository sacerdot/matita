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

include "basic_2/static/ssta_lift.ma".
include "basic_2/unwind/sstas.ma".

(* ITERATED STRATIFIED STATIC TYPE ASSIGNMENT FOR TERMS *********************)

(* Advanced forward lemmas **************************************************)

lemma sstas_fwd_correct: ∀h,g,L,T1,U1,l1. ⦃h, L⦄ ⊢ T1 •[g] ⦃l1, U1⦄ →
                         ∀T2. ⦃h, L⦄ ⊢ T1 •*[g] T2 →
                         ∃∃U2,l2. ⦃h, L⦄ ⊢ T2 •[g] ⦃l2, U2⦄.
#h #g #L #T1 #U1 #l1 #HTU1 #T2 #H @(sstas_ind … H) -T2 [ /2 width=3/ ] -HTU1
#T #T2 #l #_ #HT2 * #U #l0 #_ -l0
elim (ssta_fwd_correct … HT2) -T /2 width=3/
qed-.

(* Properties on relocation *************************************************)

lemma sstas_lift: ∀h,g,L1,T1,U1. ⦃h, L1⦄ ⊢ T1 •*[g] U1 →
                  ∀L2,d,e. ⇩[d, e] L2 ≡ L1 → ∀T2. ⇧[d, e] T1 ≡ T2 →
                  ∀U2. ⇧[d, e] U1 ≡ U2 → ⦃h, L2⦄ ⊢ T2 •*[g] U2.
#h #g #L1 #T1 #U1 #H @(sstas_ind_dx … H) -T1
[ #L2 #d #e #HL21 #X #HX #U2 #HU12
  >(lift_mono … HX … HU12) -X //
| #T0 #U0 #l0 #HTU0 #_ #IHU01 #L2 #d #e #HL21 #T2 #HT02 #U2 #HU12
  elim (lift_total U0 d e) /3 width=10/
]
qed.

(* Inversion lemmas on relocation *******************************************)

lemma sstas_inv_lift1: ∀h,g,L2,T2,U2. ⦃h, L2⦄ ⊢ T2 •*[g] U2 →
                       ∀L1,d,e. ⇩[d, e] L2 ≡ L1 → ∀T1. ⇧[d, e] T1 ≡ T2 →
                       ∃∃U1. ⦃h, L1⦄ ⊢ T1 •*[g] U1 & ⇧[d, e] U1 ≡ U2.
#h #g #L2 #T2 #U2 #H @(sstas_ind_dx … H) -T2 /2 width=3/
#T0 #U0 #l0 #HTU0 #_ #IHU01 #L1 #d #e #HL21 #U1 #HU12
elim (ssta_inv_lift1 … HTU0 … HL21 … HU12) -HTU0 -HU12 #U #HU1 #HU0
elim (IHU01 … HL21 … HU0) -IHU01 -HL21 -U0 /3 width=4/
qed-.
