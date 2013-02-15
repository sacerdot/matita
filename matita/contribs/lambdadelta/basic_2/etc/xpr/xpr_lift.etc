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
include "basic_2/reducibility/cpr_lift.ma".
include "basic_2/reducibility/xpr.ma".

(* EXTENDED PARALLEL REDUCTION ON TERMS *************************************)

(* Advanced inversion lemmas ************************************************)

lemma xpr_inv_abst1: ∀h,g,a,L,V1,T1,U2. ⦃h, L⦄ ⊢ ⓛ{a}V1.T1 •➡[g] U2 →
                     ∃∃V2,T2. L ⊢ V1 ➡ V2 & ⦃h, L. ⓛV1⦄ ⊢ T1 •➡[g] T2 &
                              U2 = ⓛ{a}V2. T2.
#h #g #a #L #V1 #T1 #U2 *
[ #H elim (cpr_inv_abst1 … H Abst V1) /3 width=5/
| #l #H elim (ssta_inv_bind1 … H) /3 width=5/
]
qed-.

(* Relocation properties ****************************************************)

lemma xpr_lift: ∀L,K,d,e. ⇩[d, e] L ≡ K →
                ∀T1,U1. ⇧[d, e] T1 ≡ U1 → ∀T2,U2. ⇧[d, e] T2 ≡ U2 →
                ∀h,g. ⦃h, K⦄ ⊢ T1 •➡[g] T2 → ⦃h, L⦄ ⊢ U1 •➡[g] U2.
#L #K #d #e #HLK #T1 #U1 #HTU1 #T2 #U2 #HTU2 #h #g *
/3 width=9/ /3 width=10/
qed.

lemma xpr_inv_lift1: ∀L,K,d,e. ⇩[d, e] L ≡ K →
                     ∀T1,U1. ⇧[d, e] T1 ≡ U1 → ∀h,g,U2. ⦃h, L⦄ ⊢ U1 •➡[g] U2 →
                     ∃∃T2. ⇧[d, e] T2 ≡ U2 & ⦃h, K⦄ ⊢ T1 •➡[g] T2.
#L #K #d #e #HLK #T1 #U1 #HTU1 #h #g #U2 * [ #HU12 | #l #HU12 ]
[ elim (cpr_inv_lift1 … HLK … HTU1 … HU12) -L -U1 /3 width=3/
| elim (ssta_inv_lift1 … HU12 … HLK … HTU1) -L -U1 /3 width=4/
]
qed-.
