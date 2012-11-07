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

include "basic_2/static/ssta.ma".
include "basic_2/dynamic/snv.ma".

(* STRATIFIED NATIVE VALIDITY FOR TERMS *************************************)

(* Properties on stratified static type assignment for terms ****************)

lemma snv_ssta: ∀h,g,L,T. ⦃h, L⦄ ⊩ T :[g] → ∃∃U,l. ⦃h, L⦄ ⊢ T •[g, l] U.
#h #g #L #T #H elim H -L -T
[ #L #k elim (deg_total h g k) /3 width=3/
| * #L #K #V #i #HLK #_ * #W #l0 #HVW
  [ elim (lift_total W 0 (i+1)) /3 width=8/
  | elim (lift_total V 0 (i+1)) /3 width=8/
  ]
| #a #I #L #V #T #_ #_ #_ * /3 width=3/
| #a #L #V #W #W1 #T0 #T1 #l #_ #_ #_ #_ #_ #_ * /3 width=3/
| #L #W #T #U #l #_ #_ #HTU #_ #_ #_ /3 width=3/ (**) (* auto fails without the last #_ *) 
]
qed-.
(*
fact snv_ssta_conf_aux: ∀h,g,L,T. (
                           ∀L0,T1,U1,l1. ⦃h, L0⦄ ⊢ T1 •[g, l1] U1 →
                           ∀T2,U2,l2. ⦃h, L0⦄ ⊢ T2 •[g, l2] U2 →
                           L0 ⊢ T1 ⬌* T2 → ⦃h, L0⦄ ⊩ T1 :[g] →  ⦃h, L0⦄ ⊩ T2 :[g] →
                           #{L0, T1} < #{L ,T} →
                           l1 = l2 ∧ L0 ⊢ U1 ⬌* U2
                        ) → (
                           ∀L0,T0. ⦃h, L0⦄ ⊩ T0 :[g] →
                           ∀U0. ⦃h, L0⦄ ⊢ T0 •➡*[g] U0 →
                           #{L0, T0} < #{L ,T} →
                           ⦃h, L0⦄ ⊩ U0 :[g]
                        ) →
                        ∀L0,T0. ⦃h, L0⦄ ⊩ T0 :[g] →
                        ∀U0,l. ⦃h, L⦄ ⊢ T0 •[g, l + 1] U0 →
                        L0 = L → T0 = T → ⦃h, L0⦄ ⊩ U0 :[g].
#h #g #L #T #IH2 #IH1 #L0 #T0 * -L0 -T0
[
|
|
| #a #L0 #V #W #W0 #T0 #V0 #l0 #HV #HT0 #HVW #HW0 #HTV0 #X #l #H #H1 #H2 destruct
  elim (ssta_inv_appl1 … H) -H #U0 #HTU0 #H destruct
  lapply (IH1 … HT0 U0 ? ?) // [ /3 width=2/ ] -HTU0 #HU0
  @(snv_appl … HV HU0 HVW HW0) -HV -HU0 -HVW -HW0
| #L0 #W #T0 #W0 #l0 #HW #HT0 #HTW0 #HW0 #X #l #H #H1 #H2 destruct
  elim (ssta_inv_cast1 … H) -H <minus_plus_m_m #V #U0 #HWV #HTU0 #H destruct
  elim (ssta_mono … HTU0 … HTW0) -HTU0 #H1 #H2
  lapply (injective_plus_l … H1) -H1 #H1 destruct
(*  elim (ssta_fwd_correct … HTW0) <minus_plus_m_m #X0 #HWX0 *)
  lapply (IH1 … HT0 W0 ? ?) -IH1 -HT0 // [ /3 width=2/ ] -HTW0 #HW0
  @(snv_cast … HV HW0) 
  
  HVW HW0) -HV -HU0 -HVW -HW0  
*)
