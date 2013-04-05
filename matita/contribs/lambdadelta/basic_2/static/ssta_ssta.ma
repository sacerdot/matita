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

(* STRATIFIED STATIC TYPE ASSIGNMENT ON TERMS *******************************)

(* Main properties **********************************************************)

(* Note: apparently this was missing in basic_1 *)
theorem ssta_mono: ∀h,g,L,T,U1,l1. ⦃h, L⦄ ⊢ T •[g] ⦃l1, U1⦄ →
                   ∀U2,l2. ⦃h, L⦄ ⊢ T •[g] ⦃l2, U2⦄ → l1 = l2 ∧ U1 = U2.
#h #g #L #T #U1 #l1 #H elim H -L -T -U1 -l1
[ #L #k #l #Hkl #X #l2 #H
  elim (ssta_inv_sort1 … H) -H #Hkl2 #H destruct
  >(deg_mono … Hkl2 … Hkl) -g -L -l2 /2 width=1/
| #L #K #V #W #U1 #i #l1 #HLK #_ #HWU1 #IHVW #U2 #l2 #H
  elim (ssta_inv_lref1 … H) -H * #K0 #V0 #W0 [2: #l0] #HLK0 #HVW0 #HW0U2
  lapply (ldrop_mono … HLK0 … HLK) -HLK -HLK0 #H destruct
  lapply (IHVW … HVW0) -IHVW -HVW0 * #H1 #H2 destruct
  >(lift_mono … HWU1 … HW0U2) -W0 -U1 /2 width=1/
| #L #K #W #V #U1 #i #l1 #HLK #_ #HWU1 #IHWV #U2 #l2 #H
  elim (ssta_inv_lref1 … H) -H * #K0 #W0 #V0 [2: #l0 ] #HLK0 #HWV0 #HV0U2
  lapply (ldrop_mono … HLK0 … HLK) -HLK -HLK0 #H destruct
  lapply (IHWV … HWV0) -IHWV -HWV0 * #H1 #H2 destruct
  >(lift_mono … HWU1 … HV0U2) -W -U1 /2 width=1/
| #a #I #L #V #T #U1 #l1 #_ #IHTU1 #X #l2 #H
  elim (ssta_inv_bind1 … H) -H #U2 #HTU2 #H destruct
  elim (IHTU1 … HTU2) -T /3 width=1/
| #L #V #T #U1 #l1 #_ #IHTU1 #X #l2 #H
  elim (ssta_inv_appl1 … H) -H #U2 #HTU2 #H destruct
  elim (IHTU1 … HTU2) -T /3 width=1/
| #L #W1 #T #U1 #l1 #_ #IHTU1 #U2 #l2 #H
  lapply (ssta_inv_cast1 … H) -H #HTU2
  elim (IHTU1 … HTU2) -T /2 width=1/
]
qed-.

(* Advanced inversion lemmas ************************************************)

lemma ssta_inv_refl_pos: ∀h,g,L,T,l. ⦃h, L⦄ ⊢ T •[g] ⦃l+1, T⦄ → ⊥.
#h #g #L #T #l #HTT
elim (ssta_fwd_correct … HTT) <minus_plus_m_m #U #HTU
elim (ssta_mono … HTU … HTT) -h -L #H #_ -T -U
elim (plus_xySz_x_false 0 l 0 ?) //
qed-.
