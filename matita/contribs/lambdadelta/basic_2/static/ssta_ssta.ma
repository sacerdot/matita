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

include "basic_2/static/da_da.ma".
include "basic_2/static/ssta_lift.ma".

(* STRATIFIED STATIC TYPE ASSIGNMENT ON TERMS *******************************)

(* Advanced inversion lemmas ************************************************)

lemma ssta_inv_refl_pos: ∀h,g,G,L,T,l.  ⦃G, L⦄ ⊢ T ▪[h, g] l+1 → ⦃G, L⦄ ⊢ T •[h, g] T → ⊥.
#h #g #G #L #T #l #H1T #HTT
lapply (ssta_da_conf … HTT … H1T) -HTT <minus_plus_m_m #H2T
lapply (da_mono … H2T … H1T) -h -G -L -T #H
elim (plus_xySz_x_false 0 l 0) //
qed-.

(* Main properties **********************************************************)

theorem ssta_mono: ∀h,g,G,L. singlevalued … (ssta h g G L).
#h #g #G #L #T #U1 #H elim H -G -L -T -U1
[ #G #L #k #X #H >(ssta_inv_sort1 … H) -X //
| #G #L #K #V #U1 #W #i #HLK #_ #HWU1 #IHVW #U2 #H
  elim (ssta_inv_lref1 … H) -H * #K0 #V0 #W0 #HLK0 #HVW0 #HW0U2
  lapply (ldrop_mono … HLK0 … HLK) -HLK -HLK0 #H destruct
  lapply (IHVW … HVW0) -IHVW -HVW0 #H destruct
  >(lift_mono … HWU1 … HW0U2) -W0 -U1 //
| #G #L #K #W #U1 #l #i #HLK #HWl #HWU1 #U2 #H
  elim (ssta_inv_lref1 … H) -H * #K0 #W0 #l0 #HLK0 #HWl0 #HW0U2
  lapply (ldrop_mono … HLK0 … HLK) -HLK -HLK0 #H destruct
  lapply (da_mono … HWl0 … HWl) -HWl0 #H destruct
  >(lift_mono … HWU1 … HW0U2) -W -U1 //
| #a #I #G #L #V #T #U1 #_ #IHTU1 #X #H
  elim (ssta_inv_bind1 … H) -H #U2 #HTU2 #H destruct /3 width=1/
| #G #L #V #T #U1 #_ #IHTU1 #X #H
  elim (ssta_inv_appl1 … H) -H #U2 #HTU2 #H destruct /3 width=1/
| #G #L #W #T #U1 #_ #IHTU1 #U2 #H
  lapply (ssta_inv_cast1 … H) -H /2 width=1/
]
qed-.
