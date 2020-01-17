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

include "basic_2A/unfold/lstas_lift.ma".

(* NAT-ITERATED STATIC TYPE ASSIGNMENT FOR TERMS ****************************)

(* Main properties **********************************************************)

theorem lstas_trans: ∀h,G,L,T1,T,d1. ⦃G, L⦄ ⊢ T1 •*[h, d1] T →
                     ∀T2,d2. ⦃G, L⦄ ⊢ T •*[h, d2] T2 → ⦃G, L⦄ ⊢ T1 •*[h, d1+d2] T2.
#h #G #L #T1 #T #d1 #H elim H -G -L -T1 -T -d1
[ #G #L #d1 #k #X #d2 #H >(lstas_inv_sort1 … H) -X
  <iter_plus /2 width=1 by lstas_sort/
| #G #L #K #V1 #V #U #i #d1 #HLK #_ #HVU #IHV1 #U2 #d2 #HU2
  lapply (drop_fwd_drop2 … HLK) #H0
  elim (lstas_inv_lift1 … HU2 … H0 … HVU)
  /3 width=6 by lstas_ldef/
| //
| #G #L #K #W1 #W #U #i #d1 #HLK #_ #HWU #IHW1 #U2 #d2 #HU2
  lapply (drop_fwd_drop2 … HLK) #H0
  elim (lstas_inv_lift1 … HU2 … H0 … HWU)
  /3 width=6 by lstas_succ/
| #a #I #G #L #V #T1 #T #d1 #_ #IHT1 #X #d2 #H
  elim (lstas_inv_bind1 … H) -H #T2 #HT2 #H destruct
  /3 width=1 by lstas_bind/
| #G #L #V #T1 #T #d1 #_ #IHT1 #X #d2 #H
  elim (lstas_inv_appl1 … H) -H #T2 #HT2 #H destruct
  /3 width=1 by lstas_appl/
| /3 width=1 by lstas_cast/
]
qed-.

(* Note: apparently this was missing in basic_1 *)
theorem lstas_mono: ∀h,G,L,d. singlevalued … (lstas h d G L).
#h #G #L #d #T #T1 #H elim H -G -L -T -T1 -d
[ #G #L #d #k #X #H >(lstas_inv_sort1 … H) -X //
| #G #L #K #V #V1 #U1 #i #d #HLK #_ #HVU1 #IHV1 #X #H
  elim (lstas_inv_lref1 … H) -H *
  #K0 #V0 #W0 [3: #d0 ] #HLK0
  lapply (drop_mono … HLK0 … HLK) -HLK -HLK0 #H destruct
  #HVW0 #HX lapply (IHV1 … HVW0) -IHV1 -HVW0 #H destruct
  /2 width=5 by lift_mono/
| #G #L #K #W #W1 #i #HLK #_ #_ #X #H
  elim (lstas_inv_lref1_O … H) -H *
  #K0 #V0 #W0 #HLK0
  lapply (drop_mono … HLK0 … HLK) -HLK -HLK0 #H destruct //
| #G #L #K #W #W1 #U1 #i #d #HLK #_ #HWU1 #IHWV #X #H
  elim (lstas_inv_lref1_S … H) -H * #K0 #W0 #V0 #HLK0
  lapply (drop_mono … HLK0 … HLK) -HLK -HLK0 #H destruct
  #HW0 #HX lapply (IHWV … HW0) -IHWV -HW0 #H destruct
  /2 width=5 by lift_mono/
| #a #I #G #L #V #T #U1 #d #_ #IHTU1 #X #H
  elim (lstas_inv_bind1 … H) -H #U2 #HTU2 #H destruct /3 width=1 by eq_f/
| #G #L #V #T #U1 #d #_ #IHTU1 #X #H
  elim (lstas_inv_appl1 … H) -H #U2 #HTU2 #H destruct /3 width=1 by eq_f/
| #G #L #W #T #U1 #d #_ #IHTU1 #U2 #H
  lapply (lstas_inv_cast1 … H) -H /2 width=1 by/
]
qed-.

(* Advanced inversion lemmas ************************************************)

(* Basic_1: was just: sty0_correct *)
lemma lstas_correct: ∀h,G,L,T1,T,d1. ⦃G, L⦄ ⊢ T1 •*[h, d1] T →
                     ∀d2. ∃T2. ⦃G, L⦄ ⊢ T •*[h, d2] T2.
#h #G #L #T1 #T #d1 #H elim H -G -L -T1 -T -d1
[ /2 width=2 by lstas_sort, ex_intro/
| #G #L #K #V1 #V #U #i #d #HLK #_ #HVU #IHV1 #d2
  elim (IHV1 d2) -IHV1 #V2
  elim (lift_total V2 0 (i+1))
  lapply (drop_fwd_drop2 … HLK) -HLK
  /3 width=11 by ex_intro, lstas_lift/
| #G #L #K #W1 #W #i #HLK #HW1 #IHW1 #d2
  @(nat_ind_plus … d2) -d2 /3 width=5 by lstas_zero, ex_intro/
  #d2 #_ elim (IHW1 d2) -IHW1 #W2 #HW2
  lapply (lstas_trans … HW1 … HW2) -W
  elim (lift_total W2 0 (i+1))
  /3 width=7 by lstas_succ, ex_intro/
| #G #L #K #W1 #W #U #i #d #HLK #_ #HWU #IHW1 #d2
  elim (IHW1 d2) -IHW1 #W2
  elim (lift_total W2 0 (i+1))
  lapply (drop_fwd_drop2 … HLK) -HLK
  /3 width=11 by ex_intro, lstas_lift/
| #a #I #G #L #V #T #U #d #_ #IHTU #d2
  elim (IHTU d2) -IHTU /3 width=2 by lstas_bind, ex_intro/
| #G #L #V #T #U #d #_ #IHTU #d2
  elim (IHTU d2) -IHTU /3 width=2 by lstas_appl, ex_intro/
| #G #L #W #T #U #d #_ #IHTU #d2
  elim (IHTU d2) -IHTU /2 width=2 by ex_intro/
]
qed-.

(* more main properties *****************************************************)

theorem lstas_conf_le: ∀h,G,L,T,U1,d1. ⦃G, L⦄ ⊢ T •*[h, d1] U1 →
                       ∀U2,d2. d1 ≤ d2 → ⦃G, L⦄ ⊢ T •*[h, d2] U2 →
                       ⦃G, L⦄ ⊢ U1 •*[h, d2-d1] U2.
#h #G #L #T #U1 #d1 #HTU1 #U2 #d2 #Hd12
>(plus_minus_m_m … Hd12) in ⊢ (%→?); -Hd12 >commutative_plus #H
elim (lstas_split … H) -H #U #HTU
>(lstas_mono … HTU … HTU1) -T //
qed-.

theorem lstas_conf: ∀h,G,L,T0,T1,d1. ⦃G, L⦄ ⊢ T0 •*[h, d1] T1 →
                    ∀T2,d2. ⦃G, L⦄ ⊢ T0 •*[h, d2] T2 →
                    ∃∃T. ⦃G, L⦄ ⊢ T1 •*[h, d2] T & ⦃G, L⦄ ⊢ T2 •*[h, d1] T.
#h #G #L #T0 #T1 #d1 #HT01 #T2 #d2 #HT02
elim (lstas_lstas … HT01 (d1+d2)) #T #HT0
lapply (lstas_conf_le … HT01 … HT0) // -HT01 <minus_plus_m_m_commutative
lapply (lstas_conf_le … HT02 … HT0) // -T0 <minus_plus_m_m
/2 width=3 by ex2_intro/
qed-.
