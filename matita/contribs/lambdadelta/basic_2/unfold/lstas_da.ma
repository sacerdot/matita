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
include "basic_2/unfold/lstas_lstas.ma".

(* NAT-ITERATED STATIC TYPE ASSIGNMENT FOR TERMS ****************************)

(* Properties on degree assignment for terms ********************************)

lemma da_lstas: ∀h,g,G,L,T,l1. ⦃G, L⦄ ⊢ T ▪[h, g] l1 → ∀l2.
                ∃∃U. ⦃G, L⦄ ⊢ T •*[h, l2] U & ⦃G, L⦄ ⊢ U ▪[h, g] l1-l2.
#h #g #G #L #T #l1 #H elim H -G -L -T -l1
[ /4 width=3 by da_sort, deg_iter, ex2_intro/
| #G #L #K #V #i #l1 #HLK #_ #IHV #l2
  elim (IHV l2) -IHV #W
  elim (lift_total W 0 (i+1))
  lapply (drop_fwd_drop2 … HLK)
  /3 width=10 by lstas_ldef, da_lift, ex2_intro/
| #G #L #K #W #i #l1 #HLK #HW #IHW #l2 @(nat_ind_plus … l2) -l2
  [ elim (IHW 0) -IHW /3 width=6 by lstas_zero, da_ldec, ex2_intro/
  | #l #_ elim (IHW l) -IHW #V
    elim (lift_total V 0 (i+1))
    lapply (drop_fwd_drop2 … HLK)
    /3 width=10 by lstas_succ, da_lift, ex2_intro/
  ]
| #a #I #G #L #V #T #l1 #_ #IHT #l2 elim (IHT … l2) -IHT
  /3 width=6 by lstas_bind, da_bind, ex2_intro/
| * #G #L #V #T #l1 #_ #IHT #l2 elim (IHT … l2) -IHT
  /3 width=5 by lstas_appl, lstas_cast, da_flat, ex2_intro/
]
qed-.

lemma lstas_da_conf: ∀h,g,G,L,T,U,l2. ⦃G, L⦄ ⊢ T •*[h, l2] U →
                     ∀l1. ⦃G, L⦄ ⊢ T ▪[h, g] l1 → ⦃G, L⦄ ⊢ U ▪[h, g] l1-l2.
#h #g #G #L #T #U #l2 #HTU #l1 #HT
elim (da_lstas … HT l2) -HT #X #HTX
lapply (lstas_mono … HTX … HTU) -T //
qed-.

(* inversion lemmas on degree assignment for terms **************************)

lemma lstas_inv_da: ∀h,g,G,L,T,U,l2. ⦃G, L⦄ ⊢ T •*[h, l2] U →
                    ∃∃l1. ⦃G, L⦄ ⊢ T ▪[h, g] l1 & ⦃G, L⦄ ⊢ U ▪[h, g] l1-l2.
#h #g #G #L #T #U #l2 #H elim H -G -L -T -U -l2
[ #G #L #l2 #k elim (deg_total h g k) /4 width=3 by da_sort, deg_iter, ex2_intro/
| #G #L #K #V #W #U #i #l2 #HLK #_ #HWU *
  lapply (drop_fwd_drop2 … HLK) /3 width=10 by da_lift, da_ldef, ex2_intro/
| #G #L #K #W #V #i #HLK #_ * /3 width=6 by da_ldec, ex2_intro/
| #G #L #K #W #V #U #i #l2 #HLK #_ #HVU *
  lapply (drop_fwd_drop2 … HLK) /3 width=10 by da_lift, da_ldec, ex2_intro/
| #a #I #G #L #V #T #U #l2 #_ * /3 width=3 by da_bind, ex2_intro/
| #G #L #V #T #U #l2 #_ * /3 width=3 by da_flat, ex2_intro/
| #G #L #W #T #U #l2 #_ * /3 width=3 by da_flat, ex2_intro/
]
qed-.

lemma lstas_inv_da_ge: ∀h,G,L,T,U,l2,l. ⦃G, L⦄ ⊢ T •*[h, l2] U →
                       ∃∃g,l1. ⦃G, L⦄ ⊢ T ▪[h, g] l1 & ⦃G, L⦄ ⊢ U ▪[h, g] l1-l2 & l ≤ l1.
#h #G #L #T #U #l2 #l #H elim H -G -L -T -U -l2
[ /4 width=5 by da_sort, deg_iter, ex3_2_intro/
| #G #L #K #V #W #U #i #l2 #HLK #_ #HWU *
  lapply (drop_fwd_drop2 … HLK) /3 width=10 by da_lift, da_ldef, ex3_2_intro/
| #G #L #K #W #V #i #HLK #_ * 
  #g #l1 #HW #HV #Hl1 /4 width=6 by da_ldec, lt_to_le, le_S_S, ex3_2_intro/
| #G #L #K #W #V #U #i #l2 #HLK #_ #HVU *
  lapply (drop_fwd_drop2 … HLK)
  /4 width=10 by da_lift, da_ldec, lt_to_le, le_S_S, ex3_2_intro/
| #a #I #G #L #V #T #U #l2 #_ * /3 width=5 by da_bind, ex3_2_intro/
| #G #L #V #T #U #l2 #_ * /3 width=5 by da_flat, ex3_2_intro/
| #G #L #W #T #U #l2 #_ * /3 width=5 by da_flat, ex3_2_intro/
]
qed-.

(* Advanced inversion lemmas ************************************************)

lemma lstas_inv_refl_pos: ∀h,G,L,T,l. ⦃G, L⦄ ⊢ T •*[h, l+1] T → ⊥.
#h #G #L #T #l2 #H elim (lstas_inv_da_ge … (l2+1) H) -H
#g #l1 #HT1 #HT12 #Hl21 lapply (da_mono … HT1 … HT12) -h -G -L -T
#H elim (discr_x_minus_xy … H) -H
[ #H destruct /2 width=3 by le_plus_xSy_O_false/
| -l1 <plus_n_Sm #H destruct 
]
qed-.
