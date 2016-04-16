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

lemma da_lstas: ∀h,g,G,L,T,d1. ⦃G, L⦄ ⊢ T ▪[h, g] d1 → ∀d2.
                ∃∃U. ⦃G, L⦄ ⊢ T •*[h, d2] U & ⦃G, L⦄ ⊢ U ▪[h, g] d1-d2.
#h #g #G #L #T #d1 #H elim H -G -L -T -d1
[ /4 width=3 by da_sort, deg_iter, ex2_intro/
| #G #L #K #V #i #d1 #HLK #_ #IHV #d2
  elim (IHV d2) -IHV #W
  elim (lift_total W 0 (i+1))
  lapply (drop_fwd_drop2 … HLK)
  /3 width=10 by lstas_ldef, da_lift, ex2_intro/
| #G #L #K #W #i #d1 #HLK #HW #IHW #d2 @(nat_ind_plus … d2) -d2
  [ elim (IHW 0) -IHW /3 width=6 by lstas_zero, da_ldec, ex2_intro/
  | #d #_ elim (IHW d) -IHW #V
    elim (lift_total V 0 (i+1))
    lapply (drop_fwd_drop2 … HLK)
    /3 width=10 by lstas_succ, da_lift, ex2_intro/
  ]
| #a #I #G #L #V #T #d1 #_ #IHT #d2 elim (IHT … d2) -IHT
  /3 width=6 by lstas_bind, da_bind, ex2_intro/
| * #G #L #V #T #d1 #_ #IHT #d2 elim (IHT … d2) -IHT
  /3 width=5 by lstas_appl, lstas_cast, da_flat, ex2_intro/
]
qed-.

lemma lstas_da_conf: ∀h,g,G,L,T,U,d2. ⦃G, L⦄ ⊢ T •*[h, d2] U →
                     ∀d1. ⦃G, L⦄ ⊢ T ▪[h, g] d1 → ⦃G, L⦄ ⊢ U ▪[h, g] d1-d2.
#h #g #G #L #T #U #d2 #HTU #d1 #HT
elim (da_lstas … HT d2) -HT #X #HTX
lapply (lstas_mono … HTX … HTU) -T //
qed-.

(* inversion lemmas on degree assignment for terms **************************)

lemma lstas_inv_da: ∀h,g,G,L,T,U,d2. ⦃G, L⦄ ⊢ T •*[h, d2] U →
                    ∃∃d1. ⦃G, L⦄ ⊢ T ▪[h, g] d1 & ⦃G, L⦄ ⊢ U ▪[h, g] d1-d2.
#h #g #G #L #T #U #d2 #H elim H -G -L -T -U -d2
[ #G #L #d2 #k elim (deg_total h g k) /4 width=3 by da_sort, deg_iter, ex2_intro/
| #G #L #K #V #W #U #i #d2 #HLK #_ #HWU *
  lapply (drop_fwd_drop2 … HLK) /3 width=10 by da_lift, da_ldef, ex2_intro/
| #G #L #K #W #V #i #HLK #_ * /3 width=6 by da_ldec, ex2_intro/
| #G #L #K #W #V #U #i #d2 #HLK #_ #HVU *
  lapply (drop_fwd_drop2 … HLK) /3 width=10 by da_lift, da_ldec, ex2_intro/
| #a #I #G #L #V #T #U #d2 #_ * /3 width=3 by da_bind, ex2_intro/
| #G #L #V #T #U #d2 #_ * /3 width=3 by da_flat, ex2_intro/
| #G #L #W #T #U #d2 #_ * /3 width=3 by da_flat, ex2_intro/
]
qed-.

lemma lstas_inv_da_ge: ∀h,G,L,T,U,d2,d. ⦃G, L⦄ ⊢ T •*[h, d2] U →
                       ∃∃g,d1. ⦃G, L⦄ ⊢ T ▪[h, g] d1 & ⦃G, L⦄ ⊢ U ▪[h, g] d1-d2 & d ≤ d1.
#h #G #L #T #U #d2 #d #H elim H -G -L -T -U -d2
[ /4 width=5 by da_sort, deg_iter, ex3_2_intro/
| #G #L #K #V #W #U #i #d2 #HLK #_ #HWU *
  lapply (drop_fwd_drop2 … HLK) /3 width=10 by da_lift, da_ldef, ex3_2_intro/
| #G #L #K #W #V #i #HLK #_ * 
  #g #d1 #HW #HV #Hd1 /4 width=6 by da_ldec, lt_to_le, le_S_S, ex3_2_intro/
| #G #L #K #W #V #U #i #d2 #HLK #_ #HVU *
  lapply (drop_fwd_drop2 … HLK)
  /4 width=10 by da_lift, da_ldec, lt_to_le, le_S_S, ex3_2_intro/
| #a #I #G #L #V #T #U #d2 #_ * /3 width=5 by da_bind, ex3_2_intro/
| #G #L #V #T #U #d2 #_ * /3 width=5 by da_flat, ex3_2_intro/
| #G #L #W #T #U #d2 #_ * /3 width=5 by da_flat, ex3_2_intro/
]
qed-.

(* Advanced inversion lemmas ************************************************)

lemma lstas_inv_refl_pos: ∀h,G,L,T,d. ⦃G, L⦄ ⊢ T •*[h, d+1] T → ⊥.
#h #G #L #T #d2 #H elim (lstas_inv_da_ge … (d2+1) H) -H
#g #d1 #HT1 #HT12 #Hd21 lapply (da_mono … HT1 … HT12) -h -G -L -T
#H elim (discr_x_minus_xy … H) -H
[ #H destruct /2 width=3 by le_plus_xSy_O_false/
| -d1 <plus_n_Sm #H destruct 
]
qed-.
