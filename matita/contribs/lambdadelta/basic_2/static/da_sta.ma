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

include "basic_2/static/sta.ma".
include "basic_2/static/da_da.ma".

(* Properties on static type assignment for terms ***************************)

lemma da_sta_conf: ∀h,g,G,L,T,U. ⦃G, L⦄ ⊢ T •[h] U →
                   ∀l. ⦃G, L⦄ ⊢ T ▪[h, g] l → ⦃G, L⦄ ⊢ U ▪[h, g] l-1.
#h #g #G #L #T #U #H elim H -G -L -T -U
[ #G #L #k #l #H
  lapply (da_inv_sort … H) -H /3 width=1 by da_sort, deg_next/
| #G #L #K #V #U #W #i #HLK #_ #HWU #IHVW #l #H
  elim (da_inv_lref … H) -H * #K0 #V0 [| #l0] #HLK0 #HV0
  lapply (drop_mono … HLK0 … HLK) -HLK0 #H destruct
  lapply (drop_fwd_drop2 … HLK) -HLK /3 width=8 by da_lift/
| #G #L #K #W #V #U #i #HLK #_ #HWU #IHWV #l #H
  elim (da_inv_lref … H) -H * #K0 #V0 [| #l0] #HLK0 #HV0 [| #H0 ]
  lapply (drop_mono … HLK0 … HLK) -HLK0 #H destruct
  lapply (drop_fwd_drop2 … HLK) -HLK /3 width=8 by da_lift/
| #a #I #G #L #V #T #U #_ #IHTU #l #H
  lapply (da_inv_bind … H) -H /3 width=1 by da_bind/
| #G #L #V #T #U #_ #IHTU #l #H
  lapply (da_inv_flat … H) -H /3 width=1 by da_flat/
| #G #L #W #T #U #_ #IHTU #l #H
  lapply (da_inv_flat … H) -H /2 width=1 by/
]
qed-.

lemma sta_da: ∀h,g,G,L,T,U. ⦃G, L⦄ ⊢ T •[h] U →
              ∃l. ⦃G, L⦄ ⊢ T ▪[h, g] l.
#h #g #G #L #T #U #H elim H -G -L -T -U
[ #G #L #k elim (deg_total h g k) /3 width=2 by da_sort, ex_intro/
| #G #L #K #V #W #W0 #i #HLK #_ #_ * /3 width=5 by da_ldef, ex_intro/
| #G #L #K #W #V #W0 #i #HLK #_ #_ * /3 width=5 by da_ldec, ex_intro/
| #a #I #G #L #V #T #U #_ * /3 width=2 by da_bind, ex_intro/
| #G #L #V #T #U #_ * /3 width=2 by da_flat, ex_intro/
| #G #L #W #T #U #_ * /3 width=2 by da_flat, ex_intro/
]
qed-.

lemma sta_da_ge: ∀h,G,L,T,U,l0. ⦃G, L⦄ ⊢ T •[h] U →
                 ∃∃g,l. ⦃G, L⦄ ⊢ T ▪[h, g] l & l0 ≤ l.
#h #G #L #T #U #l0 #H elim H -G -L -T -U
[ /3 width=4 by da_sort, ex2_2_intro/
| #G #L #K #V #W #W0 #i #HLK #_ #_ * /3 width=5 by da_ldef, ex2_2_intro/
| #G #L #K #W #V #W0 #i #HLK #_ #_ * /4 width=5 by da_ldec, lt_to_le, le_S_S, ex2_2_intro/
| #a #I #G #L #V #T #U #_ * /3 width=4 by da_bind, ex2_2_intro/
| #G #L #V #T #U #_ * /3 width=4 by da_flat, ex2_2_intro/
| #G #L #W #T #U #_ * /3 width=4 by da_flat, ex2_2_intro/
]
qed-.

(* Inversion lrmmas on static type assignment for terms *********************)

lemma da_inv_sta: ∀h,g,G,L,T,l. ⦃G, L⦄ ⊢ T ▪[h, g] l →
                  ∃U. ⦃G, L⦄ ⊢ T •[h] U.
#h #g #G #L #T #l #H elim H -G -L -T -l
[ /2 width=2/
| #G #L #K #V #i #l #HLK #_ * #W #HVW
  elim (lift_total W 0 (i+1)) /3 width=7 by sta_ldef, ex_intro/
| #G #L #K #W #i #l #HLK #_ * #V #HWV
  elim (lift_total W 0 (i+1)) /3 width=7 by sta_ldec, ex_intro/
| #a #I #G #L #V #T #l #_ * /3 width=2 by sta_bind, ex_intro/
| * #G #L #V #T #l #_ * /3 width=2 by sta_appl, sta_cast, ex_intro/
]
qed-.

lemma sta_inv_refl_pos: ∀h,g,G,L,T,l. ⦃G, L⦄ ⊢ T ▪[h, g] l+1 → ⦃G, L⦄ ⊢ T •[h] T → ⊥.
#h #g #G #L #T #l #H1T #HTT
lapply (da_sta_conf … HTT … H1T) -HTT <minus_plus_m_m #H2T
lapply (da_mono … H2T … H1T) -h -G -L -T #H
elim (plus_xySz_x_false 0 l 0) //
qed-.
