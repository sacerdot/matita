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

include "basic_2/substitution/fsups_fsups.ma".
include "basic_2/reduction/cpx_lift.ma".
include "basic_2/computation/cpxs.ma".

(* CONTEXT-SENSITIVE EXTENDED PARALLEL COMPUTATION ON TERMS *****************)

(* Advanced properties ******************************************************)

lemma cpxs_delta: ∀h,g,I,G,L,K,V,V2,i.
                  ⇩[0, i] L ≡ K.ⓑ{I}V → ⦃G, K⦄ ⊢ V ➡*[h, g] V2 →
                  ∀W2. ⇧[0, i + 1] V2 ≡ W2 → ⦃G, L⦄ ⊢ #i ➡*[h, g] W2.
#h #g #I #G #L #K #V #V2 #i #HLK #H elim H -V2 [ /3 width=9/ ]
#V1 #V2 #_ #HV12 #IHV1 #W2 #HVW2
lapply (ldrop_fwd_ldrop2 … HLK) -HLK #HLK
elim (lift_total V1 0 (i+1)) /4 width=11 by cpx_lift, cpxs_strap1/
qed.

(* Advanced inversion lemmas ************************************************)

lemma cpxs_inv_lref1: ∀h,g,G,L,T2,i. ⦃G, L⦄ ⊢ #i ➡*[h, g] T2 →
                      T2 = #i ∨
                      ∃∃I,K,V1,T1. ⇩[0, i] L ≡ K.ⓑ{I}V1 & ⦃G, K⦄ ⊢ V1 ➡*[h, g] T1 &
                                   ⇧[0, i + 1] T1 ≡ T2.
#h #g #G #L #T2 #i #H @(cpxs_ind … H) -T2 /2 width=1/
#T #T2 #_ #HT2 *
[ #H destruct
  elim (cpx_inv_lref1 … HT2) -HT2 /2 width=1/
  * /4 width=7/
| * #I #K #V1 #T1 #HLK #HVT1 #HT1
  lapply (ldrop_fwd_ldrop2 … HLK) #H0LK
  elim (cpx_inv_lift1 … HT2 … H0LK … HT1) -H0LK -T /4 width=7/
]
qed-.

(* Relocation properties ****************************************************)

lemma cpxs_lift: ∀h,g,G. l_liftable (cpxs h g G).
/3 width=9/ qed.

lemma cpxs_inv_lift1: ∀h,g,G. l_deliftable_sn (cpxs h g G).
/3 width=5 by l_deliftable_sn_LTC, cpx_inv_lift1/
qed-.

(* Properties on supclosure *************************************************)

lemma fsupq_cpxs_trans: ∀h,g,G1,G2,L1,L2,T2,U2. ⦃G2, L2⦄ ⊢ T2 ➡*[h, g] U2 →
                        ∀T1. ⦃G1, L1, T1⦄ ⊃⸮ ⦃G2, L2, T2⦄ →
                        ∃∃U1. ⦃G1, L1⦄ ⊢ T1 ➡*[h, g] U1 & ⦃G1, L1, U1⦄ ⊃* ⦃G2, L2, U2⦄.
#h #g #G1 #G2 #L1 #L2 #T2 #U2 #H @(cpxs_ind_dx … H) -T2 [ /3 width=3/ ]
#T #T2 #HT2 #_ #IHTU2 #T1 #HT1
elim (fsupq_cpx_trans … HT1 … HT2) -T #T #HT1 #HT2
elim (IHTU2 … HT2) -T2 /3 width=3/
qed-.

lemma fsups_cpxs_trans: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊃* ⦃G2, L2, T2⦄ →
                        ∀U2. ⦃G2, L2⦄ ⊢ T2 ➡*[h, g] U2 →
                        ∃∃U1. ⦃G1, L1⦄ ⊢ T1 ➡*[h, g] U1 & ⦃G1, L1, U1⦄ ⊃* ⦃G2, L2, U2⦄.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 #H @(fsups_ind … H) -G2 -L2 -T2 [ /2 width=3/ ]
#G #G2 #L #L2 #T #T2 #_ #HT2 #IHT1 #U2 #HTU2
elim (fsupq_cpxs_trans … HTU2 … HT2) -T2 #T2 #HT2 #HTU2
elim (IHT1 … HT2) -T #T #HT1 #HT2
lapply (fsups_trans … HT2 … HTU2) -G -L -T2 /2 width=3/
qed-.

lemma fsup_ssta_trans: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊃ ⦃G2, L2, T2⦄ →
                       ∀U2,l. ⦃G2, L2⦄ ⊢ T2 •[h, g] ⦃l+1, U2⦄ →
                       ∃∃U1. ⦃G1, L1⦄ ⊢ T1 ➡[h, g] U1 & ⦃G1, L1, U1⦄ ⊃⸮ ⦃G2, L2, U2⦄.
/3 width=4 by fsup_cpx_trans, ssta_cpx/ qed-.
