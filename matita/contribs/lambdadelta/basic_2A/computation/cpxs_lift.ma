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

include "basic_2A/multiple/fqus_fqus.ma".
include "basic_2A/reduction/cpx_lift.ma".
include "basic_2A/computation/cpxs.ma".

(* CONTEXT-SENSITIVE EXTENDED PARALLEL COMPUTATION ON TERMS *****************)

(* Advanced properties ******************************************************)

lemma cpxs_delta: ∀h,g,I,G,L,K,V,V2,i.
                  ⬇[i] L ≡ K.ⓑ{I}V → ⦃G, K⦄ ⊢ V ➡*[h, g] V2 →
                  ∀W2. ⬆[0, i+1] V2 ≡ W2 → ⦃G, L⦄ ⊢ #i ➡*[h, g] W2.
#h #g #I #G #L #K #V #V2 #i #HLK #H elim H -V2
[ /3 width=9 by cpx_cpxs, cpx_delta/
| #V1 lapply (drop_fwd_drop2 … HLK) -HLK
  elim (lift_total V1 0 (i+1)) /4 width=12 by cpx_lift, cpxs_strap1/
]
qed.

lemma lstas_cpxs: ∀h,g,G,L,T1,T2,d2. ⦃G, L⦄ ⊢ T1 •*[h, d2] T2 →
                  ∀d1. ⦃G, L⦄ ⊢ T1 ▪[h, g] d1 → d2 ≤ d1 → ⦃G, L⦄ ⊢ T1 ➡*[h, g] T2.
#h #g #G #L #T1 #T2 #d2 #H elim H -G -L -T1 -T2 -d2 //
[ /3 width=3 by cpxs_sort, da_inv_sort/
| #G #L #K #V1 #V2 #W2 #i #d2 #HLK #_ #HVW2 #IHV12 #d1 #H #Hd21
  elim (da_inv_lref … H) -H * #K0 #V0 [| #d0 ] #HLK0
  lapply (drop_mono … HLK0 … HLK) -HLK0 #H destruct /3 width=7 by cpxs_delta/
| #G #L #K #V1 #V2 #W2 #i #d2 #HLK #_ #HVW2 #IHV12 #d1 #H #Hd21
  elim (da_inv_lref … H) -H * #K0 #V0 [| #d0 ] #HLK0
  lapply (drop_mono … HLK0 … HLK) -HLK0 #H destruct
  #HV1 #H destruct lapply (le_plus_to_le_r … Hd21) -Hd21
  /3 width=7 by cpxs_delta/
| /4 width=3 by cpxs_bind_dx, da_inv_bind/
| /4 width=3 by cpxs_flat_dx, da_inv_flat/
| /4 width=3 by cpxs_eps, da_inv_flat/
]
qed.

(* Advanced inversion lemmas ************************************************)

lemma cpxs_inv_lref1: ∀h,g,G,L,T2,i. ⦃G, L⦄ ⊢ #i ➡*[h, g] T2 →
                      T2 = #i ∨
                      ∃∃I,K,V1,T1. ⬇[i] L ≡ K.ⓑ{I}V1 & ⦃G, K⦄ ⊢ V1 ➡*[h, g] T1 &
                                   ⬆[0, i+1] T1 ≡ T2.
#h #g #G #L #T2 #i #H @(cpxs_ind … H) -T2 /2 width=1 by or_introl/
#T #T2 #_ #HT2 *
[ #H destruct
  elim (cpx_inv_lref1 … HT2) -HT2 /2 width=1 by or_introl/
  * /4 width=7 by cpx_cpxs, ex3_4_intro, or_intror/
| * #I #K #V1 #T1 #HLK #HVT1 #HT1
  lapply (drop_fwd_drop2 … HLK) #H0LK
  elim (cpx_inv_lift1 … HT2 … H0LK … HT1) -H0LK -T
  /4 width=7 by cpxs_strap1, ex3_4_intro, or_intror/
]
qed-.

(* Relocation properties ****************************************************)

lemma cpxs_lift: ∀h,g,G. d_liftable (cpxs h g G).
/3 width=10 by cpx_lift, cpxs_strap1, d_liftable_LTC/ qed.

lemma cpxs_inv_lift1: ∀h,g,G. d_deliftable_sn (cpxs h g G).
/3 width=6 by d_deliftable_sn_LTC, cpx_inv_lift1/
qed-.

(* Properties on supclosure *************************************************)

lemma fqu_cpxs_trans: ∀h,g,G1,G2,L1,L2,T2,U2. ⦃G2, L2⦄ ⊢ T2 ➡*[h, g] U2 →
                      ∀T1. ⦃G1, L1, T1⦄ ⊐ ⦃G2, L2, T2⦄ →
                      ∃∃U1. ⦃G1, L1⦄ ⊢ T1 ➡*[h, g] U1 & ⦃G1, L1, U1⦄ ⊐ ⦃G2, L2, U2⦄.
#h #g #G1 #G2 #L1 #L2 #T2 #U2 #H @(cpxs_ind_dx … H) -T2 /2 width=3 by ex2_intro/
#T #T2 #HT2 #_ #IHTU2 #T1 #HT1 elim (fqu_cpx_trans … HT1 … HT2) -T
#T #HT1 #HT2 elim (IHTU2 … HT2) -T2 /3 width=3 by cpxs_strap2, ex2_intro/
qed-.

lemma fquq_cpxs_trans: ∀h,g,G1,G2,L1,L2,T2,U2. ⦃G2, L2⦄ ⊢ T2 ➡*[h, g] U2 →
                       ∀T1. ⦃G1, L1, T1⦄ ⊐⸮ ⦃G2, L2, T2⦄ →
                       ∃∃U1. ⦃G1, L1⦄ ⊢ T1 ➡*[h, g] U1 & ⦃G1, L1, U1⦄ ⊐⸮ ⦃G2, L2, U2⦄.
#h #g #G1 #G2 #L1 #L2 #T2 #U2 #HTU2 #T1 #H elim (fquq_inv_gen … H) -H
[ #HT12 elim (fqu_cpxs_trans … HTU2 … HT12) /3 width=3 by fqu_fquq, ex2_intro/
| * #H1 #H2 #H3 destruct /2 width=3 by ex2_intro/
]
qed-.

lemma fquq_lstas_trans: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐⸮ ⦃G2, L2, T2⦄ →
                        ∀U2,d1. ⦃G2, L2⦄ ⊢ T2 •*[h, d1] U2 →
                        ∀d2. ⦃G2, L2⦄ ⊢ T2 ▪[h, g] d2 → d1 ≤ d2 →
                        ∃∃U1. ⦃G1, L1⦄ ⊢ T1 ➡*[h, g] U1 & ⦃G1, L1, U1⦄ ⊐⸮ ⦃G2, L2, U2⦄.
/3 width=5 by fquq_cpxs_trans, lstas_cpxs/ qed-.

lemma fqup_cpxs_trans: ∀h,g,G1,G2,L1,L2,T2,U2. ⦃G2, L2⦄ ⊢ T2 ➡*[h, g] U2 →
                       ∀T1. ⦃G1, L1, T1⦄ ⊐+ ⦃G2, L2, T2⦄ →
                       ∃∃U1. ⦃G1, L1⦄ ⊢ T1 ➡*[h, g] U1 & ⦃G1, L1, U1⦄ ⊐+ ⦃G2, L2, U2⦄.
#h #g #G1 #G2 #L1 #L2 #T2 #U2 #H @(cpxs_ind_dx … H) -T2 /2 width=3 by ex2_intro/
#T #T2 #HT2 #_ #IHTU2 #T1 #HT1 elim (fqup_cpx_trans … HT1 … HT2) -T
#U1 #HTU1 #H2 elim (IHTU2 … H2) -T2 /3 width=3 by cpxs_strap2, ex2_intro/
qed-.

lemma fqus_cpxs_trans: ∀h,g,G1,G2,L1,L2,T2,U2. ⦃G2, L2⦄ ⊢ T2 ➡*[h, g] U2 →
                       ∀T1. ⦃G1, L1, T1⦄ ⊐* ⦃G2, L2, T2⦄ →
                       ∃∃U1. ⦃G1, L1⦄ ⊢ T1 ➡*[h, g] U1 & ⦃G1, L1, U1⦄ ⊐* ⦃G2, L2, U2⦄.
#h #g #G1 #G2 #L1 #L2 #T2 #U2 #HTU2 #T1 #H elim (fqus_inv_gen … H) -H
[ #HT12 elim (fqup_cpxs_trans … HTU2 … HT12) /3 width=3 by fqup_fqus, ex2_intro/
| * #H1 #H2 #H3 destruct /2 width=3 by ex2_intro/
]
qed-.

lemma fqus_lstas_trans: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐* ⦃G2, L2, T2⦄ →
                        ∀U2,d1. ⦃G2, L2⦄ ⊢ T2 •*[h, d1] U2 →
                        ∀d2. ⦃G2, L2⦄ ⊢ T2 ▪[h, g] d2 → d1 ≤ d2 →
                        ∃∃U1. ⦃G1, L1⦄ ⊢ T1 ➡*[h, g] U1 & ⦃G1, L1, U1⦄ ⊐* ⦃G2, L2, U2⦄.
/3 width=6 by fqus_cpxs_trans, lstas_cpxs/ qed-.
