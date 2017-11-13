
include "basic_2/static/lfxs_lfxs.ma".
include "basic_2/rt_transition/lfpx_frees.ma".
include "basic_2/rt_computation/lfpxs_fqup.ma".

axiom cpx_frees_conf_lfpxs: ∀h,G,L1,T1,T2. ⦃G, L1⦄ ⊢ T1 ⬈[h] T2 →
                            ∀f1. L1 ⊢ 𝐅*⦃T1⦄ ≡ f1 →
                            ∀L2. ⦃G, L1⦄ ⊢ ⬈*[h, T1] L2 →
                            ∀g1. L2 ⊢ 𝐅*⦃T1⦄ ≡ g1 →
                            ∃∃g2. L2 ⊢ 𝐅*⦃T2⦄ ≡ g2 & g2 ⊆ g1 & g1 ⊆ f1.

lemma lfpxs_cpx_conf: ∀h,G. s_r_confluent1 … (cpx h G) (lfpxs h G).
#h #G #L1 #T1 #T2 #HT12 #L2 #H
lapply (cpx_frees_conf_lfpxs … HT12) -HT12 #HT12
@(lfpxs_ind_sn … H) -L2 //
#L #L2 #HL1 * #g1 #Hg1 #HL2 #IH
elim (frees_total L1 T1) #f1 #Hf1
elim (HT12 … Hf1 …  HL1 … Hg1) -T1 #g2 #Hg2 #Hg21 #_ -f1
/4 width=7 by lfpxs_step_dx, sle_lexs_trans, ex2_intro/
qed-.
