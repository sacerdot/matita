
include "basic_2/static/lfxs_lex.ma".
include "basic_2/static/lfxs_fle.ma".
include "basic_2/rt_transition/cpx_etc.ma".
include "basic_2/rt_computation/lfpxs_lpxs.ma".

lemma lfpxs_cpx_conf: ∀h,G. s_r_confluent1 … (cpx h G) (lfpxs h G).
#h #G #L1 #T1 #T2 #HT12 #L2 #H
elim (tc_lfxs_inv_lex_lfeq … H) -H #L #HL1 #HL2
lapply (lfxs_lex … HL1 T1) #H
elim (cpx_lfxs_conf_fle … HT12 … H) -HT12 -H // #_ #HT21 #_
@(lfpxs_lpxs_lfeq … HL1) -HL1
@(fle_lfxs_trans … HL2) //
qed-.
