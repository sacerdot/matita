
include "basic_2/static/lfxs_lex.ma".
include "basic_2/rt_transition/cpx_etc.ma".
include "basic_2/rt_computation/lfpxs_lpxs.ma".

axiom fle_trans: ∀L1,L,T1,T. ⦃L1, T1⦄ ⊆ ⦃L, T⦄ →
                 ∀L2,T2. ⦃L, T⦄ ⊆ ⦃L2, T2⦄ → ⦃L1, T1⦄ ⊆ ⦃L2, T2⦄.  

axiom pippo: ∀h,G,L1,T1,T2.  ⦃G, L1⦄ ⊢ T1 ⬈[h] T2 → ∀L. ⦃G, L1⦄ ⊢⬈[h] L →
             ∧∧ ⦃L, T1⦄ ⊆ ⦃L1, T1⦄ & ⦃L, T2⦄ ⊆ ⦃L, T1⦄ & ⦃L1, T2⦄ ⊆ ⦃L1, T1⦄.
(*
lemma pippos: ∀h,G,L1,L. ⦃G, L1⦄ ⊢⬈*[h] L → ∀T1,T2.  ⦃G, L1⦄ ⊢ T1 ⬈[h] T2 →
              ∧∧ ⦃L, T1⦄ ⊆ ⦃L1, T1⦄ & ⦃L, T2⦄ ⊆ ⦃L, T1⦄.
#h #G #L1 #L #H
lapply (lex_inv_ltc … H) -H // #H
@(TC_star_ind ???????? H) -L //
[ #T1 #T2 #H elim (pippo … H) -H /2 width=3 by conj/
| #L #L0 #HL1 #HL0 #IH #T1 #T2 #HT12
  elim (IH … HT12) -IH #HT1 #HT21
  elim (pippo … T1 T1 … HL0) // #H1 #_ #_
  @conj
  [ @(fle_trans … H1) //
 
*)(*
lemma pippos: ∀h,G,L1,L. ⦃G, L1⦄ ⊢⬈*[h] L → ∀T1,T2.  ⦃G, L1⦄ ⊢ T1 ⬈[h] T2 →
              ∧∧ ⦃L, T1⦄ ⊆ ⦃L1, T1⦄ & ⦃L, T2⦄ ⊆ ⦃L, T1⦄ & ⦃L1, T2⦄ ⊆ ⦃L1, T1⦄.
#h #G #L1 #L #H
lapply (lex_inv_ltc … H) -H // #H
@(TC_star_ind_dx ???????? H) -L1 /2 width=5 by pippo/
#L1 #L0 #HL10 #HL0 #IH #T1 #T2 #HT12
elim (IH … HT12) -IH #HT1 #HT21 #H1T21 
@and3_intro
[2:
*)

axiom pippos: ∀h,G,L1,L. ⦃G, L1⦄ ⊢⬈*[h] L → ∀T1,T2.  ⦃G, L1⦄ ⊢ T1 ⬈[h] T2 →
              ∃∃T. ⦃G, L⦄ ⊢ T1 ⬈[h] T & ⦃L, T2⦄ ⊆ ⦃L, T⦄.

lemma fle_tc_lfxs_trans: ∀h,G,L1,L2,T1. ⦃G, L1⦄ ⊢⬈*[h, T1] L2 →
                         ∀T2. ⦃L1, T2⦄ ⊆ ⦃L1, T1⦄ → ⦃G, L1⦄ ⊢⬈* [h, T2] L2.
#h #G #L1 #L2 #T1 #H
@(TC_star_ind_dx ???????? H) -L1 /2 width=1 by tc_lfxs_refl, lfxs_refl/
#L1 #L #HL1 #_ #IH #T2 #HT21
lapply (fle_lfxs_trans … HT21 … HL1) -HL1 #HL1
@(TC_strap … HL1) @IH -IH


lemma lfpxs_cpx_conf: ∀h,G. s_r_confluent1 … (cpx h G) (lfpxs h G).
#h #G #L1 #T1 #T2 #HT12 #L2 #H
lapply (cpx_fle_comp … HT12) -HT12 #HT21

elim (tc_lfxs_inv_lex_lfeq … H) -H #L #HL1 #HL2
@(lfpxs_lpxs_lfeq … HL1) -HL1


@(fle_lfxs_trans

elim (pippos … HL1 … HT12) -HT12 #T #H #HT21
@(lfpxs_lpxs_lfeq … HL1) -HL1
@(fle_lfxs_trans … HL2) -HL2 //
qed-.


