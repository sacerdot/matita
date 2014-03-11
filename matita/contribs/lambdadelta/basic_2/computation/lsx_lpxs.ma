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

include "basic_2/relocation/lleq_lleq.ma".
include "basic_2/computation/lpxs_lleq.ma".
include "basic_2/computation/lpxs_lpxs.ma".
include "basic_2/computation/lsx.ma".

(* SN EXTENDED STRONGLY NORMALIZING LOCAL ENVIRONMENTS **********************)

(* Advanced properties ******************************************************)

lemma lsx_leq_conf: ∀h,g,G,L1,T,d. G ⊢ ⋕⬊*[h, g, T, d] L1 →
                    ∀L2. L1 ≃[d, ∞] L2 → G ⊢ ⋕⬊*[h, g, T, d] L2.
#h #g #G #L1 #T #d #H @(lsx_ind … H) -L1
#L1 #_ #IHL1 #L2 #HL12 @lsx_intro
#L3 #HL23 #HnL23 elim (leq_lpxs_trans_lleq … HL12 … HL23) -HL12 -HL23
#L0 #HL03 #HL10 #H elim (H T) -H /4 width=4 by/
qed-.

lemma lsx_ge: ∀h,g,G,L,T,d1,d2. d1 ≤ d2 →
              G ⊢ ⋕⬊*[h, g, T, d1] L → G ⊢ ⋕⬊*[h, g, T, d2] L.
#h #g #G #L #T #d1 #d2 #Hd12 #H @(lsx_ind … H) -L
/5 width=7 by lsx_intro, lleq_ge/
qed-.

lemma lsx_lleq_trans: ∀h,g,T,G,L1,d. G ⊢ ⋕⬊*[h, g, T, d] L1 →
                      ∀L2. L1 ⋕[T, d] L2 → G ⊢ ⋕⬊*[h, g, T, d] L2.
#h #g #T #G #L1 #d #H @(lsx_ind … H) -L1
#L1 #_ #IHL1 #L2 #HL12 @lsx_intro
#K2 #HLK2 #HnLK2 elim (lleq_lpxs_trans … HLK2 … HL12) -HLK2
/5 width=4 by lleq_canc_sn, lleq_trans/
qed-.

lemma lsx_lpxs_trans: ∀h,g,T,G,L1,d. G ⊢ ⋕⬊*[h, g, T, d] L1 →
                      ∀L2. ⦃G, L1⦄ ⊢ ➡*[h, g] L2 → G ⊢ ⋕⬊*[h, g, T, d] L2.
#h #g #T #G #L1 #d #H @(lsx_ind … H) -L1 #L1 #HL1 #IHL1 #L2 #HL12
elim (lleq_dec T L1 L2 d) /3 width=4 by lsx_lleq_trans/
qed-.

fact lsx_bind_lpxs_aux: ∀h,g,a,I,G,L1,V,d. G ⊢ ⋕⬊*[h, g, V, d] L1 →
                        ∀Y,T. G ⊢ ⋕⬊*[h, g, T, ⫯d] Y →
                        ∀L2. Y = L2.ⓑ{I}V → ⦃G, L1⦄ ⊢ ➡*[h, g] L2 →
                        G ⊢ ⋕⬊*[h, g, ⓑ{a,I}V.T, d] L2.
#h #g #a #I #G #L1 #V #d #H @(lsx_ind … H) -L1
#L1 #HL1 #IHL1 #Y #T #H @(lsx_ind … H) -Y
#Y #HY #IHY #L2 #H #HL12 destruct @lsx_intro
#L0 #HL20 lapply (lpxs_trans … HL12 … HL20)
#HL10 #H elim (nlleq_inv_bind … H) -H [ -HL1 -IHY | -HY -IHL1 ]
[ #HnV elim (lleq_dec V L1 L2 d)
  [ #HV @(IHL1 … L0) /3 width=5 by lsx_lpxs_trans, lpxs_pair, lleq_canc_sn/ (**) (* full auto too slow *)
  | -HnV -HL10 /4 width=5 by lsx_lpxs_trans, lpxs_pair/
  ]
| /3 width=4 by lpxs_pair/
]
qed-.

lemma lsx_bind: ∀h,g,a,I,G,L,V,d. G ⊢ ⋕⬊*[h, g, V, d] L →
                ∀T. G ⊢ ⋕⬊*[h, g, T, ⫯d] L.ⓑ{I}V →
                G ⊢ ⋕⬊*[h, g, ⓑ{a,I}V.T, d] L.
/2 width=3 by lsx_bind_lpxs_aux/ qed.

lemma lsx_flat_lpxs: ∀h,g,I,G,L1,V,d. G ⊢ ⋕⬊*[h, g, V, d] L1 →
                     ∀L2,T. G ⊢ ⋕⬊*[h, g, T, d] L2 → ⦃G, L1⦄ ⊢ ➡*[h, g] L2 →
                     G ⊢ ⋕⬊*[h, g, ⓕ{I}V.T, d] L2.
#h #g #I #G #L1 #V #d #H @(lsx_ind … H) -L1
#L1 #HL1 #IHL1 #L2 #T #H @(lsx_ind … H) -L2
#L2 #HL2 #IHL2 #HL12 @lsx_intro
#L0 #HL20 lapply (lpxs_trans … HL12 … HL20)
#HL10 #H elim (nlleq_inv_flat … H) -H [ -HL1 -IHL2 | -HL2 -IHL1 ]
[ #HnV elim (lleq_dec V L1 L2 d)
  [ #HV @(IHL1 … L0) /3 width=3 by lsx_lpxs_trans, lleq_canc_sn/ (**) (* full auto too slow: 47s *)
  | -HnV -HL10 /3 width=4 by lsx_lpxs_trans/
  ]
| /3 width=1 by/
]
qed-.

lemma lsx_flat: ∀h,g,I,G,L,V,d. G ⊢ ⋕⬊*[h, g, V, d] L →
                ∀T. G ⊢ ⋕⬊*[h, g, T, d] L → G ⊢ ⋕⬊*[h, g, ⓕ{I}V.T, d] L.
/2 width=3 by lsx_flat_lpxs/ qed.

(* Advanced forward lemmas **************************************************)

lemma lsx_fwd_lref_be: ∀h,g,I,G,L,d,i. d ≤ yinj i → G ⊢ ⋕⬊*[h, g, #i, d] L →
                       ∀K,V. ⇩[i] L ≡ K.ⓑ{I}V → G ⊢ ⋕⬊*[h, g, V, 0] K.
#h #g #I #G #L #d #i #Hdi #H @(lsx_ind … H) -L
#L1 #_ #IHL1 #K1 #V #HLK1 @lsx_intro
#K2 #HK12 #HnK12 lapply (ldrop_fwd_drop2 … HLK1)
#H2LK1 elim (ldrop_lpxs_trans … H2LK1 … HK12) -H2LK1 -HK12
#L2 #HL12 #H2LK2 #H elim (leq_ldrop_conf_be … H … HLK1) -H /2 width=1 by ylt_inj/
#Y #_ #HLK2 lapply (ldrop_fwd_drop2 … HLK2)
#HY lapply (ldrop_mono … HY … H2LK2) -HY -H2LK2 #H destruct
/4 width=10 by lleq_inv_lref_ge/
qed-.

lemma lsx_fwd_bind_dx: ∀h,g,a,I,G,L,V,T,d. G ⊢ ⋕⬊*[h, g, ⓑ{a,I}V.T, d] L →
                       G ⊢ ⋕⬊*[h, g, T, ⫯d] L.ⓑ{I}V.
#h #g #a #I #G #L #V1 #T #d #H @(lsx_ind … H) -L
#L1 #_ #IHL1 @lsx_intro
#Y #H #HT elim (lpxs_inv_pair1 … H) -H
#L2 #V2 #HL12 #_ #H destruct
@(lsx_leq_conf … (L2.ⓑ{I}V1)) /2 width=1 by leq_succ/
@IHL1 // #H @HT -IHL1 -HL12 -HT
@(lleq_leq_trans … (L2.ⓑ{I}V1))
/2 width=2 by lleq_fwd_bind_dx, leq_succ/
qed-.

(* Advanced inversion lemmas ************************************************)

lemma lsx_inv_bind: ∀h,g,a,I,G,L,V,T,d. G ⊢ ⋕⬊*[h, g, ⓑ{a, I}V.T, d] L →
                    G ⊢ ⋕⬊*[h, g, V, d] L ∧ G ⊢ ⋕⬊*[h, g, T, ⫯d] L.ⓑ{I}V.
/3 width=4 by lsx_fwd_bind_sn, lsx_fwd_bind_dx, conj/ qed-.
