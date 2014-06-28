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

include "basic_2/multiple/lleq_lleq.ma".
include "basic_2/reduction/lpx_lleq.ma".
include "basic_2/computation/lsx.ma".

(* SN EXTENDED STRONGLY NORMALIZING LOCAL ENVIRONMENTS **********************)

(* Advanced properties ******************************************************)

lemma lsx_lleq_trans: ∀h,g,T,G,L1,d. G ⊢ ⬊*[h, g, T, d] L1 →
                      ∀L2. L1 ≡[T, d] L2 → G ⊢ ⬊*[h, g, T, d] L2.
#h #g #T #G #L1 #d #H @(lsx_ind … H) -L1
#L1 #_ #IHL1 #L2 #HL12 @lsx_intro
#K2 #HLK2 #HnLK2 elim (lleq_lpx_trans … HLK2 … HL12) -HLK2
/5 width=4 by lleq_canc_sn, lleq_trans/
qed-.

lemma lsx_lpx_trans: ∀h,g,T,G,L1,d. G ⊢ ⬊*[h, g, T, d] L1 →
                     ∀L2. ⦃G, L1⦄ ⊢ ➡[h, g] L2 → G ⊢ ⬊*[h, g, T, d] L2.
#h #g #T #G #L1 #d #H @(lsx_ind … H) -L1 #L1 #HL1 #IHL1 #L2 #HL12
elim (lleq_dec T L1 L2 d) /3 width=4 by lsx_lleq_trans/
qed-.

lemma lsx_leq_conf: ∀h,g,G,L1,T,d. G ⊢ ⬊*[h, g, T, d] L1 →
                    ∀L2. L1 ⩬[d, ∞] L2 → G ⊢ ⬊*[h, g, T, d] L2.
#h #g #G #L1 #T #d #H @(lsx_ind … H) -L1
#L1 #_ #IHL1 #L2 #HL12 @lsx_intro
#L3 #HL23 #HnL23 elim (leq_lpx_trans_lleq … HL12 … HL23) -HL12 -HL23
#L0 #HL03 #HL10 #H elim (H T) -H /4 width=4 by/
qed-.

(* Advanced forward lemmas **************************************************)

lemma lsx_fwd_bind_dx: ∀h,g,a,I,G,L,V,T,d. G ⊢ ⬊*[h, g, ⓑ{a,I}V.T, d] L →
                       G ⊢ ⬊*[h, g, T, ⫯d] L.ⓑ{I}V.
#h #g #a #I #G #L #V1 #T #d #H @(lsx_ind … H) -L
#L1 #_ #IHL1 @lsx_intro
#Y #H #HT elim (lpx_inv_pair1 … H) -H
#L2 #V2 #HL12 #_ #H destruct
@(lsx_leq_conf … (L2.ⓑ{I}V1)) /2 width=1 by leq_succ/
@IHL1 // #H @HT -IHL1 -HL12 -HT
@(lleq_leq_trans … (L2.ⓑ{I}V1))
/2 width=2 by lleq_fwd_bind_dx, leq_succ/
qed-.

(* Advanced inversion lemmas ************************************************)

lemma lsx_inv_bind: ∀h,g,a,I,G,L,V,T,d. G ⊢ ⬊*[h, g, ⓑ{a, I}V.T, d] L →
                    G ⊢ ⬊*[h, g, V, d] L ∧ G ⊢ ⬊*[h, g, T, ⫯d] L.ⓑ{I}V.
/3 width=4 by lsx_fwd_bind_sn, lsx_fwd_bind_dx, conj/ qed-.
