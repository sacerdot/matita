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

include "basic_2/computation/lpxs_lleq.ma".
include "basic_2/computation/lpxs_lpxs.ma".
include "basic_2/computation/lsx.ma".

(* SN EXTENDED STRONGLY NORMALIZING LOCAL ENVIRONMENTS **********************)

(* Advanced properties ******************************************************)

lemma lsx_lleq_trans: ∀h,g,T,G,L1. G ⊢ ⋕⬊*[h, g, T] L1 →
                      ∀L2. L1 ⋕[T, 0] L2 → G ⊢ ⋕⬊*[h, g, T] L2.
#h #g #T #G #L1 #H @(lsx_ind … H) -L1
#L1 #_ #IHL1 #L2 #HL12 @lsx_intro
#K2 #HLK2 #HnLK2 elim (lleq_lpxs_trans … HL12 … HLK2) -HLK2
/5 width=4 by lleq_canc_sn, lleq_trans/
qed-.

lemma lsx_lpxs_trans: ∀h,g,T,G,L1. G ⊢ ⋕⬊*[h, g, T] L1 →
                      ∀L2. ⦃G, L1⦄ ⊢ ➡*[h, g] L2 → G ⊢ ⋕⬊*[h, g, T] L2.
#h #g #T #G #L1 #H @(lsx_ind … H) -L1 #L1 #HL1 #IHL1 #L2 #HL12
elim (lleq_dec T L1 L2 0) /3 width=4 by lsx_lleq_trans/
qed-.

lemma lsx_flat_lpxs: ∀h,g,I,G,L1,V. G ⊢ ⋕⬊*[h, g, V] L1 →
                     ∀L2,T. G ⊢ ⋕⬊*[h, g, T] L2 → ⦃G, L1⦄ ⊢ ➡*[h, g] L2 →
                     G ⊢ ⋕⬊*[h, g, ⓕ{I}T.V] L2.
#h #g #I #G #L1 #V #H @(lsx_ind … H) -L1
#L1 #HL1 #IHL1 #L2 #T #H @(lsx_ind … H) -L2
#L2 #HL2 #IHL2 #HL12 @lsx_intro
#L0 #HL20 lapply (lpxs_trans … HL12 … HL20)
#HL10 #H elim (nlleq_inv_flat … H) -H [ -HL2 -IHL1 | -HL1 -IHL2 ]
[ /3 width=1 by/
| #HnV elim (lleq_dec V L1 L2 0)
  [ #HV @(IHL1 … L0) /3 width=3 by lsx_lpxs_trans, lleq_canc_sn/ (**) (* full auto too slow: 47s *)
  | -HnV -HL10 /3 width=4 by lsx_lpxs_trans/
]
qed-.

lemma lsx_flat: ∀h,g,I,G,L,V. G ⊢ ⋕⬊*[h, g, V] L →
                ∀T. G ⊢ ⋕⬊*[h, g, T] L → G ⊢ ⋕⬊*[h, g, ⓕ{I}T.V] L.
/2 width=3 by lsx_flat_lpxs/ qed.
