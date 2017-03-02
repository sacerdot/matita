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

include "basic_2/syntax/tdeq_tdeq.ma".
include "basic_2/rt_transition/lfpx_lfdeq.ma".
include "basic_2/rt_computation/csx.ma".

(* STRONGLY NORMALIZING TERMS FOR UNCOUNTED PARALLEL RT-TRANSITION **********)

(* Advanced properties ******************************************************)

lemma csx_tdeq_trans: ∀h,o,G,L,T1. ⦃G, L⦄ ⊢ ⬈[h, o] 𝐒⦃T1⦄ →
                      ∀T2. T1 ≡[h, o] T2 → ⦃G, L⦄ ⊢ ⬈[h, o] 𝐒⦃T2⦄.
#h #o #G #L #T1 #H @(csx_ind … H) -T1 #T #_ #IH #T2 #HT2
@csx_intro #T1 #HT21 #HnT21 elim (tdeq_cpx_trans … HT2 … HT21) -HT21
/4 width=5 by tdeq_repl/
qed-.

lemma csx_cpx_trans: ∀h,o,G,L,T1. ⦃G, L⦄ ⊢ ⬈[h, o] 𝐒⦃T1⦄ →
                     ∀T2. ⦃G, L⦄ ⊢ T1 ⬈[h] T2 → ⦃G, L⦄ ⊢ ⬈[h, o] 𝐒⦃T2⦄.
#h #o #G #L #T1 #H @(csx_ind … H) -T1 #T1 #HT1 #IHT1 #T2 #HLT12
elim (tdeq_dec h o T1 T2) /3 width=4 by csx_tdeq_trans/
qed-.

(* Basic_1: was just: sn3_cast *)
lemma csx_cast: ∀h,o,G,L,W. ⦃G, L⦄ ⊢ ⬈[h, o] 𝐒⦃W⦄ →
                ∀T. ⦃G, L⦄ ⊢ ⬈[h, o] 𝐒⦃T⦄ → ⦃G, L⦄ ⊢ ⬈[h, o] 𝐒⦃ⓝW.T⦄.
#h #o #G #L #W #HW @(csx_ind … HW) -W
#W #HW #IHW #T #HT @(csx_ind … HT) -T
#T #HT #IHT @csx_intro
#X #H1 #H2 elim (cpx_inv_cast1 … H1) -H1
[ * #W0 #T0 #HLW0 #HLT0 #H destruct
  elim (tdeq_false_inv_pair … H2) -H2
  [ -W -T #H elim H -H //
  | -HW -IHT /3 width=3 by csx_cpx_trans/
  | -HW -HT -IHW /4 width=3 by csx_cpx_trans, cpx_pair_sn/
  ]
|*: /3 width=3 by csx_cpx_trans/
]
qed.
