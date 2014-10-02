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

include "basic_2/computation/csx_fpbs.ma".
include "basic_2/computation/lsx_csx.ma".
include "basic_2/computation/fsb_alt.ma".

(* "QRST" STRONGLY NORMALIZING TERMS ****************************************)

(* Advanced propreties on context-sensitive extended normalizing terms ******)

lemma csx_fsb_fpbs: ∀h,g,G1,L1,T1. ⦃G1, L1⦄ ⊢ ⬊*[h, g] T1 →
                    ∀G2,L2,T2. ⦃G1, L1, T1⦄ ≥[h, g] ⦃G2, L2, T2⦄ → ⦃G2, L2⦄ ⊢ ⦥[h, g] T2.
#h #g #G1 #L1 #T1 #H @(csx_ind … H) -T1
#T1 #HT1 #IHc #G2 #L2 #T2 @(fqup_wf_ind … G2 L2 T2) -G2 -L2 -T2
#G0 #L0 #T0 #IHu #H10 lapply (csx_fpbs_conf … H10) // -HT1
#HT0 generalize in match IHu; -IHu generalize in match H10; -H10
@(lsx_ind … (csx_lsx … HT0 0)) -L0
#L0 #_ #IHl #H10 #IHu @fsb_intro
#G2 #L2 #T2 * -G2 -L2 -T2 [ -IHl -IHc | -IHu -IHl |  ]
[ /4 width=5 by fpbs_fqup_trans, fqu_fqup/
| #T2 #HT02 #HnT02 elim (fpbs_cpx_trans_neq … H10 … HT02 HnT02) -T0
  /3 width=4 by/
| #L2 #HL02 #HnL02 @(IHl … HL02 HnL02) -IHl -HnL02 [ -IHu -IHc | ]
  [ /3 width=3 by fpbs_lpxs_trans, lpx_lpxs/
  | #G3 #L3 #T3 #H03 #_ elim (lpx_fqup_trans … H03 … HL02) -L2
    #L4 #T4 elim (eq_term_dec T0 T4) [ -IHc | -IHu ]
    [ #H destruct /5 width=5 by fsb_fpbs_trans, lpxs_fpbs, fpbs_fqup_trans, lpx_lpxs/
    | #HnT04 #HT04 #H04 #HL43 elim (cpxs_neq_inv_step_sn … HT04 HnT04) -HT04 -HnT04
      #T2 #HT02 #HnT02 #HT24 elim (fpbs_cpx_trans_neq … H10 … HT02 HnT02) -T0
      lapply (fpbs_intro_alt … G3 … L4 … L3 L3 … T3 … HT24 ? ? ?) -HT24
      /3 width=8 by fpbs_trans, lpx_lpxs, fqup_fqus/ (**) (* full auto too slow *)
    ]
  ]
]
qed.

lemma csx_fsb: ∀h,g,G,L,T. ⦃G, L⦄ ⊢ ⬊*[h, g] T → ⦃G, L⦄ ⊢ ⦥[h, g] T.
/2 width=5 by csx_fsb_fpbs/ qed.

(* Advanced eliminators *****************************************************)

lemma csx_ind_fpbu: ∀h,g. ∀R:relation3 genv lenv term.
                    (∀G1,L1,T1. ⦃G1, L1⦄ ⊢ ⬊*[h, g] T1 →
                                (∀G2,L2,T2. ⦃G1, L1, T1⦄ ≻[h, g] ⦃G2, L2, T2⦄ → R G2 L2 T2) →
                                R G1 L1 T1
                    ) →
                    ∀G,L,T. ⦃G, L⦄ ⊢ ⬊*[h, g] T → R G L T.
/4 width=4 by fsb_inv_csx, csx_fsb, fsb_ind_alt/ qed-.

lemma csx_ind_fpbg: ∀h,g. ∀R:relation3 genv lenv term.
                    (∀G1,L1,T1. ⦃G1, L1⦄ ⊢ ⬊*[h, g] T1 →
                                (∀G2,L2,T2. ⦃G1, L1, T1⦄ >≡[h, g] ⦃G2, L2, T2⦄ → R G2 L2 T2) →
                                R G1 L1 T1
                    ) →
                    ∀G,L,T. ⦃G, L⦄ ⊢ ⬊*[h, g] T → R G L T.
/4 width=4 by fsb_inv_csx, csx_fsb, fsb_ind_fpbg/ qed-.
