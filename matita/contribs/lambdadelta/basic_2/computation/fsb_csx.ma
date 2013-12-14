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

include "basic_2/computation/lsx_csx.ma".
include "basic_2/computation/fsb_alt.ma".

axiom lsx_fqup_conf: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊃+ ⦃G2, L2, T2⦄ →
                     G1 ⊢ ⋕⬊*[h, g, T1] L1 → G2 ⊢ ⋕⬊*[h, g, T2] L2.

axiom fqup_lpxs_trans_nlleq: ∀h,g,G1,G2,K1,K2,T1,T2. ⦃G1, K1, T1⦄ ⊃+ ⦃G2, K2, T2⦄ →
                             ∀L2. ⦃G2, K2⦄ ⊢ ➡*[h, g] L2 → (K2 ⋕[O, T2] L2 →⊥) →
                             ∃∃L1. ⦃G1, K1⦄ ⊢ ➡*[h, g] L1 &
                                   K1 ⋕[O, T1] L1 → ⊥ & ⦃G1, L1, T1⦄ ⊃+ ⦃G2, L2, T2⦄.

(* "BIG TREE" STRONGLY NORMALIZING TERMS ************************************)

(* Advanced propreties on context-senstive extended bormalizing terms *******)

lemma csx_fsb: ∀h,g,G,L,T. ⦃G, L⦄ ⊢ ⬊*[h, g] T → ⦃G, L⦄ ⊢ ⦥[h, g] T.
#h #g #G1 #L1 #T1 #H @(csx_ind_alt … H) -T1
#T1 #HT1 @(lsx_ind h g T1 G1 … L1) /2 width=1 by csx_lsx/ -L1
#L1 @(fqup_wf_ind … G1 L1 T1) -G1 -L1 -T1
#G1 #L1 #T1 #IHu #H1 #IHl #IHc @fsb_intro
#G2 #L2 #T2 * -G2 -L2 -T2
[ #G2 #L2 #T2 #H12 @IHu -IHu /2 width=5 by lsx_fqup_conf/ -H1 [| -IHl ]
  [ #L0 #HL20 #HnL20 #_ elim (fqup_lpxs_trans_nlleq … H12 … HL20 HnL20) -L2
    /6 width=5 by fsb_fpbs_trans, lpxs_fpbs, fqup_fpbs, lpxs_cpxs_trans/
  | #T0 #HT20 #HnT20 elim (fqup_cpxs_trans_neq … H12 … HT20 HnT20) -T2
    /4 width=5 by fsb_fpbs_trans, fqup_fpbs/
  ]
| -H1 -IHu -IHl /3 width=1 by/
| -H1 -IHu /5 width=5 by fsb_fpbs_trans, lpxs_fpbs, lpxs_cpxs_trans/
]
qed.

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
                                (∀G2,L2,T2. ⦃G1, L1, T1⦄ >⋕[h, g] ⦃G2, L2, T2⦄ → R G2 L2 T2) →
                                R G1 L1 T1
                    ) →
                    ∀G,L,T. ⦃G, L⦄ ⊢ ⬊*[h, g] T → R G L T.
/4 width=4 by fsb_inv_csx, csx_fsb, fsb_ind_fpbg/ qed-.
