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

include "basic_2/notation/relations/btsnalt_5.ma".
include "basic_2/computation/fpbg_fpbs.ma".
include "basic_2/computation/fsb.ma".

(* "QRST" STRONGLY NORMALIZING CLOSURES *************************************)

(* Note: alternative definition of fsb *)
inductive fsba (h) (o): relation3 genv lenv term ≝
| fsba_intro: ∀G1,L1,T1. (
                 ∀G2,L2,T2. ⦃G1, L1, T1⦄ >≡[h, o] ⦃G2, L2, T2⦄ → fsba h o G2 L2 T2
              ) → fsba h o G1 L1 T1.

interpretation
   "'big tree' strong normalization (closure) alternative"
   'BTSNAlt h o G L T = (fsba h o G L T).

(* Basic eliminators ********************************************************)

lemma fsba_ind_alt: ∀h,o. ∀R: relation3 …. (
                       ∀G1,L1,T1. ⦥⦥[h,o] ⦃G1, L1, T1⦄ → (
                          ∀G2,L2,T2. ⦃G1, L1, T1⦄ >≡[h, o] ⦃G2, L2, T2⦄ → R G2 L2 T2
                       ) → R G1 L1 T1
                    ) →
                    ∀G,L,T. ⦥⦥[h, o] ⦃G, L, T⦄ → R G L T.
#h #o #R #IH #G #L #T #H elim H -G -L -T
/4 width=1 by fsba_intro/
qed-.

(* Basic properties *********************************************************)

lemma fsba_fpbs_trans: ∀h,o,G1,L1,T1. ⦥⦥[h, o] ⦃G1, L1, T1⦄ →
                       ∀G2,L2,T2. ⦃G1, L1, T1⦄ ≥[h, o] ⦃G2, L2, T2⦄ → ⦥⦥[h, o] ⦃G2, L2, T2⦄.
#h #o #G1 #L1 #T1 #H @(fsba_ind_alt … H) -G1 -L1 -T1
/4 width=5 by fsba_intro, fpbs_fpbg_trans/
qed-.

(* Main properties **********************************************************)

theorem fsb_fsba: ∀h,o,G,L,T. ⦥[h, o] ⦃G, L, T⦄  → ⦥⦥[h, o] ⦃G, L, T⦄.
#h #o #G #L #T #H @(fsb_ind_alt … H) -G -L -T
#G1 #L1 #T1 #_ #IH @fsba_intro
#G2 #L2 #T2 * /3 width=5 by fsba_fpbs_trans/
qed.

(* Main inversion lemmas ****************************************************)

theorem fsba_inv_fsb: ∀h,o,G,L,T. ⦥⦥[h, o] ⦃G, L, T⦄ → ⦥[h, o] ⦃G, L, T⦄.
#h #o #G #L #T #H @(fsba_ind_alt … H) -G -L -T
/4 width=1 by fsb_intro, fpb_fpbg/
qed-.

(* Advanced properties ******************************************************)

lemma fsb_fpbs_trans: ∀h,o,G1,L1,T1. ⦥[h, o] ⦃G1, L1, T1⦄ →
                      ∀G2,L2,T2. ⦃G1, L1, T1⦄ ≥[h, o] ⦃G2, L2, T2⦄ → ⦥[h, o] ⦃G2, L2, T2⦄.
/4 width=5 by fsba_inv_fsb, fsb_fsba, fsba_fpbs_trans/ qed-.

(* Advanced eliminators *****************************************************)

lemma fsb_ind_fpbg: ∀h,o. ∀R:relation3 genv lenv term.
                    (∀G1,L1,T1. ⦥[h, o] ⦃G1, L1, T1⦄ →
                                (∀G2,L2,T2. ⦃G1, L1, T1⦄ >≡[h, o] ⦃G2, L2, T2⦄ → R G2 L2 T2) →
                                R G1 L1 T1
                    ) →
                    ∀G1,L1,T1. ⦥[h, o] ⦃G1, L1, T1⦄ → R G1 L1 T1.
#h #o #R #IH #G1 #L1 #T1 #H @(fsba_ind_alt h o … G1 L1 T1)
/3 width=1 by fsba_inv_fsb, fsb_fsba/
qed-.
