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

include "basic_2A/computation/fpbs_aaa.ma".
include "basic_2A/computation/csx_aaa.ma".
include "basic_2A/computation/fsb_csx.ma".

(* "QRST" STRONGLY NORMALIZING CLOSURES *************************************)

(* Main properties **********************************************************)

(* Note: this is the "big tree" theorem ("RST" version) *)
theorem aaa_fsb: ∀h,g,G,L,T,A. ⦃G, L⦄ ⊢ T ⁝ A → ⦥[h, g] ⦃G, L, T⦄.
/3 width=2 by aaa_csx, csx_fsb/ qed.

(* Note: this is the "big tree" theorem ("QRST" version) *)
theorem aaa_fsba: ∀h,g,G,L,T,A. ⦃G, L⦄ ⊢ T ⁝ A → ⦥⦥[h, g] ⦃G, L, T⦄.
/3 width=2 by fsb_fsba, aaa_fsb/ qed.

(* Advanced eliminators on atomica arity assignment for terms ***************)

fact aaa_ind_fpb_aux: ∀h,g. ∀R:relation3 genv lenv term.
                      (∀G1,L1,T1,A. ⦃G1, L1⦄ ⊢ T1 ⁝ A →
                                    (∀G2,L2,T2. ⦃G1, L1, T1⦄ ≻[h, g] ⦃G2, L2, T2⦄ → R G2 L2 T2) →
                                    R G1 L1 T1
                      ) →
                      ∀G,L,T. ⦃G, L⦄ ⊢ ⬊*[h, g] T → ∀A. ⦃G, L⦄ ⊢ T ⁝ A → R G L T.
#h #g #R #IH #G #L #T #H @(csx_ind_fpb … H) -G -L -T
#G1 #L1 #T1 #H1 #IH1 #A1 #HTA1 @IH -IH //
#G2 #L2 #T2 #H12 elim (fpbs_aaa_conf h g … G2 … L2 … T2 … HTA1) -A1
/2 width=2 by fpb_fpbs/
qed-.

lemma aaa_ind_fpb: ∀h,g. ∀R:relation3 genv lenv term.
                   (∀G1,L1,T1,A. ⦃G1, L1⦄ ⊢ T1 ⁝ A →
                                 (∀G2,L2,T2. ⦃G1, L1, T1⦄ ≻[h, g] ⦃G2, L2, T2⦄ → R G2 L2 T2) →
                                 R G1 L1 T1
                   ) →
                   ∀G,L,T,A. ⦃G, L⦄ ⊢ T ⁝ A → R G L T.
/4 width=4 by aaa_ind_fpb_aux, aaa_csx/ qed-.

fact aaa_ind_fpbg_aux: ∀h,g. ∀R:relation3 genv lenv term.
                       (∀G1,L1,T1,A. ⦃G1, L1⦄ ⊢ T1 ⁝ A →
                                     (∀G2,L2,T2. ⦃G1, L1, T1⦄ >≡[h, g] ⦃G2, L2, T2⦄ → R G2 L2 T2) →
                                     R G1 L1 T1
                       ) →
                       ∀G,L,T. ⦃G, L⦄ ⊢ ⬊*[h, g] T → ∀A. ⦃G, L⦄ ⊢ T ⁝ A → R G L T.
#h #g #R #IH #G #L #T #H @(csx_ind_fpbg … H) -G -L -T
#G1 #L1 #T1 #H1 #IH1 #A1 #HTA1 @IH -IH //
#G2 #L2 #T2 #H12 elim (fpbs_aaa_conf h g … G2 … L2 … T2 … HTA1) -A1
/2 width=2 by fpbg_fwd_fpbs/
qed-.

lemma aaa_ind_fpbg: ∀h,g. ∀R:relation3 genv lenv term.
                    (∀G1,L1,T1,A. ⦃G1, L1⦄ ⊢ T1 ⁝ A →
                                  (∀G2,L2,T2. ⦃G1, L1, T1⦄ >≡[h, g] ⦃G2, L2, T2⦄ → R G2 L2 T2) →
                                  R G1 L1 T1
                    ) →
                    ∀G,L,T,A. ⦃G, L⦄ ⊢ T ⁝ A → R G L T.
/4 width=4 by aaa_ind_fpbg_aux, aaa_csx/ qed-.
