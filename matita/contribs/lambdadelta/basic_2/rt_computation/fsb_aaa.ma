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

include "basic_2/rt_computation/csx_aaa.ma".
include "basic_2/rt_computation/fpbs_aaa.ma".
include "basic_2/rt_computation/fpbs_fpb.ma".
include "basic_2/rt_computation/fsb_csx.ma".

(* STRONGLY NORMALIZING CLOSURES FOR PARALLEL RST-TRANSITION ****************)

(* Main properties with atomic arity assignment for terms *******************)

(* Note: this is the "big tree" theorem *)
theorem aaa_fsb: ∀h,o,G,L,T,A. ⦃G, L⦄ ⊢ T ⁝ A → ≥[h, o] 𝐒⦃G, L, T⦄.
/3 width=2 by aaa_csx, csx_fsb/ qed.

(* Advanced eliminators with atomic arity assignment for terms **************)

fact aaa_ind_fpb_aux: ∀h,o. ∀Q:relation3 ….
                      (∀G1,L1,T1,A. ⦃G1, L1⦄ ⊢ T1 ⁝ A →
                                    (∀G2,L2,T2. ⦃G1, L1, T1⦄ ≻[h, o] ⦃G2, L2, T2⦄ → Q G2 L2 T2) →
                                    Q G1 L1 T1
                      ) →
                      ∀G,L,T. ⦃G, L⦄ ⊢ ⬈*[h, o] 𝐒⦃T⦄ → ∀A. ⦃G, L⦄ ⊢ T ⁝ A →  Q G L T.
#h #o #R #IH #G #L #T #H @(csx_ind_fpb … H) -G -L -T
#G1 #L1 #T1 #H1 #IH1 #A1 #HTA1 @IH -IH //
#G2 #L2 #T2 #H12 elim (fpbs_aaa_conf h o … G2 … L2 … T2 … HTA1) -A1
/2 width=2 by fpb_fpbs/
qed-.

lemma aaa_ind_fpb: ∀h,o. ∀Q:relation3 ….
                   (∀G1,L1,T1,A. ⦃G1, L1⦄ ⊢ T1 ⁝ A →
                                 (∀G2,L2,T2. ⦃G1, L1, T1⦄ ≻[h, o] ⦃G2, L2, T2⦄ → Q G2 L2 T2) →
                                 Q G1 L1 T1
                   ) →
                   ∀G,L,T,A. ⦃G, L⦄ ⊢ T ⁝ A → Q G L T.
/4 width=4 by aaa_ind_fpb_aux, aaa_csx/ qed-.

fact aaa_ind_fpbg_aux: ∀h,o. ∀Q:relation3 ….
                       (∀G1,L1,T1,A. ⦃G1, L1⦄ ⊢ T1 ⁝ A →
                                     (∀G2,L2,T2. ⦃G1, L1, T1⦄ >[h, o] ⦃G2, L2, T2⦄ → Q G2 L2 T2) →
                                     Q G1 L1 T1
                       ) →
                       ∀G,L,T. ⦃G, L⦄ ⊢ ⬈*[h, o] 𝐒⦃T⦄ → ∀A. ⦃G, L⦄ ⊢ T ⁝ A →  Q G L T.
#h #o #Q #IH #G #L #T #H @(csx_ind_fpbg … H) -G -L -T
#G1 #L1 #T1 #H1 #IH1 #A1 #HTA1 @IH -IH //
#G2 #L2 #T2 #H12 elim (fpbs_aaa_conf h o … G2 … L2 … T2 … HTA1) -A1
/2 width=2 by fpbg_fwd_fpbs/
qed-.

lemma aaa_ind_fpbg: ∀h,o. ∀Q:relation3 ….
                    (∀G1,L1,T1,A. ⦃G1, L1⦄ ⊢ T1 ⁝ A →
                                  (∀G2,L2,T2. ⦃G1, L1, T1⦄ >[h, o] ⦃G2, L2, T2⦄ → Q G2 L2 T2) →
                                  Q G1 L1 T1
                    ) →
                    ∀G,L,T,A. ⦃G, L⦄ ⊢ T ⁝ A → Q G L T.
/4 width=4 by aaa_ind_fpbg_aux, aaa_csx/ qed-.
