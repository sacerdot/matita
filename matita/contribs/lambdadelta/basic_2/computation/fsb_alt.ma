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
include "basic_2/computation/fpbg.ma".
include "basic_2/computation/fsb.ma".

(* "BIG TREE" STRONGLY NORMALIZING TERMS ************************************)

(* Note: alternative definition of fsb *)
inductive fsba (h) (g): relation3 genv lenv term ≝
| fsba_intro: ∀G1,L1,T1. (
                 ∀G2,L2,T2. ⦃G1, L1, T1⦄ >[h, g] ⦃G2, L2, T2⦄ → fsba h g G2 L2 T2
              ) → fsba h g G1 L1 T1.

interpretation
   "'big tree' strong normalization (closure) alternative"
   'BTSNAlt h g G L T = (fsba h g G L T).

(* Basic eliminators ********************************************************)

theorem fsba_ind_alt: ∀h,g. ∀R: relation3 …. (
                         ∀G1,L1,T1. ⦃G1, L1⦄ ⊢ ⦥⦥[h,g] T1 → (
                            ∀G2,L2,T2. ⦃G1, L1, T1⦄ >[h, g] ⦃G2, L2, T2⦄ → R G2 L2 T2
                         ) → R G1 L1 T1
                      ) →
                      ∀G,L,T. ⦃G, L⦄ ⊢ ⦥⦥[h, g] T → R G L T.
#h #g #R #IH #G #L #T #H elim H -G -L -T
/4 width=1 by fsba_intro/
qed-.

(* Main inversion lemmas ****************************************************)

theorem fsba_inv_fsb: ∀h,g,G,L,T. ⦃G, L⦄ ⊢ ⦥⦥[h, g] T → ⦃G, L⦄ ⊢ ⦥[h, g] T.
#h #g #G #L #T #H @(fsba_ind_alt … H) -G -L -T
/4 width=1 by fsb_intro, fpbc_fpbg/
qed-.
