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

include "basic_2/notation/relations/btsn_5.ma".
include "basic_2/computation/fpbu.ma".
include "basic_2/computation/csx_alt.ma".

(* "BIG TREE" STRONGLY NORMALIZING TERMS ************************************)

inductive fsb (h) (g): relation3 genv lenv term ≝
| fsb_intro: ∀G1,L1,T1. (
                ∀G2,L2,T2. ⦃G1, L1, T1⦄ ≻[h, g] ⦃G2, L2, T2⦄ → fsb h g G2 L2 T2
             ) → fsb h g G1 L1 T1
.

interpretation
   "'big tree' strong normalization (closure)"
   'BTSN h g G L T = (fsb h g G L T).

(* Basic eliminators ********************************************************)

lemma fsb_ind_alt: ∀h,g. ∀R: relation3 …. (
                      ∀G1,L1,T1. ⦃G1, L1⦄ ⊢ ⦥[h,g] T1 → (
                         ∀G2,L2,T2. ⦃G1, L1, T1⦄ ≻[h, g] ⦃G2, L2, T2⦄ → R G2 L2 T2
                      ) → R G1 L1 T1
                   ) →
                   ∀G,L,T. ⦃G, L⦄ ⊢ ⦥[h, g] T → R G L T.
#h #g #R #IH #G #L #T #H elim H -G -L -T
/4 width=1 by fsb_intro/
qed-.

(* Basic inversion lemmas ***************************************************)

lemma fsb_inv_csx: ∀h,g,G,L,T. ⦃G, L⦄ ⊢ ⦥[h, g] T → ⦃G, L⦄ ⊢ ⬊*[h, g] T.
#h #g #G #L #T #H elim H -G -L -T /5 width=1 by csx_intro_cpxs, fpbu_cpxs/
qed-.
