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
include "basic_2/reduction/fpb.ma".
include "basic_2/computation/csx.ma".

(* "QRST" STRONGLY NORMALIZING CLOSURES *************************************)

inductive fsb (h) (o): relation3 genv lenv term ≝
| fsb_intro: ∀G1,L1,T1. (
                ∀G2,L2,T2. ⦃G1, L1, T1⦄ ≻[h, o] ⦃G2, L2, T2⦄ → fsb h o G2 L2 T2
             ) → fsb h o G1 L1 T1
.

interpretation
   "'qrst' strong normalization (closure)"
   'BTSN h o G L T = (fsb h o G L T).

(* Basic eliminators ********************************************************)

lemma fsb_ind_alt: ∀h,o. ∀R: relation3 …. (
                      ∀G1,L1,T1. ⦥[h,o] ⦃G1, L1, T1⦄ → (
                         ∀G2,L2,T2. ⦃G1, L1, T1⦄ ≻[h, o] ⦃G2, L2, T2⦄ → R G2 L2 T2
                      ) → R G1 L1 T1
                   ) →
                   ∀G,L,T. ⦥[h, o] ⦃G, L, T⦄ → R G L T.
#h #o #R #IH #G #L #T #H elim H -G -L -T
/4 width=1 by fsb_intro/
qed-.

(* Basic inversion lemmas ***************************************************)

lemma fsb_inv_csx: ∀h,o,G,L,T. ⦥[h, o] ⦃G, L, T⦄ → ⦃G, L⦄ ⊢ ⬊*[h, o] T.
#h #o #G #L #T #H elim H -G -L -T /5 width=1 by csx_intro, fpb_cpx/
qed-.
