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

include "basic_2/notation/relations/predsnstar_8.ma".
include "basic_2/reduction/fpn.ma".
include "basic_2/computation/lpxs.ma".

(* ORDERED "BIG TREE" NORMAL FORMS ******************************************)

definition fpns: ∀h. sd h → tri_relation genv lenv term ≝
                 λh,g,G1,L1,T1,G2,L2,T2.
                 ∧∧ G1 = G2 & ⦃G1, L1⦄ ⊢ ➡*[h, g] L2 & T1 = T2.

interpretation
   "ordered 'big tree' normal forms (closure)"
   'PRedSnStar h g G1 L1 T1 G2 L2 T2 = (fpns h g G1 L1 T1 G2 L2 T2).

(* Basic_properties *********************************************************)

lemma fpns_refl: ∀h,g. tri_reflexive … (fpns h g).
/2 width=1 by and3_intro/ qed.

lemma fpn_fpns: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊢ ➡[h, g] ⦃G2, L2, T2⦄ →
                ⦃G1, L1, T1⦄ ⊢ ➡*[h, g] ⦃G2, L2, T2⦄.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 * /3 width=1 by lpx_lpxs, and3_intro/
qed.

lemma fpns_strap1: ∀h,g,G1,G,G2,L1,L,L2,T1,T,T2. ⦃G1, L1, T1⦄ ⊢ ➡*[h, g] ⦃G, L, T⦄ →
                   ⦃G, L, T⦄ ⊢ ➡[h, g] ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ ⊢ ➡*[h, g] ⦃G2, L2, T2⦄.
#h #g #G1 #G #G2 #L1 #L #L2 #T1 #T #T2 * #H1G #H1L #G1T *
/3 width=3 by lpxs_strap1, and3_intro/
qed-.

lemma fpns_strap2: ∀h,g,G1,G,G2,L1,L,L2,T1,T,T2. ⦃G1, L1, T1⦄ ⊢ ➡[h, g] ⦃G, L, T⦄ →
                   ⦃G, L, T⦄ ⊢ ➡*[h, g] ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ ⊢ ➡*[h, g] ⦃G2, L2, T2⦄.
#h #g #G1 #G #G2 #L1 #L #L2 #T1 #T #T2 * #H1G #H1L #G1T *
/3 width=3 by lpxs_strap2, and3_intro/
qed-.

(* Basic forward lemmas *****************************************************)

lemma fpns_fwd_bteq: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊢ ➡*[h, g] ⦃G2, L2, T2⦄ →
                     ⦃G1, L1, T1⦄ ⋕ ⦃G2, L2, T2⦄.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 * /3 width=4 by lpxs_fwd_length, and3_intro/
qed-.
