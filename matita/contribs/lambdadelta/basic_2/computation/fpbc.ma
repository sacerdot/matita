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

include "basic_2/notation/relations/lazybtpredproper_8.ma".
include "basic_2/multiple/fleq.ma".
include "basic_2/computation/fpbu.ma".

(* SINGLE-STEP "BIG TREE" PROPER PARALLEL COMPUTATION FOR CLOSURES **********)

definition fpbc: ∀h. sd h → tri_relation genv lenv term ≝
                 λh,g,G1,L1,T1,G2,L2,T2.
                 ∃∃G,L,T. ⦃G1, L1, T1⦄ ≻[h, g] ⦃G, L, T⦄ & ⦃G, L, T⦄ ≡[0] ⦃G2, L2, T2⦄.

interpretation
   "single-step 'big tree' proper parallel reduction (closure)"
   'LazyBTPRedProper h g G1 L1 T1 G2 L2 T2 = (fpbc h g G1 L1 T1 G2 L2 T2).

(* Baic properties **********************************************************)

lemma fpbu_fpbc: ∀h,g,G1,G2,L1,L2,T1,T2.
                 ⦃G1, L1, T1⦄ ≻[h, g] ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ ≻≡[h, g] ⦃G2, L2, T2⦄.
/2 width=5 by ex2_3_intro/ qed.
