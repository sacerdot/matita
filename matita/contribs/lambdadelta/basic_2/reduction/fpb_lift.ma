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

include "basic_2/reduction/cpx_lift.ma".
include "basic_2/reduction/fpb.ma".

(* "BIG TREE" PARALLEL REDUCTION FOR CLOSURES *******************************)

(* Advanced properties ******************************************************)

lemma sta_fpb: ∀h,g,G,L,T1,T2,l.
                ⦃G, L⦄ ⊢ T1 ▪[h, g] l+1 → ⦃G, L⦄ ⊢ T1 •[h] T2 →
                ⦃G, L, T1⦄ ≽[h, g] ⦃G, L, T2⦄.
/3 width=4 by fpb_cpx, sta_cpx/ qed.
