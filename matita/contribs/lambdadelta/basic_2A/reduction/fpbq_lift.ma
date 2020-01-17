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

include "basic_2A/reduction/cpx_lift.ma".
include "basic_2A/reduction/fpbq.ma".

(* "QRST" PARALLEL REDUCTION FOR CLOSURES ***********************************)

(* Advanced properties ******************************************************)

lemma sta_fpbq: ∀h,g,G,L,T1,T2,d.
                 ⦃G, L⦄ ⊢ T1 ▪[h, g] d+1 → ⦃G, L⦄ ⊢ T1 •*[h, 1] T2 →
                 ⦃G, L, T1⦄ ≽[h, g] ⦃G, L, T2⦄.
/3 width=4 by fpbq_cpx, sta_cpx/ qed.
