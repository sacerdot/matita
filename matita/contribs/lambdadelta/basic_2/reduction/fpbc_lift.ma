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

include "basic_2/static/ssta_ssta.ma".
include "basic_2/reduction/cpx_lift.ma".
include "basic_2/reduction/fpbc.ma".

(* "BIG TREE" PROPER PARALLEL REDUCTION FOR CLOSURES ************************)

(* Advanced properties ******************************************************)

lemma ssta_fpbc: ∀h,g,G,L,T1,T2,l. ⦃G, L⦄ ⊢ T1 ▪[h, g] l+1 →
                ⦃G, L⦄ ⊢ T1 •[h, g] T2 → ⦃G, L, T1⦄ ≻[h, g] ⦃G, L, T2⦄.
#h #g #G #L #T1 #T2 #l #HT1 #HT12 elim (eq_term_dec T1 T2)
/3 width=5 by fpbc_cpx, ssta_cpx/ #H destruct
elim (ssta_inv_refl_pos … HT1 … HT12)
qed.
