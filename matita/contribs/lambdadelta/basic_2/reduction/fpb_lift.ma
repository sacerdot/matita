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

include "basic_2/unfold/lstas_da.ma".
include "basic_2/reduction/cpx_lift.ma".
include "basic_2/reduction/fpb.ma".

(* "RST" PROPER PARALLEL COMPUTATION FOR CLOSURES ***************************)

(* Advanced properties ******************************************************)

lemma sta_fpb: ∀h,o,G,L,T1,T2,d. ⦃G, L⦄ ⊢ T1 ▪[h, o] d+1 →
               ⦃G, L⦄ ⊢ T1 •*[h, 1] T2 → ⦃G, L, T1⦄ ≻[h, o] ⦃G, L, T2⦄.
#h #o #G #L #T1 #T2 #d #HT1 #HT12 elim (eq_term_dec T1 T2)
/3 width=2 by fpb_cpx, sta_cpx/ #H destruct
elim (lstas_inv_refl_pos h G L T2 0) //
qed.
