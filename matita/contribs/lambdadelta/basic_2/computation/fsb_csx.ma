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

include "basic_2/computation/csx_aaa.ma".
include "basic_2/computation/fsb.ma".

(* "BIG TREE" STRONGLY NORMALIZING TERMS ************************************)

(* Advanced propreties ******************************************************)

lemma csx_fsb: ∀h,g,G,L,T. ⦃G, L⦄ ⊢ ⬊*[h, g] T → ⦃G, L⦄ ⊢ ⦥[h, g] T.
#h #g #G #L #T #H @(csx_ind_fpbc … H) -T /3 width=1 by fsb_intro/
qed.

(* Main properties **********************************************************)

(* Note: this is the "big tree" theorem ("small step" version) *)
theorem aaa_fsb: ∀h,g,G,L,T,A. ⦃G, L⦄ ⊢ T ⁝ A → ⦃G, L⦄ ⊢ ⦥[h, g] T.
/3 width=2 by aaa_csx, csx_fsb/ qed.
