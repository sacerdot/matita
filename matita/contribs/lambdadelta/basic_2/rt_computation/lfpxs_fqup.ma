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

include "basic_2/i_static/tc_lfxs_fqup.ma".
include "basic_2/rt_computation/lfpxs.ma".

(* UNCOUNTED PARALLEL RT-COMPUTATION FOR LOCAL ENV.S ON REFERRED ENTRIES ****)

(* Advanced properties ******************************************************)

lemma lfpxs_refl: ∀h,G,T. reflexive … (lfpxs h G T).
/2 width=1 by tc_lfxs_refl/ qed.

(* Advanced forward lemmas **************************************************)

lemma lfpxs_fwd_bind_dx: ∀h,p,I,G,L1,L2,V,T. ⦃G, L1⦄ ⊢ ⬈*[h, ⓑ{p,I}V.T] L2 →
                         ⦃G, L1.ⓑ{I}V⦄ ⊢ ⬈*[h, T] L2.ⓑ{I}V.
/2 width=2 by tc_lfxs_fwd_bind_dx/ qed-.

lemma lfpxs_fwd_bind_dx_void: ∀h,p,I,G,L1,L2,V,T. ⦃G, L1⦄ ⊢ ⬈*[h, ⓑ{p,I}V.T] L2 →
                              ⦃G, L1.ⓧ⦄ ⊢ ⬈*[h, T] L2.ⓧ.
/2 width=4 by tc_lfxs_fwd_bind_dx_void/ qed-.

(* Advanced eliminators *****************************************************)

(* Basic_2A1: uses: lpxs_ind *)
lemma lfpxs_ind_sn: ∀h,G,L1,T. ∀R:predicate lenv. R L1 →
                    (∀L,L2. ⦃G, L1⦄ ⊢ ⬈*[h, T] L → ⦃G, L⦄ ⊢ ⬈[h, T] L2 → R L → R L2) →
                    ∀L2. ⦃G, L1⦄ ⊢ ⬈*[h, T] L2 → R L2.
#h #G @tc_lfxs_ind_sn // (**) (* auto fails *)
qed-. 

(* Basic_2A1: uses: lpxs_ind_dx *)
lemma lfpxs_ind_dx: ∀h,G,L2,T. ∀R:predicate lenv. R L2 →
                    (∀L1,L. ⦃G, L1⦄ ⊢ ⬈[h, T] L → ⦃G, L⦄ ⊢ ⬈*[h, T] L2 → R L → R L1) →
                    ∀L1. ⦃G, L1⦄ ⊢ ⬈*[h, T] L2 → R L1.
#h #G @tc_lfxs_ind_dx // (**) (* auto fails *)
qed-. 
