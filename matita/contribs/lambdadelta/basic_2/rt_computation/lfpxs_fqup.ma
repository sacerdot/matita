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

include "basic_2/rt_transition/lfpx_fqup.ma".
include "basic_2/rt_computation/lfpxs.ma".

(* UNCOUNTED PARALLEL RT-COMPUTATION FOR LOCAL ENV.S ON REFERRED ENTRIES ****)

(* Advanced eliminators *****************************************************)

(* Basic_2A1: was just: lpxs_ind *)
lemma lfpxs_ind: ∀h,G,L1,T. ∀R:predicate lenv. R L1 →
                 (∀L,L2. ⦃G, L1⦄ ⊢ ⬈*[h, T] L → ⦃G, L⦄ ⊢ ⬈[h, T] L2 → R L → R L2) →
                 ∀L2. ⦃G, L1⦄ ⊢ ⬈*[h, T] L2 → R L2.
#h #G #L1 #T #R #HL1 #IHL1 #L2 #HL12
@(TC_star_ind … HL1 IHL1 … HL12) //
qed-.

(* Basic_2A1: was just: lpxs_ind_dx *)
lemma lfpxs_ind_dx: ∀h,G,L2,T. ∀R:predicate lenv. R L2 →
                    (∀L1,L. ⦃G, L1⦄ ⊢ ⬈[h, T] L → ⦃G, L⦄ ⊢ ⬈*[h, T] L2 → R L → R L1) →
                    ∀L1. ⦃G, L1⦄ ⊢ ⬈*[h, T] L2 → R L1.
#h #o #G #L2 #R #HL2 #IHL2 #L1 #HL12
@(TC_star_ind_dx … HL2 IHL2 … HL12) //
qed-.

(* Advanced properties ******************************************************)

(* Basic_2A1: was just: lpxs_refl *)
lemma lfpxs_refl: ∀h,G,L,T. ⦃G, L⦄ ⊢ ⬈*[h, T] L.
/2 width=1 by lfpx_lfpxs/ qed.
