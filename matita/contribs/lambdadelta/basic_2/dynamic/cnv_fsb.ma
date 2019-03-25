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

include "basic_2/rt_computation/fsb_aaa.ma".
include "basic_2/dynamic/cnv_aaa.ma".

(* CONTEXT-SENSITIVE NATIVE VALIDITY FOR TERMS ******************************)

(* Forward lemmas with strongly rst-normalizing closures ********************)

(* Basic_2A1: uses: snv_fwd_fsb *)
lemma cnv_fwd_fsb (a) (h): ∀G,L,T. ⦃G, L⦄ ⊢ T ![a, h] → ≥[h] 𝐒⦃G, L, T⦄.
#a #h #G #L #T #H elim (cnv_fwd_aaa … H) -H /2 width=2 by aaa_fsb/
qed-.

(* Inversion lemmas with proper parallel rst-computation for closures *******)

lemma cnv_fpbg_refl_false (a) (h) (G) (L) (T):
                          ⦃G, L⦄ ⊢ T ![a,h] → ⦃G, L, T⦄ >[h] ⦃G, L, T⦄ → ⊥.
/3 width=7 by cnv_fwd_fsb, fsb_fpbg_refl_false/ qed-.
