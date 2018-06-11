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
include "basic_2/dynamic/nv_aaa.ma".

(* NATIVE VALIDITY FOR TERMS ************************************************)

(* Forward lemmas with strongly rst-normalizing closures ********************)

(* Basic_2A1: uses: snv_fwd_fsb *)
lemma nv_fwd_fsb (a) (h) (o): ∀G,L,T. ⦃G, L⦄ ⊢ T ![a, h] → ≥[h, o] 𝐒⦃G, L, T⦄.
#a #h #o #G #L #T #H elim (nv_fwd_aaa … H) -H /2 width=2 by aaa_fsb/
qed-.
