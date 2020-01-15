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

(* Note: this is the "big tree" theorem *)
(* Basic_2A1: uses: snv_fwd_fsb *)
lemma cnv_fwd_fsb (h) (a):
      ∀G,L,T. ❪G,L❫ ⊢ T ![h,a] → ≥𝐒[h] ❪G,L,T❫.
#h #a #G #L #T #H elim (cnv_fwd_aaa … H) -H /2 width=2 by aaa_fsb/
qed-.

(* Forward lemmas with strongly rt-normalizing terms ************************)

lemma cnv_fwd_csx (h) (a):
      ∀G,L,T. ❪G,L❫ ⊢ T ![h,a] → ❪G,L❫ ⊢ ⬈*𝐒[h] T.
#h #a #G #L #T #H
/3 width=2 by cnv_fwd_fsb, fsb_inv_csx/
qed-.

(* Inversion lemmas with proper parallel rst-computation for closures *******)

lemma cnv_fpbg_refl_false (h) (a):
      ∀G,L,T. ❪G,L❫ ⊢ T ![h,a] → ❪G,L,T❫ >[h] ❪G,L,T❫ → ⊥.
/3 width=7 by cnv_fwd_fsb, fsb_fpbg_refl_false/ qed-.
