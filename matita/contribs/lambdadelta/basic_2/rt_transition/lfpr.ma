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

include "basic_2/notation/relations/predsn_5.ma".
include "basic_2/static/lfxs.ma".
include "basic_2/rt_transition/cpr_ext.ma".

(* PARALLEL R-TRANSITION FOR LOCAL ENV.S ON REFERRED ENTRIES ****************)

definition lfpr: sh → genv → relation3 term lenv lenv ≝
                 λh,G. lfxs (cpm 0 h G).

interpretation
   "parallel r-transition on referred entries (local environment)"
   'PRedSn h T G L1 L2 = (lfpr h G T L1 L2).

(* Basic properties ***********************************************************)

lemma lfpr_atom: ∀h,I,G. ⦃G, ⋆⦄ ⊢ ➡[h, ⓪{I}] ⋆.
/2 width=1 by lfxs_atom/ qed.

lemma lfpr_sort: ∀h,I,G,L1,L2,V1,V2,s.
                 ⦃G, L1⦄ ⊢ ➡[h, ⋆s] L2 → ⦃G, L1.ⓑ{I}V1⦄ ⊢ ➡[h, ⋆s] L2.ⓑ{I}V2.
/2 width=1 by lfxs_sort/ qed.

lemma lfpr_pair: ∀h,I,G,L1,L2,V1,V2. ⦃G, L1⦄ ⊢ ➡[h, V1] L2 →
                 ⦃G, L1⦄ ⊢ V1 ➡[h] V2 → ⦃G, L1.ⓑ{I}V1⦄ ⊢ ➡[h, #0] L2.ⓑ{I}V2.
/2 width=1 by lfxs_pair/ qed.

lemma lfpr_lref: ∀h,I1,I2,G,L1,L2,i.
                 ⦃G, L1⦄ ⊢ ➡[h, #i] L2 → ⦃G, L1.ⓘ{I1}⦄ ⊢ ➡[h, #↑i] L2.ⓘ{I2}.
/2 width=1 by lfxs_lref/ qed.

lemma lfpr_gref: ∀h,I1,I2,G,L1,L2,l.
                 ⦃G, L1⦄ ⊢ ➡[h, §l] L2 → ⦃G, L1.ⓘ{I1}⦄ ⊢ ➡[h, §l] L2.ⓘ{I2}.
/2 width=1 by lfxs_gref/ qed.

lemma lfpr_bind_repl_dx: ∀h,I,I1,G,L1,L2,T.
                         ⦃G, L1.ⓘ{I}⦄ ⊢ ➡[h, T] L2.ⓘ{I1} →
                         ∀I2. ⦃G, L1⦄ ⊢ I ➡[h] I2 →
                         ⦃G, L1.ⓘ{I}⦄ ⊢ ➡[h, T] L2.ⓘ{I2}.
/2 width=2 by lfxs_bind_repl_dx/ qed-.

(* Basic inversion lemmas ***************************************************)

(* Basic_2A1: uses: lpr_inv_atom1 *)
lemma lfpr_inv_atom_sn: ∀h,I,G,Y2. ⦃G, ⋆⦄ ⊢ ➡[h, ⓪{I}] Y2 → Y2 = ⋆.
/2 width=3 by lfxs_inv_atom_sn/ qed-.

(* Basic_2A1: uses: lpr_inv_atom2 *)
lemma lfpr_inv_atom_dx: ∀h,I,G,Y1. ⦃G, Y1⦄ ⊢ ➡[h, ⓪{I}] ⋆ → Y1 = ⋆.
/2 width=3 by lfxs_inv_atom_dx/ qed-.

lemma lfpr_inv_sort: ∀h,G,Y1,Y2,s. ⦃G, Y1⦄ ⊢ ➡[h, ⋆s] Y2 →
                     ∨∨ Y1 = ⋆ ∧ Y2 = ⋆
                      | ∃∃I1,I2,L1,L2. ⦃G, L1⦄ ⊢ ➡[h, ⋆s] L2 &
                                       Y1 = L1.ⓘ{I1} & Y2 = L2.ⓘ{I2}.
/2 width=1 by lfxs_inv_sort/ qed-.
(*
lemma lfpr_inv_zero: ∀h,G,Y1,Y2. ⦃G, Y1⦄ ⊢ ➡[h, #0] Y2 →
                     (Y1 = ⋆ ∧ Y2 = ⋆) ∨
                     ∃∃I,L1,L2,V1,V2. ⦃G, L1⦄ ⊢ ➡[h, V1] L2 &
                                      ⦃G, L1⦄ ⊢ V1 ➡[h] V2 &
                                      Y1 = L1.ⓑ{I}V1 & Y2 = L2.ⓑ{I}V2.
/2 width=1 by lfxs_inv_zero/ qed-.
*)
lemma lfpr_inv_lref: ∀h,G,Y1,Y2,i. ⦃G, Y1⦄ ⊢ ➡[h, #↑i] Y2 →
                     ∨∨ Y1 = ⋆ ∧ Y2 = ⋆
                      | ∃∃I1,I2,L1,L2. ⦃G, L1⦄ ⊢ ➡[h, #i] L2 &
                                       Y1 = L1.ⓘ{I1} & Y2 = L2.ⓘ{I2}.
/2 width=1 by lfxs_inv_lref/ qed-.

lemma lfpr_inv_gref: ∀h,G,Y1,Y2,l. ⦃G, Y1⦄ ⊢ ➡[h, §l] Y2 →
                     ∨∨ Y1 = ⋆ ∧ Y2 = ⋆
                      | ∃∃I1,I2,L1,L2. ⦃G, L1⦄ ⊢ ➡[h, §l] L2 &
                                       Y1 = L1.ⓘ{I1} & Y2 = L2.ⓘ{I2}.
/2 width=1 by lfxs_inv_gref/ qed-.

lemma lfpr_inv_bind: ∀h,p,I,G,L1,L2,V,T. ⦃G, L1⦄ ⊢ ➡[h, ⓑ{p,I}V.T] L2 →
                     ∧∧ ⦃G, L1⦄ ⊢ ➡[h, V] L2 & ⦃G, L1.ⓑ{I}V⦄ ⊢ ➡[h, T] L2.ⓑ{I}V.
/2 width=2 by lfxs_inv_bind/ qed-.

lemma lfpr_inv_flat: ∀h,I,G,L1,L2,V,T. ⦃G, L1⦄ ⊢ ➡[h, ⓕ{I}V.T] L2 →
                     ∧∧ ⦃G, L1⦄ ⊢ ➡[h, V] L2 & ⦃G, L1⦄ ⊢ ➡[h, T] L2.
/2 width=2 by lfxs_inv_flat/ qed-.

(* Advanced inversion lemmas ************************************************)

lemma lfpr_inv_sort_bind_sn: ∀h,I1,G,Y2,L1,s. ⦃G, L1.ⓘ{I1}⦄ ⊢ ➡[h, ⋆s] Y2 →
                             ∃∃I2,L2. ⦃G, L1⦄ ⊢ ➡[h, ⋆s] L2 & Y2 = L2.ⓘ{I2}.
/2 width=2 by lfxs_inv_sort_bind_sn/ qed-.

lemma lfpr_inv_sort_bind_dx: ∀h,I2,G,Y1,L2,s. ⦃G, Y1⦄ ⊢ ➡[h, ⋆s] L2.ⓘ{I2} →
                             ∃∃I1,L1. ⦃G, L1⦄ ⊢ ➡[h, ⋆s] L2 & Y1 = L1.ⓘ{I1}.
/2 width=2 by lfxs_inv_sort_bind_dx/ qed-.

lemma lfpr_inv_zero_pair_sn: ∀h,I,G,Y2,L1,V1. ⦃G, L1.ⓑ{I}V1⦄ ⊢ ➡[h, #0] Y2 →
                             ∃∃L2,V2. ⦃G, L1⦄ ⊢ ➡[h, V1] L2 & ⦃G, L1⦄ ⊢ V1 ➡[h] V2 &
                                      Y2 = L2.ⓑ{I}V2.
/2 width=1 by lfxs_inv_zero_pair_sn/ qed-.

lemma lfpr_inv_zero_pair_dx: ∀h,I,G,Y1,L2,V2. ⦃G, Y1⦄ ⊢ ➡[h, #0] L2.ⓑ{I}V2 →
                             ∃∃L1,V1. ⦃G, L1⦄ ⊢ ➡[h, V1] L2 & ⦃G, L1⦄ ⊢ V1 ➡[h] V2 &
                                      Y1 = L1.ⓑ{I}V1.
/2 width=1 by lfxs_inv_zero_pair_dx/ qed-.

lemma lfpr_inv_lref_bind_sn: ∀h,I1,G,Y2,L1,i. ⦃G, L1.ⓘ{I1}⦄ ⊢ ➡[h, #↑i] Y2 →
                             ∃∃I2,L2. ⦃G, L1⦄ ⊢ ➡[h, #i] L2 & Y2 = L2.ⓘ{I2}.
/2 width=2 by lfxs_inv_lref_bind_sn/ qed-.

lemma lfpr_inv_lref_bind_dx: ∀h,I2,G,Y1,L2,i. ⦃G, Y1⦄ ⊢ ➡[h, #↑i] L2.ⓘ{I2} →
                             ∃∃I1,L1. ⦃G, L1⦄ ⊢ ➡[h, #i] L2 & Y1 = L1.ⓘ{I1}.
/2 width=2 by lfxs_inv_lref_bind_dx/ qed-.

lemma lfpr_inv_gref_bind_sn: ∀h,I1,G,Y2,L1,l. ⦃G, L1.ⓘ{I1}⦄ ⊢ ➡[h, §l] Y2 →
                             ∃∃I2,L2. ⦃G, L1⦄ ⊢ ➡[h, §l] L2 & Y2 = L2.ⓘ{I2}.
/2 width=2 by lfxs_inv_gref_bind_sn/ qed-.

lemma lfpr_inv_gref_bind_dx: ∀h,I2,G,Y1,L2,l. ⦃G, Y1⦄ ⊢ ➡[h, §l] L2.ⓘ{I2} →
                             ∃∃I1,L1. ⦃G, L1⦄ ⊢ ➡[h, §l] L2 & Y1 = L1.ⓘ{I1}.
/2 width=2 by lfxs_inv_gref_bind_dx/ qed-.

(* Basic forward lemmas *****************************************************)

lemma lfpr_fwd_pair_sn: ∀h,I,G,L1,L2,V,T.
                        ⦃G, L1⦄ ⊢ ➡[h, ②{I}V.T] L2 → ⦃G, L1⦄ ⊢ ➡[h, V] L2.
/2 width=3 by lfxs_fwd_pair_sn/ qed-.

lemma lfpr_fwd_bind_dx: ∀h,p,I,G,L1,L2,V,T.
                        ⦃G, L1⦄ ⊢ ➡[h, ⓑ{p,I}V.T] L2 → ⦃G, L1.ⓑ{I}V⦄ ⊢ ➡[h, T] L2.ⓑ{I}V.
/2 width=2 by lfxs_fwd_bind_dx/ qed-.

lemma lfpr_fwd_flat_dx: ∀h,I,G,L1,L2,V,T.
                        ⦃G, L1⦄ ⊢ ➡[h, ⓕ{I}V.T] L2 → ⦃G, L1⦄ ⊢ ➡[h, T] L2.
/2 width=3 by lfxs_fwd_flat_dx/ qed-.

(* Basic_2A1: removed theorems 5:
              lpr_inv_pair1 lpr_inv_pair2
              cpr_conf_lpr lpr_cpr_conf_dx lpr_cpr_conf_sn
*)
(* Basic_1: removed theorems 7:
            wcpr0_gen_sort wcpr0_gen_head
            wcpr0_getl wcpr0_getl_back
            pr0_subst1_back
            wcpr0_drop wcpr0_drop_back
*)
