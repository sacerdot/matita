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

include "basic_2/notation/relations/predtysn_4.ma".
include "static_2/static/rex.ma".
include "basic_2/rt_transition/cpx_ext.ma".

(* EXTENDED PARALLEL RT-TRANSITION FOR REFERRED LOCAL ENVIRONMENTS **********)

definition rpx (G): relation3 term lenv lenv ≝
           rex (cpx G).

interpretation
  "extended parallel rt-transition on referred entries (local environment)"
  'PRedTySn T G L1 L2 = (rpx G T L1 L2).

(* Basic properties ***********************************************************)

lemma rpx_atom (G):
      ∀I. ❨G,⋆❩ ⊢ ⬈[⓪[I]] ⋆.
/2 width=1 by rex_atom/ qed.

lemma rpx_sort (G):
      ∀I1,I2,L1,L2,s.
      ❨G,L1❩ ⊢ ⬈[⋆s] L2 → ❨G,L1.ⓘ[I1]❩ ⊢ ⬈[⋆s] L2.ⓘ[I2].
/2 width=1 by rex_sort/ qed.

lemma rpx_pair (G):
      ∀I,L1,L2,V1,V2.
      ❨G,L1❩ ⊢ ⬈[V1] L2 → ❨G,L1❩ ⊢ V1 ⬈ V2 → ❨G,L1.ⓑ[I]V1❩ ⊢ ⬈[#0] L2.ⓑ[I]V2.
/2 width=1 by rex_pair/ qed.

lemma rpx_lref (G):
      ∀I1,I2,L1,L2,i.
      ❨G,L1❩ ⊢ ⬈[#i] L2 → ❨G,L1.ⓘ[I1]❩ ⊢ ⬈[#↑i] L2.ⓘ[I2].
/2 width=1 by rex_lref/ qed.

lemma rpx_gref (G):
      ∀I1,I2,L1,L2,l.
      ❨G,L1❩ ⊢ ⬈[§l] L2 → ❨G,L1.ⓘ[I1]❩ ⊢ ⬈[§l] L2.ⓘ[I2].
/2 width=1 by rex_gref/ qed.

lemma rpx_bind_repl_dx (G):
      ∀I,I1,L1,L2,T. ❨G,L1.ⓘ[I]❩ ⊢ ⬈[T] L2.ⓘ[I1] →
      ∀I2. ❨G,L1❩ ⊢ I ⬈ I2 → ❨G,L1.ⓘ[I]❩ ⊢ ⬈[T] L2.ⓘ[I2].
/2 width=2 by rex_bind_repl_dx/ qed-.

(* Basic inversion lemmas ***************************************************)

lemma rpx_inv_atom_sn (G):
      ∀Y2,T. ❨G,⋆❩ ⊢ ⬈[T] Y2 → Y2 = ⋆.
/2 width=3 by rex_inv_atom_sn/ qed-.

lemma rpx_inv_atom_dx (G):
      ∀Y1,T. ❨G,Y1❩ ⊢ ⬈[T] ⋆ → Y1 = ⋆.
/2 width=3 by rex_inv_atom_dx/ qed-.

lemma rpx_inv_sort (G):
      ∀Y1,Y2,s. ❨G,Y1❩ ⊢ ⬈[⋆s] Y2 →
      ∨∨ ∧∧ Y1 = ⋆ & Y2 = ⋆
       | ∃∃I1,I2,L1,L2. ❨G,L1❩ ⊢ ⬈[⋆s] L2 & Y1 = L1.ⓘ[I1] & Y2 = L2.ⓘ[I2].
/2 width=1 by rex_inv_sort/ qed-.

lemma rpx_inv_lref (G):
      ∀Y1,Y2,i. ❨G,Y1❩ ⊢ ⬈[#↑i] Y2 →
      ∨∨ ∧∧ Y1 = ⋆ & Y2 = ⋆
       | ∃∃I1,I2,L1,L2. ❨G,L1❩ ⊢ ⬈[#i] L2 & Y1 = L1.ⓘ[I1] & Y2 = L2.ⓘ[I2].
/2 width=1 by rex_inv_lref/ qed-.

lemma rpx_inv_gref (G):
      ∀Y1,Y2,l. ❨G,Y1❩ ⊢ ⬈[§l] Y2 →
      ∨∨ ∧∧ Y1 = ⋆ & Y2 = ⋆
       | ∃∃I1,I2,L1,L2. ❨G,L1❩ ⊢ ⬈[§l] L2 & Y1 = L1.ⓘ[I1] & Y2 = L2.ⓘ[I2].
/2 width=1 by rex_inv_gref/ qed-.

lemma rpx_inv_bind (G):
      ∀p,I,L1,L2,V,T. ❨G,L1❩ ⊢ ⬈[ⓑ[p,I]V.T] L2 →
      ∧∧ ❨G,L1❩ ⊢ ⬈[V] L2 & ❨G,L1.ⓑ[I]V❩ ⊢ ⬈[T] L2.ⓑ[I]V.
/2 width=2 by rex_inv_bind/ qed-.

lemma rpx_inv_flat (G):
      ∀I,L1,L2,V,T. ❨G,L1❩ ⊢ ⬈[ⓕ[I]V.T] L2 →
      ∧∧ ❨G,L1❩ ⊢ ⬈[V] L2 & ❨G,L1❩ ⊢ ⬈[T] L2.
/2 width=2 by rex_inv_flat/ qed-.

(* Advanced inversion lemmas ************************************************)

lemma rpx_inv_sort_bind_sn (G):
      ∀I1,Y2,L1,s. ❨G,L1.ⓘ[I1]❩ ⊢ ⬈[⋆s] Y2 →
      ∃∃I2,L2. ❨G,L1❩ ⊢ ⬈[⋆s] L2 & Y2 = L2.ⓘ[I2].
/2 width=2 by rex_inv_sort_bind_sn/ qed-.

lemma rpx_inv_sort_bind_dx (G):
      ∀I2,Y1,L2,s. ❨G,Y1❩ ⊢ ⬈[⋆s] L2.ⓘ[I2] →
      ∃∃I1,L1. ❨G,L1❩ ⊢ ⬈[⋆s] L2 & Y1 = L1.ⓘ[I1].
/2 width=2 by rex_inv_sort_bind_dx/ qed-.

lemma rpx_inv_zero_pair_sn (G):
      ∀I,Y2,L1,V1. ❨G,L1.ⓑ[I]V1❩ ⊢ ⬈[#0] Y2 →
      ∃∃L2,V2. ❨G,L1❩ ⊢ ⬈[V1] L2 & ❨G,L1❩ ⊢ V1 ⬈ V2 & Y2 = L2.ⓑ[I]V2.
/2 width=1 by rex_inv_zero_pair_sn/ qed-.

lemma rpx_inv_zero_pair_dx (G):
      ∀I,Y1,L2,V2. ❨G,Y1❩ ⊢ ⬈[#0] L2.ⓑ[I]V2 →
      ∃∃L1,V1. ❨G,L1❩ ⊢ ⬈[V1] L2 & ❨G,L1❩ ⊢ V1 ⬈ V2 & Y1 = L1.ⓑ[I]V1.
/2 width=1 by rex_inv_zero_pair_dx/ qed-.

lemma rpx_inv_lref_bind_sn (G):
      ∀I1,Y2,L1,i. ❨G,L1.ⓘ[I1]❩ ⊢ ⬈[#↑i] Y2 →
      ∃∃I2,L2. ❨G,L1❩ ⊢ ⬈[#i] L2 & Y2 = L2.ⓘ[I2].
/2 width=2 by rex_inv_lref_bind_sn/ qed-.

lemma rpx_inv_lref_bind_dx (G):
      ∀I2,Y1,L2,i. ❨G,Y1❩ ⊢ ⬈[#↑i] L2.ⓘ[I2] →
      ∃∃I1,L1. ❨G,L1❩ ⊢ ⬈[#i] L2 & Y1 = L1.ⓘ[I1].
/2 width=2 by rex_inv_lref_bind_dx/ qed-.

lemma rpx_inv_gref_bind_sn (G):
      ∀I1,Y2,L1,l. ❨G,L1.ⓘ[I1]❩ ⊢ ⬈[§l] Y2 →
      ∃∃I2,L2. ❨G,L1❩ ⊢ ⬈[§l] L2 & Y2 = L2.ⓘ[I2].
/2 width=2 by rex_inv_gref_bind_sn/ qed-.

lemma rpx_inv_gref_bind_dx (G):
      ∀I2,Y1,L2,l. ❨G,Y1❩ ⊢ ⬈[§l] L2.ⓘ[I2] →
      ∃∃I1,L1. ❨G,L1❩ ⊢ ⬈[§l] L2 & Y1 = L1.ⓘ[I1].
/2 width=2 by rex_inv_gref_bind_dx/ qed-.

(* Basic forward lemmas *****************************************************)

lemma rpx_fwd_pair_sn (G):
      ∀I,L1,L2,V,T. ❨G,L1❩ ⊢ ⬈[②[I]V.T] L2 → ❨G,L1❩ ⊢ ⬈[V] L2.
/2 width=3 by rex_fwd_pair_sn/ qed-.

lemma rpx_fwd_bind_dx (G):
      ∀p,I,L1,L2,V,T. ❨G,L1❩ ⊢ ⬈[ⓑ[p,I]V.T] L2 → ❨G,L1.ⓑ[I]V❩ ⊢ ⬈[T] L2.ⓑ[I]V.
/2 width=2 by rex_fwd_bind_dx/ qed-.

lemma rpx_fwd_flat_dx (G):
      ∀I,L1,L2,V,T. ❨G,L1❩ ⊢ ⬈[ⓕ[I]V.T] L2 → ❨G,L1❩ ⊢ ⬈[T] L2.
/2 width=3 by rex_fwd_flat_dx/ qed-.
