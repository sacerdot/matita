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

include "static_2/syntax/ext2_ext2.ma".
include "static_2/syntax/teqx_teqx.ma".
include "static_2/static/reqx_length.ma".

(* SORT-IRRELEVANT EQUIVALENCE FOR LOCAL ENVIRONMENTS ON REFERRED ENTRIES ***)

(* Advanced properties ******************************************************)

(* Basic_2A1: uses: lleq_sym *)
lemma reqx_sym: ∀T. symmetric … (reqx T).
/3 width=3 by reqx_fsge_comp, rex_sym, teqx_sym/ qed-.

(* Basic_2A1: uses: lleq_dec *)
lemma reqx_dec: ∀L1,L2. ∀T:term. Decidable (L1 ≛[T] L2).
/3 width=1 by rex_dec, teqx_dec/ qed-.

(* Main properties **********************************************************)

(* Basic_2A1: uses: lleq_bind lleq_bind_O *)
theorem reqx_bind: ∀p,I,L1,L2,V1,V2,T.
                   L1 ≛[V1] L2 → L1.ⓑ{I}V1 ≛[T] L2.ⓑ{I}V2 →
                   L1 ≛[ⓑ{p,I}V1.T] L2.
/2 width=2 by rex_bind/ qed.

(* Basic_2A1: uses: lleq_flat *)
theorem reqx_flat: ∀I,L1,L2,V,T.
                   L1 ≛[V] L2 → L1 ≛[T] L2 → L1 ≛[ⓕ{I}V.T] L2.
/2 width=1 by rex_flat/ qed.

theorem reqx_bind_void: ∀p,I,L1,L2,V,T.
                        L1 ≛[V] L2 → L1.ⓧ ≛[T] L2.ⓧ → L1 ≛[ⓑ{p,I}V.T] L2.
/2 width=1 by rex_bind_void/ qed.

(* Basic_2A1: uses: lleq_trans *)
theorem reqx_trans: ∀T. Transitive … (reqx T).
#T #L1 #L * #f1 #Hf1 #HL1 #L2 * #f2 #Hf2 #HL2
lapply (frees_teqx_conf_reqx … Hf1 T … HL1) // #H0
lapply (frees_mono … Hf2 … H0) -Hf2 -H0
/5 width=7 by sex_trans, sex_eq_repl_back, teqx_trans, ext2_trans, ex2_intro/
qed-.

(* Basic_2A1: uses: lleq_canc_sn *)
theorem reqx_canc_sn: ∀T. left_cancellable … (reqx T).
/3 width=3 by reqx_trans, reqx_sym/ qed-.

(* Basic_2A1: uses: lleq_canc_dx *)
theorem reqx_canc_dx: ∀T. right_cancellable … (reqx T).
/3 width=3 by reqx_trans, reqx_sym/ qed-.

theorem reqx_repl: ∀L1,L2. ∀T:term. L1 ≛[T] L2 →
                   ∀K1. L1 ≛[T] K1 → ∀K2. L2 ≛[T] K2 → K1 ≛[T] K2.
/3 width=3 by reqx_canc_sn, reqx_trans/ qed-.

(* Negated properties *******************************************************)

(* Note: auto works with /4 width=8/ so reqx_canc_sn is preferred **********)
(* Basic_2A1: uses: lleq_nlleq_trans *)
lemma reqx_rneqx_trans: ∀T:term.∀L1,L. L1 ≛[T] L →
                        ∀L2. (L ≛[T] L2 → ⊥) → (L1 ≛[T] L2 → ⊥).
/3 width=3 by reqx_canc_sn/ qed-.

(* Basic_2A1: uses: nlleq_lleq_div *)
lemma rneqx_reqx_div: ∀T:term.∀L2,L. L2 ≛[T] L →
                      ∀L1. (L1 ≛[T] L → ⊥) → (L1 ≛[T] L2 → ⊥).
/3 width=3 by reqx_trans/ qed-.

theorem rneqx_reqx_canc_dx: ∀L1,L. ∀T:term. (L1 ≛[T] L → ⊥) →
                            ∀L2. L2 ≛[T] L → L1 ≛[T] L2 → ⊥.
/3 width=3 by reqx_trans/ qed-.

(* Negated inversion lemmas *************************************************)

(* Basic_2A1: uses: nlleq_inv_bind nlleq_inv_bind_O *)
lemma rneqx_inv_bind: ∀p,I,L1,L2,V,T. (L1 ≛[ⓑ{p,I}V.T] L2 → ⊥) →
                      (L1 ≛[V] L2 → ⊥) ∨ (L1.ⓑ{I}V ≛[T] L2.ⓑ{I}V → ⊥).
/3 width=2 by rnex_inv_bind, teqx_dec/ qed-.

(* Basic_2A1: uses: nlleq_inv_flat *)
lemma rneqx_inv_flat: ∀I,L1,L2,V,T. (L1 ≛[ⓕ{I}V.T] L2 → ⊥) →
                      (L1 ≛[V] L2 → ⊥) ∨ (L1 ≛[T] L2 → ⊥).
/3 width=2 by rnex_inv_flat, teqx_dec/ qed-.

lemma rneqx_inv_bind_void: ∀p,I,L1,L2,V,T. (L1 ≛[ⓑ{p,I}V.T] L2 → ⊥) →
                           (L1 ≛[V] L2 → ⊥) ∨ (L1.ⓧ ≛[T] L2.ⓧ → ⊥).
/3 width=3 by rnex_inv_bind_void, teqx_dec/ qed-.
