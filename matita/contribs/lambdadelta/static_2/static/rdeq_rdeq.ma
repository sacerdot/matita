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
include "static_2/syntax/tdeq_tdeq.ma".
include "static_2/static/rdeq_length.ma".

(* DEGREE-BASED EQUIVALENCE FOR LOCAL ENVIRONMENTS ON REFERRED ENTRIES ******)

(* Advanced properties ******************************************************)

(* Basic_2A1: uses: lleq_sym *)
lemma rdeq_sym: ∀h,o,T. symmetric … (rdeq h o T).
/3 width=3 by rdeq_fsge_comp, rex_sym, tdeq_sym/ qed-.

(* Basic_2A1: uses: lleq_dec *)
lemma rdeq_dec: ∀h,o,L1,L2. ∀T:term. Decidable (L1 ≛[h, o, T] L2).
/3 width=1 by rex_dec, tdeq_dec/ qed-.

(* Main properties **********************************************************)

(* Basic_2A1: uses: lleq_bind lleq_bind_O *) 
theorem rdeq_bind: ∀h,o,p,I,L1,L2,V1,V2,T.
                   L1 ≛[h, o, V1] L2 → L1.ⓑ{I}V1 ≛[h, o, T] L2.ⓑ{I}V2 →
                   L1 ≛[h, o, ⓑ{p,I}V1.T] L2.
/2 width=2 by rex_bind/ qed.

(* Basic_2A1: uses: lleq_flat *)
theorem rdeq_flat: ∀h,o,I,L1,L2,V,T. L1 ≛[h, o, V] L2 → L1 ≛[h, o, T] L2 →
                   L1 ≛[h, o, ⓕ{I}V.T] L2.
/2 width=1 by rex_flat/ qed.

theorem rdeq_bind_void: ∀h,o,p,I,L1,L2,V,T.
                        L1 ≛[h, o, V] L2 → L1.ⓧ ≛[h, o, T] L2.ⓧ →
                        L1 ≛[h, o, ⓑ{p,I}V.T] L2.
/2 width=1 by rex_bind_void/ qed.

(* Basic_2A1: uses: lleq_trans *)
theorem rdeq_trans: ∀h,o,T. Transitive … (rdeq h o T).
#h #o #T #L1 #L * #f1 #Hf1 #HL1 #L2 * #f2 #Hf2 #HL2
lapply (frees_tdeq_conf_rdeq … Hf1 T … HL1) // #H0
lapply (frees_mono … Hf2 … H0) -Hf2 -H0
/5 width=7 by sex_trans, sex_eq_repl_back, tdeq_trans, ext2_trans, ex2_intro/
qed-.

(* Basic_2A1: uses: lleq_canc_sn *)
theorem rdeq_canc_sn: ∀h,o,T. left_cancellable … (rdeq h o T).
/3 width=3 by rdeq_trans, rdeq_sym/ qed-.

(* Basic_2A1: uses: lleq_canc_dx *)
theorem rdeq_canc_dx: ∀h,o,T. right_cancellable … (rdeq h o T).
/3 width=3 by rdeq_trans, rdeq_sym/ qed-.

theorem rdeq_repl: ∀h,o,L1,L2. ∀T:term. L1 ≛[h, o, T] L2 →
                   ∀K1. L1 ≛[h, o, T] K1 → ∀K2. L2 ≛[h, o, T] K2 → K1 ≛[h, o, T] K2.
/3 width=3 by rdeq_canc_sn, rdeq_trans/ qed-.

(* Negated properties *******************************************************)

(* Note: auto works with /4 width=8/ so rdeq_canc_sn is preferred **********) 
(* Basic_2A1: uses: lleq_nlleq_trans *)
lemma rdeq_rdneq_trans: ∀h,o.∀T:term.∀L1,L. L1 ≛[h, o, T] L →
                        ∀L2. (L ≛[h, o, T] L2 → ⊥) → (L1 ≛[h, o, T] L2 → ⊥).
/3 width=3 by rdeq_canc_sn/ qed-.

(* Basic_2A1: uses: nlleq_lleq_div *)
lemma rdneq_rdeq_div: ∀h,o.∀T:term.∀L2,L. L2 ≛[h, o, T] L →
                      ∀L1. (L1 ≛[h, o, T] L → ⊥) → (L1 ≛[h, o, T] L2 → ⊥).
/3 width=3 by rdeq_trans/ qed-.

theorem rdneq_rdeq_canc_dx: ∀h,o,L1,L. ∀T:term. (L1 ≛[h, o, T] L → ⊥) →
                            ∀L2. L2 ≛[h, o, T] L → L1 ≛[h, o, T] L2 → ⊥.
/3 width=3 by rdeq_trans/ qed-.

(* Negated inversion lemmas *************************************************)

(* Basic_2A1: uses: nlleq_inv_bind nlleq_inv_bind_O *)
lemma rdneq_inv_bind: ∀h,o,p,I,L1,L2,V,T. (L1 ≛[h, o, ⓑ{p,I}V.T] L2 → ⊥) →
                      (L1 ≛[h, o, V] L2 → ⊥) ∨ (L1.ⓑ{I}V ≛[h, o, T] L2.ⓑ{I}V → ⊥).
/3 width=2 by rnex_inv_bind, tdeq_dec/ qed-.

(* Basic_2A1: uses: nlleq_inv_flat *)
lemma rdneq_inv_flat: ∀h,o,I,L1,L2,V,T. (L1 ≛[h, o, ⓕ{I}V.T] L2 → ⊥) →
                      (L1 ≛[h, o, V] L2 → ⊥) ∨ (L1 ≛[h, o, T] L2 → ⊥).
/3 width=2 by rnex_inv_flat, tdeq_dec/ qed-.

lemma rdneq_inv_bind_void: ∀h,o,p,I,L1,L2,V,T. (L1 ≛[h, o, ⓑ{p,I}V.T] L2 → ⊥) →
                           (L1 ≛[h, o, V] L2 → ⊥) ∨ (L1.ⓧ ≛[h, o, T] L2.ⓧ → ⊥).
/3 width=3 by rnex_inv_bind_void, tdeq_dec/ qed-.