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

include "basic_2A/multiple/lleq_drop.ma".

(* LAZY EQUIVALENCE FOR LOCAL ENVIRONMENTS **********************************)

(* Main properties **********************************************************)

theorem lleq_trans: ∀l,T. Transitive … (lleq l T).
/2 width=3 by lleq_llpx_sn_trans/ qed-.

theorem lleq_canc_sn: ∀L,L1,L2,T,l. L ≡[l, T] L1→ L ≡[l, T] L2 → L1 ≡[l, T] L2.
/3 width=3 by lleq_trans, lleq_sym/ qed-.

theorem lleq_canc_dx: ∀L1,L2,L,T,l. L1 ≡[l, T] L → L2 ≡[l, T] L → L1 ≡[l, T] L2.
/3 width=3 by lleq_trans, lleq_sym/ qed-.

(* Advanced properies on negated lazy equivalence *****************************)

(* Note: for use in auto, works with /4 width=8/ so lleq_canc_sn is preferred *) 
lemma lleq_nlleq_trans: ∀l,T,L1,L. L1 ≡[T, l] L →
                        ∀L2. (L ≡[T, l] L2 → ⊥) → (L1 ≡[T, l] L2 → ⊥).
/3 width=3 by lleq_canc_sn/ qed-.

lemma nlleq_lleq_div: ∀l,T,L2,L. L2 ≡[T, l] L →
                      ∀L1. (L1 ≡[T, l] L → ⊥) → (L1 ≡[T, l] L2 → ⊥).
/3 width=3 by lleq_trans/ qed-.
