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

include "basic_2/multiple/lleq_drop.ma".

(* Main properties **********************************************************)

theorem lleq_trans: ∀d,T. Transitive … (lleq d T).
/2 width=3 by lleq_llpx_sn_trans/ qed-.

theorem lleq_canc_sn: ∀L,L1,L2,T,d. L ≡[d, T] L1→ L ≡[d, T] L2 → L1 ≡[d, T] L2.
/3 width=3 by lleq_trans, lleq_sym/ qed-.

theorem lleq_canc_dx: ∀L1,L2,L,T,d. L1 ≡[d, T] L → L2 ≡[d, T] L → L1 ≡[d, T] L2.
/3 width=3 by lleq_trans, lleq_sym/ qed-.

(* Note: lleq_nlleq_trans: ∀d,T,L1,L. L1≡[T, d] L →
                           ∀L2. (L ≡[T, d] L2 → ⊥) → (L1 ≡[T, d] L2 → ⊥).
/3 width=3 by lleq_canc_sn/ qed-.
works with /4 width=8/ so lleq_canc_sn is more convenient
*)
