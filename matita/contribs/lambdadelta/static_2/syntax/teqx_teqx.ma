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

include "static_2/syntax/teqx.ma".

(* SORT-IRRELEVANT EQUIVALENCE ON TERMS *************************************)

(* Main properties **********************************************************)

theorem teqx_trans: Transitive … teqx.
#T1 #T #H elim H -T1 -T
[ #s1 #s #X #H
  elim (teqx_inv_sort1 … H) -s /2 width=1 by teqx_sort/
| #i1 #i #H <(teqx_inv_lref1 … H) -H //
| #l1 #l #H <(teqx_inv_gref1 … H) -H //
| #I #V1 #V #T1 #T #_ #_ #IHV #IHT #X #H
  elim (teqx_inv_pair1 … H) -H /3 width=1 by teqx_pair/
]
qed-.

theorem teqx_canc_sn: left_cancellable … teqx.
/3 width=3 by teqx_trans, teqx_sym/ qed-.

theorem teqx_canc_dx: right_cancellable … teqx.
/3 width=3 by teqx_trans, teqx_sym/ qed-.

theorem teqx_repl: ∀T1,T2. T1 ≛ T2 →
                   ∀U1. T1 ≛ U1 → ∀U2. T2 ≛ U2 → U1 ≛ U2.
/3 width=3 by teqx_canc_sn, teqx_trans/ qed-.

(* Negated main properies ***************************************************)

theorem teqx_tneqx_trans: ∀T1,T. T1 ≛ T → ∀T2. (T ≛ T2 → ⊥) → T1 ≛ T2 → ⊥.
/3 width=3 by teqx_canc_sn/ qed-.

theorem tneqx_teqx_canc_dx: ∀T1,T. (T1 ≛ T → ⊥) → ∀T2. T2 ≛ T → T1 ≛ T2 → ⊥.
/3 width=3 by teqx_trans/ qed-.
