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

include "static_2/syntax/teqg_teqg.ma".
include "static_2/syntax/teqx.ma".

(* SORT-IRRELEVANT EQUIVALENCE ON TERMS *************************************)

(* Main properties **********************************************************)

theorem teqx_trans:
        Transitive … teqx.
/2 width=3 by teqg_trans/ qed-.

theorem teqx_canc_sn:
        left_cancellable … teqx.
/2 width=3 by teqg_canc_sn/ qed-.

theorem teqx_canc_dx:
        right_cancellable … teqx.
/2 width=3 by teqg_canc_dx/ qed-.
(*
theorem teqx_repl: ∀T1,T2. T1 ≛ T2 →
                   ∀U1. T1 ≛ U1 → ∀U2. T2 ≛ U2 → U1 ≛ U2.
/3 width=3 by teqx_canc_sn, teqx_trans/ qed-.

(* Negated main properies ***************************************************)

theorem teqx_tneqx_trans: ∀T1,T. T1 ≛ T → ∀T2. (T ≛ T2 → ⊥) → T1 ≛ T2 → ⊥.
/3 width=3 by teqx_canc_sn/ qed-.

theorem tneqx_teqx_canc_dx: ∀T1,T. (T1 ≛ T → ⊥) → ∀T2. T2 ≛ T → T1 ≛ T2 → ⊥.
/3 width=3 by teqx_trans/ qed-.
*)
