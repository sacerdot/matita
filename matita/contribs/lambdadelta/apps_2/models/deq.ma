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

include "apps_2/notation/models/ringeq_4.ma".
include "apps_2/models/model_li.ma".
include "apps_2/models/model_props.ma".

(* DENOTATIONAL EQUIVALENCE  ************************************************)

definition deq (M): relation3 lenv term term ≝
                    λL,T1,T2. ∀gv,lv. lv ϵ ⟦L⟧[gv] → ⟦T1⟧[gv, lv] ≗{M} ⟦T2⟧[gv, lv].

interpretation "denotational equivalence (model)"
   'RingEq M L T1 T2 = (deq M L T1 T2).

(* Basic properties *********************************************************)

lemma deq_refl (M): is_model M →
                    c_reflexive … (deq M).
/2 width=1 by mq/ qed.
(*
lemma veq_sym: ∀M. symmetric … (veq M).
// qed-.

theorem veq_trans: ∀M. transitive … (veq M).
// qed-.
*)
