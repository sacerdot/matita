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

include "apps_2/notation/models/ringeq_5.ma".
include "apps_2/models/li.ma".
include "static_2/syntax/genv.ma".

(* DENOTATIONAL EQUIVALENCE  ************************************************)

definition deq (M): relation4 genv lenv term term ≝
                    λG,L,T1,T2. ∀gv,lv. lv ϵ ⟦L⟧[gv] → ⟦T1⟧[gv, lv] ≗{M} ⟦T2⟧[gv, lv].

interpretation "denotational equivalence (model)"
   'RingEq M G L T1 T2 = (deq M G L T1 T2).

(* Basic properties *********************************************************)

lemma deq_refl (M): is_model M →
                    ∀G,L. reflexive … (deq M G L).
/2 width=1 by mr/ qed.
(*
lemma veq_sym: ∀M. symmetric … (veq M).
// qed-.

theorem veq_trans: ∀M. transitive … (veq M).
// qed-.
*)
