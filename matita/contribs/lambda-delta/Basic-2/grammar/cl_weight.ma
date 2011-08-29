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

include "Basic-2/grammar/lenv_weight.ma".
include "Basic-2/grammar/cl_shift.ma".

(* WEIGHT OF A CLOSURE ******************************************************)

definition cw: lenv → term → ? ≝ λL,T. #[L] + #[T].

interpretation "weight (closure)" 'Weight L T = (cw L T).

(* Basic properties *********************************************************)

axiom cw_wf_ind: ∀R:lenv→term→Prop.
                 (∀L2,T2. (∀L1,T1. #[L1,T1] < #[L2,T2] → R L1 T1) → R L2 T2) →
                 ∀L,T. R L T.

lemma cw_shift: ∀K,I,V,T. #[K. 𝕓{I} V, T] < #[K, 𝕔{I} V. T].
normalize //
qed.

lemma tw_shift: ∀L,T. #[L, T] ≤ #[L @ T].
#L elim L //
#K #I #V #IHL #T
@transitive_le [3: @IHL |2: /2/ | skip ]
qed.
