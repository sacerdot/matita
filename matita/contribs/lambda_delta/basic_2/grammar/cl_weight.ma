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

include "basic_2/grammar/lenv_weight.ma".
include "basic_2/grammar/cl_shift.ma".

(* WEIGHT OF A CLOSURE ******************************************************)

definition cw: lenv → term → ? ≝ λL,T. #[L] + #[T].

interpretation "weight (closure)" 'Weight L T = (cw L T).

(* Basic properties *********************************************************)

(* Basic_1: was: flt_wf__q_ind *)

(* Basic_1: was: flt_wf_ind *)
axiom cw_wf_ind: ∀R:lenv→predicate term.
                 (∀L2,T2. (∀L1,T1. #[L1,T1] < #[L2,T2] → R L1 T1) → R L2 T2) →
                 ∀L,T. R L T.

(* Basic_1: was: flt_shift *)
lemma cw_shift: ∀K,I,V,T. #[K. ⓑ{I} V, T] < #[K, ②{I} V. T].
normalize //
qed.

lemma tw_shift: ∀L,T. #[L, T] ≤ #[L @ T].
#L elim L //
#K #I #V #IHL #T
@transitive_le [3: @IHL |2: /2 width=2/ | skip ]
qed.

lemma cw_tpair_sn: ∀I,L,V,T. #[L, V] < #[L, ②{I}V.T].
#I #L #V #T normalize in ⊢ (? % %); //
qed.

lemma cw_tpair_dx: ∀I,L,V,T. #[L, T] < #[L, ②{I}V.T].
#I #L #V #T normalize in ⊢ (? % %); //
qed.

lemma cw_tpair_dx_sn: ∀I1,I2,L,V1,V2,T. #[L, V2] < #[L, ②{I1}V1.②{I2}V2.T].
#I1 #I2 #L #V1 #V2 #T normalize in ⊢ (? % %); /2 width=1/
qed.

lemma cw_tpair_dx_sn_shift: ∀I1,I2,L,V1,V2,T. #[L.ⓑ{I2}V2, T] < #[L, ②{I1}V1.②{I2}V2.T].
#I1 #I2 #L #V1 #V2 #T normalize in ⊢ (? % %); /2 width=1/
qed.

(* Basic_1: removed theorems 6:
            flt_thead_sx flt_thead_dx flt_arith0 flt_arith1 flt_arith2 flt_trans
*)
