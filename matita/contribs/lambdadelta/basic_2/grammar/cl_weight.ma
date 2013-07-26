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

include "basic_2/notation/functions/weight_2.ma".
include "basic_2/grammar/lenv_weight.ma".
include "basic_2/grammar/cl_shift.ma".

(* WEIGHT OF A CLOSURE ******************************************************)

definition fw: lenv → term → ? ≝ λL,T. ♯{L} + ♯{T}.

interpretation "weight (closure)" 'Weight L T = (fw L T).

(* Basic properties *********************************************************)

(* Basic_1: was: flt_shift *)
lemma fw_shift: ∀a,K,I,V,T. ♯{K. ⓑ{I} V, T} < ♯{K, ⓑ{a,I} V. T}.
normalize //
qed.

lemma fw_tpair_sn: ∀I,L,V,T. ♯{L, V} < ♯{L, ②{I}V.T}.
normalize in ⊢ (?→?→?→?→?%%); //
qed.

lemma fw_tpair_dx: ∀I,L,V,T. ♯{L, T} < ♯{L, ②{I}V.T}.
normalize in ⊢ (?→?→?→?→?%%); //
qed.

lemma fw_lpair_sn: ∀I,L,V,T. ♯{L, V} < ♯{L.ⓑ{I}V, T}.
normalize /3 width=1 by monotonic_lt_plus_l, monotonic_le_plus_r/ (**) (* auto too slow without trace *)
qed.

(* Basic_1: removed theorems 7:
            flt_thead_sx flt_thead_dx flt_trans
            flt_arith0 flt_arith1 flt_arith2 flt_wf_ind
*)
(* Basic_1: removed local theorems 1: q_ind *)
