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
include "basic_2/syntax/lenv_weight.ma".

(* WEIGHT OF A RESTRICTED CLOSURE *******************************************)

definition rfw: lenv → term → ? ≝ λL,T. ♯{L} + ♯{T}.

interpretation "weight (restricted closure)" 'Weight L T = (rfw L T).

(* Basic properties *********************************************************)

(* Basic_1: was: flt_shift *)
lemma rfw_shift: ∀p,I,K,V,T. ♯{K.ⓑ{I}V, T} < ♯{K, ⓑ{p,I}V.T}.
normalize /2 width=1 by monotonic_le_plus_r/
qed.
(*
lemma rfw_clear: ∀p,I1,I2,K,V,T. ♯{K.ⓤ{I1}, T} < ♯{K, ⓑ{p,I2}V.T}.
normalize /4 width=1 by monotonic_le_plus_r, le_S_S/
qed.
*)
lemma rfw_tpair_sn: ∀I,L,V,T. ♯{L, V} < ♯{L, ②{I}V.T}.
normalize in ⊢ (?→?→?→?→?%%); //
qed.

lemma rfw_tpair_dx: ∀I,L,V,T. ♯{L, T} < ♯{L, ②{I}V.T}.
normalize in ⊢ (?→?→?→?→?%%); //
qed.

lemma rfw_lpair_sn: ∀I,L,V,T. ♯{L, V} < ♯{L.ⓑ{I}V, T}.
normalize /3 width=1 by monotonic_lt_plus_l, monotonic_le_plus_r/
qed.

lemma rfw_lpair_dx: ∀I,L,V,T. ♯{L, T} < ♯{L.ⓑ{I}V, T}.
normalize /3 width=1 by monotonic_lt_plus_l, monotonic_le_plus_r/
qed.

(* Basic_1: removed theorems 7:
            flt_thead_sx flt_thead_dx flt_trans
            flt_arith0 flt_arith1 flt_arith2 flt_wf_ind
*)
(* Basic_1: removed local theorems 1: q_ind *)
