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

include "basic_2/notation/functions/weight_3.ma".
include "basic_2/grammar/lenv_weight.ma".
include "basic_2/grammar/genv.ma".

(* WEIGHT OF A CLOSURE ******************************************************)

(* activate genv *)
definition fw: genv → lenv → term → ? ≝ λG,L,T. ♯{L} + ♯{T}.

interpretation "weight (closure)" 'Weight G L T = (fw G L T).

(* Basic properties *********************************************************)

(* Basic_1: was: flt_shift *)
lemma fw_shift: ∀a,I,G,K,V,T. ♯{G, K.ⓑ{I}V, T} < ♯{G, K, ⓑ{a,I}V.T}.
normalize //
qed.

lemma fw_tpair_sn: ∀I,G,L,V,T. ♯{G, L, V} < ♯{G, L, ②{I}V.T}.
normalize in ⊢ (?→?→?→?→?→?%%); //
qed.

lemma fw_tpair_dx: ∀I,G,L,V,T. ♯{G, L, T} < ♯{G, L, ②{I}V.T}.
normalize in ⊢ (?→?→?→?→?→?%%); //
qed.

lemma fw_lpair_sn: ∀I,G,L,V,T. ♯{G, L, V} < ♯{G, L.ⓑ{I}V, T}.
normalize /3 width=1 by monotonic_lt_plus_l, monotonic_le_plus_r/
qed.

(* Basic_1: removed theorems 7:
            flt_thead_sx flt_thead_dx flt_trans
            flt_arith0 flt_arith1 flt_arith2 flt_wf_ind
*)
(* Basic_1: removed local theorems 1: q_ind *)
