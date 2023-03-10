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

include "basic_2A/notation/functions/weight_2.ma".
include "basic_2A/grammar/lenv_weight.ma".

(* WEIGHT OF A RESTRICTED CLOSURE *******************************************)

definition rfw: lenv → term → ? ≝ λL,T. ♯{L} + ♯{T}.

interpretation "weight (restricted closure)" 'Weight L T = (rfw L T).

(* Basic properties *********************************************************)

lemma rfw_shift: ∀a,I,K,V,T. ♯{K.ⓑ{I}V, T} < ♯{K, ⓑ{a,I}V.T}.
normalize //
qed.

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
