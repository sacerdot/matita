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

include "Basic_2/grammar/term_simple.ma".

(* CONTEXT-FREE REDUCIBLE AND IRREDUCIBLE TERMS *****************************)

(* reducible terms *)
inductive trf: predicate term ≝
| trf_abst_sn: ∀V,T.   trf V → trf (𝕔{Abst} V. T)
| trf_abst_dx: ∀V,T.   trf T → trf (𝕔{Abst} V. T)
| trf_appl_sn: ∀V,T.   trf V → trf (𝕔{Appl} V. T)
| trf_appl_dx: ∀V,T.   trf T → trf (𝕔{Appl} V. T)
| trf_abbr   : ∀V,T.           trf (𝕔{Abbr} V. T)
| trf_cast   : ∀V,T.           trf (𝕔{Cast} V. T)
| trf_beta   : ∀V,W,T. trf (𝕔{Appl} V. 𝕔{Abst} W. T)
.

interpretation
   "context-free reducibility (term)"
   'Reducible T = (trf T).

(* irreducible terms *)
definition tif: predicate term ≝ λT. ℝ[T] → False.

interpretation
   "context-free irreducibility (term)"
   'NotReducible T = (tif T).

(* Basic inversion lemmas ***************************************************)

fact trf_inv_atom_aux: ∀I,T. ℝ[T] → T =  𝕒{I} → False.
#I #T * -T
[ #V #T #_ #H destruct
| #V #T #_ #H destruct
| #V #T #_ #H destruct
| #V #T #_ #H destruct
| #V #T #H destruct
| #V #T #H destruct
| #V #W #T #H destruct
]
qed.

lemma trf_inv_atom: ∀I. ℝ[𝕒{I}] → False.
/2 width=4/ qed-.

fact trf_inv_abst_aux: ∀W,U,T. ℝ[T] → T =  𝕔{Abst} W. U → ℝ[W] ∨ ℝ[U].
#W #U #T * -T
[ #V #T #HV #H destruct /2 width=1/
| #V #T #HT #H destruct /2 width=1/
| #V #T #_ #H destruct
| #V #T #_ #H destruct
| #V #T #H destruct
| #V #T #H destruct
| #V #W0 #T #H destruct
]
qed.

lemma trf_inv_abst: ∀V,T. ℝ[𝕔{Abst}V.T] → ℝ[V] ∨ ℝ[T].
/2 width=3/ qed-.

fact trf_inv_appl_aux: ∀W,U,T. ℝ[T] → T =  𝕔{Appl} W. U →
                       ∨∨ ℝ[W] | ℝ[U] | (𝕊[U] → False).
#W #U #T * -T
[ #V #T #_ #H destruct
| #V #T #_ #H destruct
| #V #T #HV #H destruct /2 width=1/
| #V #T #HT #H destruct /2 width=1/
| #V #T #H destruct
| #V #T #H destruct
| #V #W0 #T #H destruct
  @or3_intro2 #H elim (simple_inv_bind … H)
]
qed.

lemma trf_inv_appl: ∀W,U. ℝ[𝕔{Appl}W.U] → ∨∨ ℝ[W] | ℝ[U] | (𝕊[U] → False).
/2 width=3/ qed-.

lemma tif_inv_abbr: ∀V,T. 𝕀[𝕔{Abbr}V.T] → False.
/2 width=1/ qed-.

lemma tif_inv_abst: ∀V,T. 𝕀[𝕔{Abst}V.T] → 𝕀[V] ∧ 𝕀[T].
/4 width=1/ qed-.

lemma tif_inv_appl: ∀V,T. 𝕀[𝕔{Appl}V.T] → ∧∧ 𝕀[V] & 𝕀[T] & 𝕊[T].
#V #T #HVT @and3_intro /3 width=1/
generalize in match HVT; -HVT elim T -T //
* // * #U #T #_ #_ #H elim (H ?) -H /2 width=1/
qed-.

lemma tif_inv_cast: ∀V,T. 𝕀[𝕔{Cast}V.T] → False.
/2 width=1/ qed-.

(* Basic properties *********************************************************)

lemma tif_atom: ∀I. 𝕀[𝕒{I}].
/2 width=4/ qed.

lemma tif_abst: ∀V,T. 𝕀[V] →  𝕀[T] →  𝕀[𝕔 {Abst}V.T].
#V #T #HV #HT #H
elim (trf_inv_abst … H) -H /2 width=1/
qed.

lemma tif_appl: ∀V,T. 𝕀[V] →  𝕀[T] →  𝕊[T] → 𝕀[𝕔{Appl}V.T].
#V #T #HV #HT #S #H
elim (trf_inv_appl … H) -H /2 width=1/
qed.
