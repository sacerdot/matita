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

include "ground/arith/pnat_plus.ma".
include "explicit_updating/syntax/term.ma".
include "explicit_updating/notation/functions/sharp_1.ma".

(* WEIGHT FOR TERM **********************************************************)

rec definition term_weight (t:𝕋) on t : ℕ⁺ ≝
match t with
[ lref p   ⇒ 𝟏
| abst b t ⇒ ↑(term_weight t)
| appl v t ⇒ (term_weight v)+(term_weight t)
| lift f t ⇒ ↑(term_weight t)
].

interpretation
  "weight (term)"
  'Sharp t = (term_weight t).

(* Basic constructions ******************************************************)

lemma term_weight_lref (p):
      (𝟏) = ♯❨𝛏p❩.
//
qed.

lemma term_weight_abst (b) (t):
      ↑♯❨t❩ = ♯❨𝛌b.t❩.
//
qed.

lemma term_weight_appl (v) (t):
      ♯❨v❩+♯❨t❩ = ♯❨＠v.t❩.
//
qed.

lemma term_weight_lift (f) (t):
      ↑♯❨t❩ = ♯❨𝛗f.t❩.
//
qed.
