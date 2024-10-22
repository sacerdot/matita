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

include "explicit_updating/syntax/term.ma".
include "explicit_updating/notation/functions/flat_1.ma".

(* FLATTENING FOR TERM ******************************************************)

(* Source: ❘·❘ (Barendregt, The λ-Calculus, 11.1.2 iii) *) 
rec definition term_flat (t:𝕋) on t : 𝕋 ≝
match t with
[ lref p   ⇒ 𝛏p
| abst b t ⇒ 𝛌ⓕ.(term_flat t)
| appl v t ⇒ ＠(term_flat v).(term_flat t)
| lift f t ⇒ 𝛗f.(term_flat t)
].

interpretation
  "flattening (term)"
  'Flat t = (term_flat t).

definition flattenable: relation2 (relation2 …) (relation2 …) ≝
           λR1,R2. ∀t1,t2. R1 t1 t2 → R2 (♭t1) (♭t2)
. 

(* Basic constructions ******************************************************)

lemma term_flat_lref (p):
      (𝛏p) = ♭(𝛏p).
//
qed.

lemma term_flat_abst (b) (t):
      (𝛌ⓕ.♭t) = ♭(𝛌b.t).
//
qed.

lemma term_flat_appl (v) (t):
      (＠♭v.♭t) = ♭(＠v.t).
//
qed.

lemma term_flat_lift (f) (t):
      (𝛗f.♭t) = ♭(𝛗f.t).
//
qed.
