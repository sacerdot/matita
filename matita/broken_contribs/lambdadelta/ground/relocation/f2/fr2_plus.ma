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

include "ground/arith/nat_minus_plus.ma".
include "ground/relocation/f2/fr2_map.ma".

(* ADDITION FOR FINITE RELOCATION MAPS WITH PAIRS ***************************)

(* Note: this is pushs *)
(*** pluss *)
rec definition fr2_plus (f:fr2_map) (n:ℕ) on f ≝ match f with
[ fr2_empty       ⇒ 𝐞
| fr2_lcons d h f ⇒ ❨d+n,h❩◗fr2_plus f n
].

interpretation
  "plus (finite relocation maps with pairs)"
  'plus f n = (fr2_plus f n).

(* Basic constructions ******************************************************)

(*** pluss_SO2 *)
lemma fr2_plus_lcons_unit (d) (h) (f):
      (❨d,h❩◗f)+(⁤𝟏) = ❨⁤↑d,h❩◗(f+(⁤𝟏)).
normalize // qed.

(* Basic inversions *********************************************************)

(*** pluss_inv_nil2 *)
lemma fr2_plus_inv_empty_dx (n) (f):
      f+n = 𝐞 → f = 𝐞.
#n * // normalize
#d #h #f #H destruct
qed.

(*** pluss_inv_cons2 *)
lemma fr2_plus_inv_lcons_dx (n) (d) (h) (f2) (f):
      f + n = ❨d,h❩◗f2 →
      ∃∃f1. f1+n = f2 & f = ❨d-n,h❩◗f1.
#n #d #h #f2 *
[ normalize #H destruct
| #d1 #h1 #f1 whd in ⊢ (??%?→?); #H destruct
  <nminus_plus_sx_refl_sx /2 width=3 by ex2_intro/
]
qed-.
