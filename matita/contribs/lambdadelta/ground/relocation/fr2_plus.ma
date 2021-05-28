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
include "ground/relocation/fr2_map.ma".

(* ADDITION FOR FINITE RELOCATION MAPS WITH PAIRS ******************************)

(* Note: this is pushs *)
(*** pluss *)
rec definition fr2_plus (f:fr2_map) (n:nat) on f ≝ match f with
[ fr2_nil        ⇒ ◊
| fr2_cons d h f ⇒ ❨d+n,h❩;fr2_plus f n
].

interpretation
  "plus (finite relocation maps with pairs)"
  'plus f n = (fr2_plus f n).

(* Basic properties *********************************************************)

(*** pluss_SO2 *)
lemma fr2_plus_cons_unit (d) (h) (f):
      ((❨d,h❩;f)+𝟏) = ❨↑d,h❩;f+𝟏.
normalize // qed.

(* Basic inversion lemmas ***************************************************)

(*** pluss_inv_nil2 *)
lemma fr2_plus_inv_nil_dx (n) (f):
      f+n = ◊ → f = ◊.
#n * // normalize
#d #h #f #H destruct
qed.

(*** pluss_inv_cons2 *)
lemma fr2_plus_inv_cons_dx (n) (d) (h) (f2) (f):
      f + n = ❨d,h❩;f2 →
      ∃∃f1. f1+n = f2 & f = ❨d-n,h❩;f1.
#n #d #h #f2 *
[ normalize #H destruct
| #d1 #h1 #f1 whd in ⊢ (??%?→?); #H destruct
  <nminus_plus_sn_refl_sn /2 width=3 by ex2_intro/
]
qed-.
