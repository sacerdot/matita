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

(* ADDITION FOR FINITE RELOCATION MAPS WITH PAIRS ***************************)

(* Note: this is pushs *)
(*** pluss *)
rec definition fr2_plus (f:fr2_map) (n:nat) on f â match f with
[ fr2_empty       â ð
| fr2_lcons d h f â â¨d+n,hâ©âfr2_plus f n
].

interpretation
  "plus (finite relocation maps with pairs)"
  'plus f n = (fr2_plus f n).

(* Basic constructions ******************************************************)

(*** pluss_SO2 *)
lemma fr2_plus_lcons_unit (d) (h) (f):
      ((â¨d,hâ©âf)+ð) = â¨âd,hâ©âf+ð.
normalize // qed.

(* Basic inversions *********************************************************)

(*** pluss_inv_nil2 *)
lemma fr2_plus_inv_empty_dx (n) (f):
      f+n = ð â f = ð.
#n * // normalize
#d #h #f #H destruct
qed.

(*** pluss_inv_cons2 *)
lemma fr2_plus_inv_lcons_dx (n) (d) (h) (f2) (f):
      f + n = â¨d,hâ©âf2 â
      ââf1. f1+n = f2 & f = â¨d-n,hâ©âf1.
#n #d #h #f2 *
[ normalize #H destruct
| #d1 #h1 #f1 whd in â¢ (??%?â?); #H destruct
  <nminus_plus_sn_refl_sn /2 width=3 by ex2_intro/
]
qed-.
