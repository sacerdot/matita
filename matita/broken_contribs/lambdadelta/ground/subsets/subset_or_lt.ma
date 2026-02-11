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

include "ground/subsets/subset_lt.ma".
include "ground/subsets/subset_or_le.ma".

(* UNION FOR SUBSETS ********************************************************)

(* Constructions with subset_lt and subset_ol *******************************)

lemma subset_lt_or_bi_sx (A) (u1) (u2) (v): (**)
      v ⧸≬❪A❫ u2 → u1 ⊂ u2 → v ∪ u1 ⊂ v ∪ u2.
#A #u1 #u2 #v #Hu2 * #Hu #H0
@subset_lt_mk
[ /2 width=5 by subset_or_le_repl/
| elim (subsets_inh_inv_in … H0) -H0 #a * #Ha #Hna
  @(subsets_inh_in … a)
  @subset_in_nimp
  [ /2 width=1 by subset_or_in_dx/
  | /4 width=7 by subset_nin_or, subset_ol_i/
  ]
]
qed.

lemma subset_lt_or_bi_dx (A) (u1) (u2) (v): (**)
      v ⧸≬❪A❫ u2 → u1 ⊂ u2 → u1 ∪ v ⊂ u2 ∪ v.
#A #u1 #u2 #v #Hu2 * #Hu #H0
@subset_lt_mk
[ /2 width=5 by subset_or_le_repl/
| elim (subsets_inh_inv_in … H0) -H0 #a * #Ha #Hna
  @(subsets_inh_in … a)
  @subset_in_nimp
  [ /2 width=1 by subset_or_in_sx/
  | /4 width=7 by subset_nin_or, subset_ol_i/
  ]
]
qed.
