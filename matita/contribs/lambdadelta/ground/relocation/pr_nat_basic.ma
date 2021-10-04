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

include "ground/relocation/pr_basic.ma".
include "ground/relocation/pr_nat_uni.ma".

(* NON-NEGATIVE APPLICATION FOR PARTIAL RELOCATION MAPS *********************)

(* Constructions with pr_basic **********************************************)

lemma pr_nat_basic_lt (m) (n) (l):
      l < m → @↑❪l, 𝐛❨m,n❩❫ ≘ l.
#m @(nat_ind_succ … m) -m
[ #n #i #H elim (nlt_inv_zero_dx … H)
| #m #IH #n #l @(nat_ind_succ … l) -l
  [ #_ /2 width=2 by refl, pr_pat_refl/
  | #l #_ #H
    lapply (nlt_inv_succ_bi … H) -H #Hlm
    /3 width=7 by refl, pr_pat_push/
  ]
]
qed.

lemma pr_nat_basic_ge (m) (n) (l):
      m ≤ l → @↑❪l, 𝐛❨m,n❩❫ ≘ l+n.
#m @(nat_ind_succ … m) -m //
#m #IH #n #l #H
elim (nle_inv_succ_sn … H) -H #Hml #H >H -H
/3 width=7 by pr_nat_push/
qed.

(* Inversions with pr_basic *************************************************)

lemma pr_nat_basic_inv_lt (m) (n) (l) (k):
      l < m → @↑❪l, 𝐛❨m,n❩❫ ≘ k → l = k.
/3 width=4 by pr_nat_basic_lt, pr_nat_mono/ qed-.

lemma pr_nat_basic_inv_ge (m) (n) (l) (k):
      m ≤ l → @↑❪l, 𝐛❨m,n❩❫ ≘ k → l+n = k.
/3 width=4 by pr_nat_basic_ge, pr_nat_mono/ qed-.
