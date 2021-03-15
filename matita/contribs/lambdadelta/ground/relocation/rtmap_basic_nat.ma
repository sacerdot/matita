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

include "ground/relocation/rtmap_nat_uni.ma".
include "ground/relocation/rtmap_basic.ma".

(* RELOCATION MAP ***********************************************************)

(* Prioerties with application **********************************************)

lemma rm_nat_basic_lt (m) (n) (l):
      l < m → @↑❪l, 𝐁❨m,n❩❫ ≘ l.
#m @(nat_ind_succ … m) -m
[ #n #i #H elim (nlt_inv_zero_dx … H)
| #m #IH #n #l @(nat_ind_succ … l) -l
  [ #_ /2 width=2 by refl, at_refl/
  | #l #_ #H
    lapply (nlt_inv_succ_bi … H) -H #Hlm
    /3 width=7 by refl, at_push/
  ]
]
qed.

lemma rm_nat_basic_ge (m) (n) (l):
      m ≤ l → @↑❪l, 𝐁❨m,n❩❫ ≘ l+n.
#m @(nat_ind_succ … m) -m //
#m #IH #n #l #H
elim (nle_inv_succ_sn … H) -H #Hml #H >H -H
/3 width=7 by rm_nat_push/
qed.

(* Inversion lemmas with application ****************************************)

lemma rm_nat_basic_inv_lt (m) (n) (l) (k):
      l < m → @↑❪l, 𝐁❨m,n❩❫ ≘ k → l = k.
/3 width=4 by rm_nat_basic_lt, rm_nat_mono/ qed-.

lemma rm_nat_basic_inv_ge (m) (n) (l) (k):
      m ≤ l → @↑❪l, 𝐁❨m,n❩❫ ≘ k → l+n = k.
/3 width=4 by rm_nat_basic_ge, rm_nat_mono/ qed-.
