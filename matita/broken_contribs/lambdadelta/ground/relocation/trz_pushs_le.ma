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

include "ground/relocation/trz_pushs.ma".
include "ground/arith/int_nat_succ.ma".
include "ground/arith/int_lt_pred.ma".

(* ITERATED PUSH FOR TOTAL RELOCATION MAPS WITH INTEGERS ********************)

(* Constructions with order for integers ************************************)

lemma trz_pushs_unfold_be (n) (z) (f):
      (⁤𝟏) ≤ z → z ≤ ⊕n →
      z = (⫯*[n]f)＠⧣❨z❩.
#n @(nat_ind_succ … n) -n
[ #z #f #H1z #H2z
  elim zle_inv_pos_zero
  /2 width=4 by zle_trans/
| #n #IH #z #f #H1z <znat_succ #H2z
  elim (zle_split_lt_eq … H2z) -H2z #H2z
  [ /3 width=1 by zlt_inv_succ_dx_le/
  | destruct <trz_pushs_succ -H1z
    generalize in match IH; -IH
    cases n -n // #p #IH
    <trz_push_pos_succ <trz_after_unfold
    <IH -IH //
  ]
]
qed.
