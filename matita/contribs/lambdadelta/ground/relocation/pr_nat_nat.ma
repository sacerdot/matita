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

include "ground/arith/nat_lt_pred.ma".
include "ground/relocation/pr_nat.ma".

(* NON-NEGATIVE APPLICATION FOR PARTIAL RELOCATION MAPS *****************************)

(* Main destructions ********************************************************)

theorem pr_nat_monotonic (k2) (l2) (f):
        @↑❪l2,f❫ ≘ k2 → ∀k1,l1. @↑❪l1,f❫ ≘ k1 → l1 < l2 → k1 < k2.
#k2 @(nat_ind_succ … k2) -k2
[ #l2 #f #H2f elim (pr_nat_inv_zero_dx … H2f) -H2f //
  #g #H21 #_ #k1 #l1 #_ #Hi destruct
  elim (nlt_inv_zero_dx … Hi)
| #k2 #IH #l2 #f #H2f #k1 @(nat_ind_succ … k1) -k1 //
  #k1 #_ #l1 #H1f #Hl elim (nlt_inv_gen … Hl)
  #_ #Hl2 elim (pr_nat_inv_succ_bi … H2f (↓l2)) -H2f [1,3: * |*: // ]
  #g #H2g #H
  [ elim (pr_nat_inv_push_succ … H1f … H) -f
    /4 width=8 by nlt_inv_succ_bi, nlt_succ_bi/
  | /4 width=8 by pr_nat_inv_next_succ, nlt_succ_bi/
  ]
]
qed-.

theorem pr_nat_inv_monotonic (k1) (l1) (f):
        @↑❪l1,f❫ ≘ k1 → ∀k2,l2. @↑❪l2,f❫ ≘ k2 → k1 < k2 → l1 < l2.
#k1 @(nat_ind_succ … k1) -k1
[ #l1 #f #H1f elim (pr_nat_inv_zero_dx … H1f) -H1f //
  #g * -l1 #H #k2 #l2 #H2f #Hk
  lapply (nlt_des_gen … Hk) -Hk #H22
  elim (pr_nat_inv_push_succ … H2f … (↓k2) H) -f //
| #k1 #IH #l1 @(nat_ind_succ … l1) -l1
  [ #f #H1f elim (pr_nat_inv_zero_succ … H1f) -H1f [ |*: // ]
    #g #H1g #H #k2 #l2 #H2f #Hj elim (nlt_inv_succ_sn … Hj) -Hj
    /3 width=7 by pr_nat_inv_next_succ/
  | #l1 #_ #f #H1f #k2 #l2 #H2f #Hj elim (nlt_inv_succ_sn … Hj) -Hj
    #Hj #H22 elim (pr_nat_inv_succ_bi … H1f) -H1f [1,4: * |*: // ]
    #g #Hg #H
    [ elim (pr_nat_inv_push_succ … H2f … (↓k2) H) -f
      /3 width=7 by nlt_succ_bi/
    | /3 width=7 by pr_nat_inv_next_succ/
    ]
  ]
]
qed-.

theorem pr_nat_mono (f) (l) (l1) (l2):
        @↑❪l,f❫ ≘ l1 → @↑❪l,f❫ ≘ l2 → l2 = l1.
#f #l #l1 #l2 #H1 #H2 elim (nat_split_lt_eq_gt l2 l1) //
#Hi elim (nlt_ge_false l l)
/2 width=6 by pr_nat_inv_monotonic/
qed-.

theorem pr_nat_inj (f) (l1) (l2) (l):
        @↑❪l1,f❫ ≘ l → @↑❪l2,f❫ ≘ l → l1 = l2.
#f #l1 #l2 #l #H1 #H2 elim (nat_split_lt_eq_gt l2 l1) //
#Hi elim (nlt_ge_false l l)
/2 width=6 by pr_nat_monotonic/
qed-.
