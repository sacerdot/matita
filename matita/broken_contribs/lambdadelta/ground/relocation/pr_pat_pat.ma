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

include "ground/arith/pnat_lt_pred.ma".
include "ground/relocation/pr_pat.ma".

(* POSITIVE APPLICATION FOR PARTIAL RELOCATION MAPS *************************)

(* Main constructions *******************************************************)

(*** at_monotonic *)
theorem pr_pat_monotonic:
        ∀j2,i2,f. ＠⧣❨i2,f❩ ≘ j2 → ∀j1,i1. ＠⧣❨i1,f❩ ≘ j1 →
        i1 < i2 → j1 < j2.
#j2 elim j2 -j2
[ #i2 #f #H2f elim (pr_pat_inv_unit_dx … H2f) -H2f //
  #g #H21 #_ #j1 #i1 #_ #Hi elim (plt_ge_false … Hi) -Hi //
| #j2 #IH #i2 #f #H2f * //
  #j1 #i1 #H1f #Hi elim (plt_inv_gen … Hi)
  #_ #Hi2 elim (pr_pat_inv_succ_bi … H2f (⫰i2)) -H2f [1,3: * |*: // ]
  #g #H2g #H
  [ elim (pr_pat_inv_push_succ … H1f … H) -f
    /4 width=8 by plt_inv_succ_bi, plt_succ_bi/
  | /4 width=8 by pr_pat_inv_next_succ, plt_succ_bi/
  ]
]
qed-.

(*** at_inv_monotonic *)
theorem pr_pat_inv_monotonic:
        ∀j1,i1,f. ＠⧣❨i1,f❩ ≘ j1 → ∀j2,i2. ＠⧣❨i2,f❩ ≘ j2 →
        j1 < j2 → i1 < i2.
#j1 elim j1 -j1
[ #i1 #f #H1f elim (pr_pat_inv_unit_dx … H1f) -H1f //
  #g * -i1 #H #j2 #i2 #H2f #Hj lapply (plt_des_gen … Hj) -Hj
  #H22 elim (pr_pat_inv_push_succ … H2f … (⫰j2) H) -f //
| #j1 #IH *
  [ #f #H1f elim (pr_pat_inv_unit_succ … H1f) -H1f [ |*: // ]
    #g #H1g #H #j2 #i2 #H2f #Hj elim (plt_inv_succ_sn … Hj) -Hj
    /3 width=7 by pr_pat_inv_next_succ/
  | #i1 #f #H1f #j2 #i2 #H2f #Hj elim (plt_inv_succ_sn … Hj) -Hj
    #Hj #H22 elim (pr_pat_inv_succ_bi … H1f) -H1f [1,4: * |*: // ]
    #g #Hg #H
    [ elim (pr_pat_inv_push_succ … H2f … (⫰j2) H) -f
      /3 width=7 by plt_succ_bi/
    | /3 width=7 by pr_pat_inv_next_succ/
    ]
  ]
]
qed-.

(*** at_mono *)
theorem pr_pat_mono (f) (i):
        ∀i1. ＠⧣❨i,f❩ ≘ i1 → ∀i2. ＠⧣❨i,f❩ ≘ i2 → i2 = i1.
#f #i #i1 #H1 #i2 #H2 elim (pnat_split_lt_eq_gt i2 i1) //
#Hi elim (plt_ge_false i i)
/2 width=6 by pr_pat_inv_monotonic/
qed-.

(*** at_inj *)
theorem pr_pat_inj (f) (i):
        ∀i1. ＠⧣❨i1,f❩ ≘ i → ∀i2. ＠⧣❨i2,f❩ ≘ i → i1 = i2.
#f #i #i1 #H1 #i2 #H2 elim (pnat_split_lt_eq_gt i2 i1) //
#Hi elim (plt_ge_false i i)
/2 width=6 by pr_pat_monotonic/
qed-.

(*** at_div_comm *)
theorem pr_pat_div_comm (f2) (g2) (f1) (g1):
        H_pr_pat_div f2 g2 f1 g1 → H_pr_pat_div g2 f2 g1 f1.
#f2 #g2 #f1 #g1 #IH #jg #jf #j #Hg #Hf
elim (IH … Hf Hg) -IH -j /2 width=3 by ex2_intro/
qed-.

(*** at_div_pp *)
theorem pr_pat_div_push_bi (f2) (g2) (f1) (g1):
        H_pr_pat_div f2 g2 f1 g1 → H_pr_pat_div (⫯f2) (⫯g2) (⫯f1) (⫯g1).
#f2 #g2 #f1 #g1 #IH #jf #jg #j #Hf #Hg
elim (pr_pat_inv_push … Hf) -Hf [1,2: * |*: // ]
[ #H1 #H2 destruct -IH
  lapply (pr_pat_inv_push_unit … Hg ???) -Hg [4: |*: // ] #H destruct
  /3 width=3 by pr_pat_refl, ex2_intro/
| #xf #i #Hf2 #H1 #H2 destruct
  lapply (pr_pat_inv_push_succ … Hg ????) -Hg [5: * |*: // ] #xg #Hg2 #H destruct
  elim (IH … Hf2 Hg2) -IH -i /3 width=9 by pr_pat_push, ex2_intro/
]
qed-.

(*** at_div_nn *)
theorem pr_pat_div_next_bi (f2) (g2) (f1) (g1):
        H_pr_pat_div f2 g2 f1 g1 → H_pr_pat_div (↑f2) (↑g2) (f1) (g1).
#f2 #g2 #f1 #g1 #IH #jf #jg #j #Hf #Hg
elim (pr_pat_inv_next … Hf) -Hf [ |*: // ] #i #Hf2 #H destruct
lapply (pr_pat_inv_next_succ … Hg ????) -Hg [5: |*: // ] #Hg2
elim (IH … Hf2 Hg2) -IH -i /2 width=3 by ex2_intro/
qed-.

(*** at_div_np *)
theorem pr_pat_div_next_push (f2) (g2) (f1) (g1):
        H_pr_pat_div f2 g2 f1 g1 → H_pr_pat_div (↑f2) (⫯g2) (f1) (↑g1).
#f2 #g2 #f1 #g1 #IH #jf #jg #j #Hf #Hg
elim (pr_pat_inv_next … Hf) -Hf [ |*: // ] #i #Hf2 #H destruct
lapply (pr_pat_inv_push_succ … Hg ????) -Hg [5: * |*: // ] #xg #Hg2 #H destruct
elim (IH … Hf2 Hg2) -IH -i /3 width=7 by pr_pat_next, ex2_intro/
qed-.

(*** at_div_pn *)
theorem pr_pat_div_push_next (f2) (g2) (f1) (g1):
        H_pr_pat_div f2 g2 f1 g1 → H_pr_pat_div (⫯f2) (↑g2) (↑f1) (g1).
/4 width=6 by pr_pat_div_next_push, pr_pat_div_comm/ qed-.
