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

include "ground/arith/pnat_pred.ma".
include "ground/arith/pnat_lt.ma".
include "ground/relocation/p1/pr_pat.ma".

(* POSITIVE APPLICATION FOR PARTIAL RELOCATION MAPS *************************)

(* Destructions with plt and ple ********************************************)

(*** at_increasing *)
lemma pr_pat_increasing (i2) (i1) (f):
      ＠⧣❨i1,f❩ ≘ i2 → i1 ≤ i2.
#i2 elim i2 -i2
[ #i1 #f #Hf elim (pr_pat_inv_unit_dx … Hf) -Hf //
| #i2 #IH * //
  #i1 #f #Hf elim (pr_pat_inv_succ_bi … Hf) -Hf [1,4: * |*: // ]
  /3 width=2 by ple_succ_bi, ple_succ_dx/
]
qed-.

(*** at_increasing_strict *)
lemma pr_pat_increasing_strict (g) (i1) (i2):
      ＠⧣❨i1,g❩ ≘ i2 → ∀f. ↑f = g →
      ∧∧ i1 < i2 & ＠⧣❨i1,f❩ ≘ ⫰i2.
#g #i1 #i2 #Hg #f #H elim (pr_pat_inv_next … Hg … H) -Hg -H
/4 width=2 by conj, pr_pat_increasing, ple_succ_bi/
qed-.

(*** at_fwd_id_ex *)
lemma pr_pat_des_id (f) (i): ＠⧣❨i,f❩ ≘ i → ⫯⫰f = f.
#f elim (pr_map_split_tl f) //
#H #i #Hf elim (pr_pat_inv_next … Hf … H) -Hf -H
#j2 #Hg #H destruct lapply (pr_pat_increasing … Hg) -Hg
#H elim (plt_ge_false … H) -H //
qed-.

(* Constructions with ple ***************************************************)

(*** at_le_ex *)
lemma pr_pat_le_ex (j2) (i2) (f):
      ＠⧣❨i2,f❩ ≘ j2 → ∀i1. i1 ≤ i2 →
      ∃∃j1. ＠⧣❨i1,f❩ ≘ j1 & j1 ≤ j2.
#j2 elim j2 -j2 [2: #j2 #IH ] #i2 #f #Hf
[ elim (pr_pat_inv_succ_dx … Hf) -Hf [1,3: * |*: // ]
  #g [ #x2 ] #Hg [ #H2 ] #H0
  [ * /3 width=3 by pr_pat_refl, ex2_intro/
    #i1 #Hi12 destruct lapply (ple_inv_succ_bi … Hi12) -Hi12
    #Hi12 elim (IH … Hg … Hi12) -x2 -IH
    /3 width=7 by pr_pat_push, ex2_intro, ple_succ_bi/
  | #i1 #Hi12 elim (IH … Hg … Hi12) -IH -i2
    /3 width=5 by pr_pat_next, ex2_intro, ple_succ_bi/
  ]
| elim (pr_pat_inv_unit_dx … Hf) -Hf //
  #g * -i2 #H2 #i1 #Hi12 <(ple_inv_unit_dx … Hi12)
  /3 width=3 by pr_pat_refl, ex2_intro/
]
qed-.

(*** at_id_le *)
lemma pr_pat_id_le (i1) (i2):
      i1 ≤ i2 → ∀f. ＠⧣❨i2,f❩ ≘ i2 → ＠⧣❨i1,f❩ ≘ i1.
#i1 #i2 #H
@(ple_ind_alt … H) -i1 -i2 [ #i2 | #i1 #i2 #_ #IH ] #f #Hf
lapply (pr_pat_des_id … Hf) #H <H in Hf; -H
/4 width=7 by pr_pat_inv_succ_push_succ, pr_pat_push, pr_pat_refl/
qed-.
