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

include "ground/relocation/gr_pat_pat.ma".
include "ground/relocation/gr_after.ma".

(* RELATIONAL COMPOSITION FOR GENERIC RELOCATION MAPS ***********************************************************)

(* Forward lemmas on pat *****************************************************)

(*** after_at_fwd *)
lemma gr_after_pat_des (i) (i1):
      ∀f. @❪i1, f❫ ≘ i → ∀f2,f1. f2 ⊚ f1 ≘ f →
      ∃∃i2. @❪i1, f1❫ ≘ i2 & @❪i2, f2❫ ≘ i.
#i elim i -i [2: #i #IH ] #i1 #f #Hf #f2 #f1 #Hf21
[ elim (gr_pat_inv_succ_dx … Hf) -Hf [1,3:* |*: // ]
  [1: #g #j1 #Hg #H0 #H |2,4: #g #Hg #H ]
| elim (gr_pat_inv_unit_dx … Hf) -Hf //
  #g #H1 #H
]
[2: elim (gr_after_inv_next … Hf21 … H) -f *
    [ #g2 #g1 #Hg21 #H2 #H1 | #g2 #Hg21 #H2 ]
|*: elim (gr_after_inv_push … Hf21 … H) -f
    #g2 #g1 #Hg21 #H2 #H1
]
[4: -Hg21 |*: elim (IH … Hg … Hg21) -g -IH ]
/3 width=9 by gr_pat_refl, gr_pat_push, gr_pat_next, ex2_intro/
qed-.

(*** after_fwd_at *)
lemma gr_after_des_pat (i) (i2) (i1):
      ∀f1,f2. @❪i1, f1❫ ≘ i2 → @❪i2, f2❫ ≘ i →
      ∀f. f2 ⊚ f1 ≘ f → @❪i1, f❫ ≘ i.
#i elim i -i [2: #i #IH ] #i2 #i1 #f1 #f2 #Hf1 #Hf2 #f #Hf
[ elim (gr_pat_inv_succ_dx … Hf2) -Hf2 [1,3: * |*: // ]
  #g2 [ #j2 ] #Hg2 [ #H22 ] #H20
  [ elim (gr_pat_inv_succ_dx … Hf1 … H22) -i2 *
    #g1 [ #j1 ] #Hg1 [ #H11 ] #H10
    [ elim (gr_after_inv_push_bi … Hf … H20 H10) -f1 -f2 /3 width=7 by gr_pat_push/
    | elim (gr_after_inv_push_next … Hf … H20 H10) -f1 -f2 /3 width=6 by gr_pat_next/
    ]
  | elim (gr_after_inv_next_sn … Hf … H20) -f2 /3 width=7 by gr_pat_next/
  ]
| elim (gr_pat_inv_unit_dx … Hf2) -Hf2 // #g2 #H22 #H20
  elim (gr_pat_inv_unit_dx … Hf1 … H22) -i2 #g1 #H11 #H10
  elim (gr_after_inv_push_bi … Hf … H20 H10) -f1 -f2 /2 width=2 by gr_pat_refl/
]
qed-.

(*** after_fwd_at2 *)
lemma gr_after_des_pat_sn (i1) (i):
      ∀f. @❪i1, f❫ ≘ i → ∀f1,i2. @❪i1, f1❫ ≘ i2 →
      ∀f2. f2 ⊚ f1 ≘ f → @❪i2, f2❫ ≘ i.
#i1 #i #f #Hf #f1 #i2 #Hf1 #f2 #H elim (gr_after_pat_des … Hf … H) -f
#j1 #H #Hf2 <(gr_pat_mono … Hf1 … H) -i1 -i2 //
qed-.

(*** after_fwd_at1 *)
lemma gr_after_des_pat_dx (i) (i2) (i1):
      ∀f,f2. @❪i1, f❫ ≘ i → @❪i2, f2❫ ≘ i →
      ∀f1. f2 ⊚ f1 ≘ f → @❪i1, f1❫ ≘ i2.
#i elim i -i [2: #i #IH ] #i2 #i1 #f #f2 #Hf #Hf2 #f1 #Hf1
[ elim (gr_pat_inv_succ_dx … Hf) -Hf [1,3: * |*: // ]
  #g [ #j1 ] #Hg [ #H01 ] #H00
  elim (gr_pat_inv_succ_dx … Hf2) -Hf2 [1,3,5,7: * |*: // ]
  #g2 [1,3: #j2 ] #Hg2 [1,2: #H22 ] #H20
  [ elim (gr_after_inv_push_sn_push … Hf1 … H20 H00) -f2 -f /3 width=7 by gr_pat_push/
  | elim (gr_after_inv_push_sn_next … Hf1 … H20 H00) -f2 -f /3 width=5 by gr_pat_next/
  | elim (gr_after_inv_next_sn_push … Hf1 … H20 H00)
  | /4 width=9 by gr_after_inv_next_sn_next, gr_pat_next/
  ]
| elim (gr_pat_inv_unit_dx … Hf) -Hf // #g #H01 #H00
  elim (gr_pat_inv_unit_dx … Hf2) -Hf2 // #g2 #H21 #H20
  elim (gr_after_inv_push_sn_push … Hf1 … H20 H00) -f2 -f /3 width=2 by gr_pat_refl/
]
qed-.
