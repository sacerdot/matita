(**************************************************************************)
(*       ___                                                              *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||         The HELM team.                                      *)
(*      ||A||         http://helm.tcs.unibo.it                            *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU General Public License Version 2                  *)
(*                                                                        *)
(**************************************************************************)

include "ground/notation/relations/ratsucc_3.ma".
include "ground/arith/nat_lt_pred.ma".
include "ground/relocation/rtmap_at.ma".

(* NON-NEGATIVE APPLICATION FOR RELOCATION MAPS *****************************)

definition rm_nat: relation3 rtmap nat nat ≝
           λf,l1,l2. @❪↑l1,f❫ ≘ ↑l2.

interpretation
  "relational non-negative application (relocation maps)"
  'RAtSucc l1 f l2 = (rm_nat f l1 l2).

(* Basic properties *********************************************************)

lemma rm_nat_refl (f) (g) (k1) (k2):
      (⫯f) = g → 𝟎 = k1 → 𝟎 = k2 → @↑❪k1,g❫ ≘ k2.
#f #g #k1 #k2 #H1 #H2 #H3 destruct
/2 width=2 by at_refl/
qed.

lemma rm_nat_push (f) (l1) (l2) (g) (k1) (k2):
      @↑❪l1,f❫ ≘ l2 → ⫯f = g → ↑l1 = k1 → ↑l2 = k2 → @↑❪k1,g❫ ≘ k2.
#f #l1 #l2 #g #k1 #k2 #Hf #H1 #H2 #H3 destruct
/2 width=7 by at_push/
qed.

lemma rm_nat_next (f) (l1) (l2) (g) (k2):
      @↑❪l1,f❫ ≘ l2 → ↑f = g → ↑l2 = k2 → @↑❪l1,g❫ ≘ k2.
#f #l1 #l2 #g #k2 #Hf #H1 #H2 destruct
/2 width=5 by at_next/
qed.

lemma rm_nat_pred_bi (f) (i1) (i2):
      @❪i1,f❫ ≘ i2 → @↑❪↓i1,f❫ ≘ ↓i2.
#f #i1 #i2
>(npsucc_pred i1) in ⊢ (%→?); >(npsucc_pred i2) in ⊢ (%→?);
//
qed.

(* Basic inversion lemmas ***************************************************)

lemma rm_nat_inv_ppx (f) (l1) (l2):
      @↑❪l1,f❫ ≘ l2 → ∀g. 𝟎 = l1 → ⫯g = f → 𝟎 = l2.
#f #l1 #l2 #H #g #H1 #H2 destruct
lapply (at_inv_ppx … H ???) -H
/2 width=2 by eq_inv_npsucc_bi/
qed-.

lemma rm_nat_inv_npx (f) (l1) (l2):
      @↑❪l1,f❫ ≘ l2 → ∀g,k1. ↑k1 = l1 → ⫯g = f →
      ∃∃k2. @↑❪k1,g❫ ≘ k2 & ↑k2 = l2.
#f #l1 #l2 #H #g #k1 #H1 #H2 destruct
elim (at_inv_npx … H) -H [|*: // ] #k2 #Hg
>(npsucc_pred (↑l2)) #H
@(ex2_intro … (↓k2)) //
<pnpred_psucc //
qed-.

lemma rm_nat_inv_xnx (f) (l1) (l2):
      @↑❪l1,f❫ ≘ l2 → ∀g. ↑g = f →
      ∃∃k2. @↑❪l1,g❫ ≘ k2 & ↑k2 = l2.
#f #l1 #l2 #H #g #H1 destruct
elim (at_inv_xnx … H) -H [|*: // ] #k2
>(npsucc_pred (k2)) in ⊢ (%→?→?); #Hg #H
@(ex2_intro … (↓k2)) //
<pnpred_psucc //
qed-.

(* Advanced inversion lemmas ************************************************)

lemma rm_nat_inv_ppn (f) (l1) (l2):
      @↑❪l1,f❫ ≘ l2 → ∀g,k2. 𝟎 = l1 → ⫯g = f → ↑k2 = l2 → ⊥.
#f #l1 #l2 #Hf #g #k2 #H1 #H <(rm_nat_inv_ppx … Hf … H1 H) -f -g -l1 -l2
/2 width=3 by eq_inv_nsucc_zero/
qed-.

lemma rm_nat_inv_npp (f) (l1) (l2):
      @↑❪l1,f❫ ≘ l2 → ∀g,k1. ↑k1 = l1 → ⫯g = f → 𝟎 = l2 → ⊥.
#f #l1 #l2 #Hf #g #k1 #H1 #H elim (rm_nat_inv_npx … Hf … H1 H) -f -l1
#x2 #Hg * -l2 /2 width=3 by eq_inv_zero_nsucc/
qed-.

lemma rm_nat_inv_npn (f) (l1) (l2):
      @↑❪l1,f❫ ≘ l2 → ∀g,k1,k2. ↑k1 = l1 → ⫯g = f → ↑k2 = l2 → @↑❪k1,g❫ ≘ k2.
#f #l1 #l2 #Hf #g #k1 #k2 #H1 #H elim (rm_nat_inv_npx … Hf … H1 H) -f -l1
#x2 #Hg * -l2 #H >(eq_inv_nsucc_bi … H) -k2 //
qed-.

lemma rm_nat_inv_xnp (f) (l1) (l2):
      @↑❪l1,f❫ ≘ l2 → ∀g. ↑g = f → 𝟎 = l2 → ⊥.
#f #l1 #l2 #Hf #g #H elim (rm_nat_inv_xnx … Hf … H) -f
#x2 #Hg * -l2 /2 width=3 by eq_inv_zero_nsucc/
qed-.

lemma rm_nat_inv_xnn (f) (l1) (l2):
      @↑❪l1,f❫ ≘ l2 → ∀g,k2. ↑g = f → ↑k2 = l2 → @↑❪l1,g❫ ≘ k2.
#f #l1 #l2 #Hf #g #k2 #H elim (rm_nat_inv_xnx … Hf … H) -f
#x2 #Hg * -l2 #H >(eq_inv_nsucc_bi … H) -k2 //
qed-.

lemma rm_nat_inv_pxp (f) (l1) (l2):
      @↑❪l1,f❫ ≘ l2 → 𝟎 = l1 → 𝟎 = l2 → ∃g. ⫯g = f.
#f elim (pn_split … f) * /2 width=2 by ex_intro/
#g #H #l1 #l2 #Hf #H1 #H2 cases (rm_nat_inv_xnp … Hf … H H2)
qed-.

lemma rm_nat_inv_pxn (f) (l1) (l2):
      @↑❪l1,f❫ ≘ l2 → ∀k2. 𝟎 = l1 → ↑k2 = l2 →
      ∃∃g. @↑❪l1,g❫ ≘ k2 & ↑g = f.
#f elim (pn_split … f) *
#g #H #l1 #l2 #Hf #k2 #H1 #H2
[ elim (rm_nat_inv_ppn … Hf … H1 H H2)
| /3 width=5 by rm_nat_inv_xnn, ex2_intro/
]
qed-.

lemma rm_nat_inv_nxp (f) (l1) (l2):
      @↑❪l1,f❫ ≘ l2 → ∀k1. ↑k1 = l1 → 𝟎 = l2 → ⊥.
#f elim (pn_split f) *
#g #H #l1 #l2 #Hf #k1 #H1 #H2
[ elim (rm_nat_inv_npp … Hf … H1 H H2)
| elim (rm_nat_inv_xnp … Hf … H H2)
]
qed-.

lemma rm_nat_inv_nxn (f) (l1) (l2):
      @↑❪l1,f❫ ≘ l2 → ∀k1,k2. ↑k1 = l1 → ↑k2 = l2 →
      ∨∨ ∃∃g. @↑❪k1,g❫ ≘ k2 & ⫯g = f
       | ∃∃g. @↑❪l1,g❫ ≘ k2 & ↑g = f.
#f elim (pn_split f) *
/4 width=7 by rm_nat_inv_xnn, rm_nat_inv_npn, ex2_intro, or_intror, or_introl/
qed-.

(* Note: the following inversion lemmas must be checked *)
lemma rm_nat_inv_xpx (f) (l1) (l2):
      @↑❪l1,f❫ ≘ l2 → ∀g. ⫯g = f →
      ∨∨ ∧∧ 𝟎 = l1 & 𝟎 = l2
       | ∃∃k1,k2. @↑❪k1,g❫ ≘ k2 & ↑k1 = l1 & ↑k2 = l2.
#f * [2: #l1 ] #l2 #Hf #g #H
[ elim (rm_nat_inv_npx … Hf … H) -f /3 width=5 by or_intror, ex3_2_intro/
| >(rm_nat_inv_ppx … Hf … H) -f /3 width=1 by conj, or_introl/
]
qed-.

lemma rm_nat_inv_xpp (f) (l1) (l2):
      @↑❪l1,f❫ ≘ l2 → ∀g. ⫯g = f → 𝟎 = l2 → 𝟎 = l1.
#f #l1 #l2 #Hf #g #H elim (rm_nat_inv_xpx … Hf … H) -f * //
#k1 #k2 #_ #_ * -l2 #H elim (eq_inv_zero_nsucc … H)
qed-.

lemma rm_nat_inv_xpn (f) (l1) (l2):
      @↑❪l1,f❫ ≘ l2 → ∀g,k2. ⫯g = f → ↑k2 = l2 →
      ∃∃k1. @↑❪k1,g❫ ≘ k2 & ↑k1 = l1.
#f #l1 #l2 #Hf #g #k2 #H elim (rm_nat_inv_xpx … Hf … H) -f *
[ #_ * -l2 #H elim (eq_inv_nsucc_zero … H)
| #x1 #x2 #Hg #H1 * -l2 #H
  lapply (eq_inv_nsucc_bi … H) -H #H destruct
  /2 width=3 by ex2_intro/
]
qed-.

lemma rm_nat_inv_xxp (f) (l1) (l2):
      @↑❪l1,f❫ ≘ l2 → 𝟎 = l2 → ∃∃g. 𝟎 = l1 & ⫯g = f.
#f elim (pn_split f) *
#g #H #l1 #l2 #Hf #H2
[ /3 width=6 by rm_nat_inv_xpp, ex2_intro/
| elim (rm_nat_inv_xnp … Hf … H H2)
]
qed-.

lemma rm_nat_inv_xxn (f) (l1) (l2): @↑❪l1,f❫ ≘ l2 → ∀k2.  ↑k2 = l2 →
      ∨∨ ∃∃g,k1. @↑❪k1,g❫ ≘ k2 & ↑k1 = l1 & ⫯g = f
       | ∃∃g. @↑❪l1,g❫ ≘ k2 & ↑g = f.
#f elim (pn_split f) *
#g #H #l1 #l2 #Hf #k2 #H2
[ elim (rm_nat_inv_xpn … Hf … H H2) -l2 /3 width=5 by or_introl, ex3_2_intro/
| lapply (rm_nat_inv_xnn … Hf … H H2) -l2 /3 width=3 by or_intror, ex2_intro/
]
qed-.

(* Main destructions ********************************************************)

theorem rm_nat_monotonic (k2) (l2) (f):
        @↑❪l2,f❫ ≘ k2 → ∀k1,l1. @↑❪l1,f❫ ≘ k1 → l1 < l2 → k1 < k2.
#k2 @(nat_ind_succ … k2) -k2
[ #l2 #f #H2f elim (rm_nat_inv_xxp … H2f) -H2f //
  #g #H21 #_ #k1 #l1 #_ #Hi destruct
  elim (nlt_inv_zero_dx … Hi)
| #k2 #IH #l2 #f #H2f #k1 @(nat_ind_succ … k1) -k1 //
  #k1 #_ #l1 #H1f #Hl elim (nlt_inv_gen … Hl)
  #_ #Hl2 elim (rm_nat_inv_nxn … H2f (↓l2)) -H2f [1,3: * |*: // ]
  #g #H2g #H
  [ elim (rm_nat_inv_xpn … H1f … H) -f
    /4 width=8 by nlt_inv_succ_bi, nlt_succ_bi/
  | /4 width=8 by rm_nat_inv_xnn, nlt_succ_bi/
  ]
]
qed-.

theorem rm_nat_inv_monotonic (k1) (l1) (f):
        @↑❪l1,f❫ ≘ k1 → ∀k2,l2. @↑❪l2,f❫ ≘ k2 → k1 < k2 → l1 < l2.
#k1 @(nat_ind_succ … k1) -k1
[ #l1 #f #H1f elim (rm_nat_inv_xxp … H1f) -H1f //
  #g * -l1 #H #k2 #l2 #H2f #Hk
  lapply (nlt_des_gen … Hk) -Hk #H22
  elim (rm_nat_inv_xpn … H2f … (↓k2) H) -f //
| #k1 #IH #l1 @(nat_ind_succ … l1) -l1
  [ #f #H1f elim (rm_nat_inv_pxn … H1f) -H1f [ |*: // ]
    #g #H1g #H #k2 #l2 #H2f #Hj elim (nlt_inv_succ_sn … Hj) -Hj
    /3 width=7 by rm_nat_inv_xnn/
  | #l1 #_ #f #H1f #k2 #l2 #H2f #Hj elim (nlt_inv_succ_sn … Hj) -Hj
    #Hj #H22 elim (rm_nat_inv_nxn … H1f) -H1f [1,4: * |*: // ]
    #g #Hg #H
    [ elim (rm_nat_inv_xpn … H2f … (↓k2) H) -f
      /3 width=7 by nlt_succ_bi/
    | /3 width=7 by rm_nat_inv_xnn/
    ]
  ]
]
qed-.

theorem rm_nat_mono (f) (l) (l1) (l2):
        @↑❪l,f❫ ≘ l1 → @↑❪l,f❫ ≘ l2 → l2 = l1.
#f #l #l1 #l2 #H1 #H2 elim (nat_split_lt_eq_gt l2 l1) //
#Hi elim (nlt_ge_false l l) /3 width=6 by rm_nat_inv_monotonic, eq_sym/
qed-.

theorem rm_nat_inj (f) (l1) (l2) (l):
        @↑❪l1,f❫ ≘ l → @↑❪l2,f❫ ≘ l → l1 = l2.
#f #l1 #l2 #l #H1 #H2 elim (nat_split_lt_eq_gt l2 l1) //
#Hi elim (nlt_ge_false l l) /2 width=6 by rm_nat_monotonic/
qed-.
