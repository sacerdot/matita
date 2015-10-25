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

include "basic_2/grammar/lreq_lreq.ma".
include "basic_2/substitution/drop.ma".

(* BASIC SLICING FOR LOCAL ENVIRONMENTS *************************************)

definition dedropable_sn: predicate (relation lenv) ≝
                          λR. ∀L1,K1,s,l,m. ⬇[s, l, m] L1 ≡ K1 → ∀K2. R K1 K2 →
                          ∃∃L2. R L1 L2 & ⬇[s, l, m] L2 ≡ K2 & L1 ⩬[l, m] L2.

(* Properties on equivalence ************************************************)

lemma lreq_drop_trans_be: ∀L1,L2,l,m. L1 ⩬[l, m] L2 →
                          ∀I,K2,W,s,i. ⬇[s, 0, i] L2 ≡ K2.ⓑ{I}W →
                          l ≤ i → ∀m0. i + ⫯m0 = l + m →
                          ∃∃K1. K1 ⩬[0, m0] K2 & ⬇[s, 0, i] L1 ≡ K1.ⓑ{I}W.
#L1 #L2 #l #m #H elim H -L1 -L2 -l -m
[ #l #m #J #K2 #W #s #i #H
  elim (drop_inv_atom1 … H) -H #H destruct
| #I1 #I2 #L1 #L2 #V1 #V2 #_ #_ #J #K2 #W #s #i #_ #_ #m0
  >yplus_succ2 #H elim (ysucc_inv_O_dx … H)
| #I #L1 #L2 #V #m #HL12 #IHL12 #J #K2 #W #s #i #H #_ >yplus_O1 #m0 #H0
  elim (drop_inv_O1_pair1 … H) -H * #Hi #HLK1 [ -IHL12 | -HL12 ]
  [ destruct
    /2 width=3 by drop_pair, ex2_intro/
  | lapply (ylt_inv_O1 … Hi) #H <H in H0; -H
    >yplus_succ1 #H lapply (ysucc_inv_inj … H) -H <(yplus_O1 m)
    #H0 elim (IHL12 … HLK1 … H0) -IHL12 -HLK1 -H0 //
    /3 width=3 by drop_drop_lt, ex2_intro/
  ]
| #I1 #I2 #L1 #L2 #V1 #V2 #l #m #_ #IHL12 #J #K2 #W #s #i #HLK2 #Hli #m0
  elim (yle_inv_succ1 … Hli) -Hli
  #Hli #Hi <Hi >yplus_succ1 >yplus_succ1 #H lapply (ysucc_inv_inj … H) -H
  #H0 lapply (drop_inv_drop1_lt … HLK2 ?) -HLK2 /2 width=1 by ylt_O1/
  #HLK1 elim (IHL12 … HLK1 … H0) -IHL12 -HLK1 -H0
  /4 width=3 by ylt_O1, drop_drop_lt, ex2_intro/
]
qed-.

lemma lreq_drop_conf_be: ∀L1,L2,l,m. L1 ⩬[l, m] L2 →
                         ∀I,K1,W,s,i. ⬇[s, 0, i] L1 ≡ K1.ⓑ{I}W →
                         l ≤ i → ∀m0. i + ⫯m0 = l + m →
                         ∃∃K2. K1 ⩬[0, m0] K2 & ⬇[s, 0, i] L2 ≡ K2.ⓑ{I}W.
#L1 #L2 #l #m #HL12 #I #K1 #W #s #i #HLK1 #Hli #m0 #H0
elim (lreq_drop_trans_be … (lreq_sym … HL12) … HLK1 … H0) // -L1 -Hli -H0
/3 width=3 by lreq_sym, ex2_intro/
qed-.

lemma drop_O1_ex: ∀K2,i,L1. |L1| = |K2| + i →
                  ∃∃L2. L1 ⩬[0, i] L2 & ⬇[i] L2 ≡ K2.
#K2 #i @(ynat_ind … i) -i
[ /3 width=3 by lreq_O2, ex2_intro/
| #i #IHi #Y >yplus_succ2 #Hi
  elim (drop_O1_lt (Ⓕ) Y 0) [2: >Hi // ]
  #I #L1 #V #H lapply (drop_inv_O2 … H) -H #H destruct
  >length_pair in Hi; #H lapply (ysucc_inv_inj … H) -H
  #HL1K2 elim (IHi L1) -IHi // -HL1K2
  /3 width=5 by lreq_pair, drop_drop, ex2_intro/
| #L1 >yplus_Y2 #H elim (ylt_yle_false (|L1|) (∞)) //
]
qed-.

lemma dedropable_sn_TC: ∀R. dedropable_sn R → dedropable_sn (TC … R).
#R #HR #L1 #K1 #s #l #m #HLK1 #K2 #H elim H -K2
[ #K2 #HK12 elim (HR … HLK1 … HK12) -HR -K1
  /3 width=4 by inj, ex3_intro/
| #K #K2 #_ #HK2 * #L #H1L1 #HLK #H2L1 elim (HR … HLK … HK2) -HR -K
  /3 width=6 by lreq_trans, step, ex3_intro/
]
qed-.

(* Inversion lemmas on equivalence ******************************************)

lemma drop_O1_inj: ∀i,L1,L2,K. ⬇[i] L1 ≡ K → ⬇[i] L2 ≡ K → L1 ⩬[i, ∞] L2.
#i @(ynat_ind … i) -i
[ #L1 #L2 #K #H <(drop_inv_O2 … H) -K #H <(drop_inv_O2 … H) -L1 //
| #i #IHi * [2: #L1 #I1 #V1 ] * [2,4: #L2 #I2 #V2 ] #K #HLK1 #HLK2 //
  lapply (drop_fwd_length … HLK1)
  <(drop_fwd_length … HLK2) [ /4 width=5 by drop_inv_drop1, lreq_succ/ ]
  #H [ elim (ysucc_inv_O_sn … H) | elim (ysucc_inv_O_dx … H) ]
| #L1 #L2 #K #H1 lapply (drop_fwd_Y2 … H1) -H1
  #H elim (ylt_yle_false … H) //
]
qed-.
