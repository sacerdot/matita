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

include "basic_2/grammar/leq_leq.ma".
include "basic_2/substitution/drop.ma".

(* BASIC SLICING FOR LOCAL ENVIRONMENTS *************************************)

definition dedropable_sn: predicate (relation lenv) ≝
                          λR. ∀L1,K1,s,d,e. ⇩[s, d, e] L1 ≡ K1 → ∀K2. R K1 K2 →
                          ∃∃L2. R L1 L2 & ⇩[s, d, e] L2 ≡ K2 & L1 ⩬[d, e] L2.

(* Properties on equivalence ************************************************)

lemma leq_drop_trans_be: ∀L1,L2,d,e. L1 ⩬[d, e] L2 →
                         ∀I,K2,W,s,i. ⇩[s, 0, i] L2 ≡ K2.ⓑ{I}W →
                         d ≤ i → i < d + e →
                         ∃∃K1. K1 ⩬[0, ⫰(d+e-i)] K2 & ⇩[s, 0, i] L1 ≡ K1.ⓑ{I}W.
#L1 #L2 #d #e #H elim H -L1 -L2 -d -e
[ #d #e #J #K2 #W #s #i #H
  elim (drop_inv_atom1 … H) -H #H destruct
| #I1 #I2 #L1 #L2 #V1 #V2 #_ #_ #J #K2 #W #s #i #_ #_ #H
  elim (ylt_yle_false … H) //
| #I #L1 #L2 #V #e #HL12 #IHL12 #J #K2 #W #s #i #H #_ >yplus_O1
  elim (drop_inv_O1_pair1 … H) -H * #Hi #HLK1 [ -IHL12 | -HL12 ]
  [ #_ destruct >ypred_succ
    /2 width=3 by drop_pair, ex2_intro/
  | lapply (ylt_inv_O1 i ?) /2 width=1 by ylt_inj/
    #H <H -H #H lapply (ylt_inv_succ … H) -H
    #Hie elim (IHL12 … HLK1) -IHL12 -HLK1 // -Hie
    >yminus_succ <yminus_inj /3 width=3 by drop_drop_lt, ex2_intro/
  ]
| #I1 #I2 #L1 #L2 #V1 #V2 #d #e #_ #IHL12 #J #K2 #W #s #i #HLK2 #Hdi
  elim (yle_inv_succ1 … Hdi) -Hdi
  #Hdi #Hi <Hi >yplus_succ1 #H lapply (ylt_inv_succ … H) -H
  #Hide lapply (drop_inv_drop1_lt … HLK2 ?) -HLK2 /2 width=1 by ylt_O/
  #HLK1 elim (IHL12 … HLK1) -IHL12 -HLK1 <yminus_inj >yminus_SO2
  /4 width=3 by ylt_O, drop_drop_lt, ex2_intro/
]
qed-.

lemma leq_drop_conf_be: ∀L1,L2,d,e. L1 ⩬[d, e] L2 →
                        ∀I,K1,W,s,i. ⇩[s, 0, i] L1 ≡ K1.ⓑ{I}W →
                        d ≤ i → i < d + e →
                        ∃∃K2. K1 ⩬[0, ⫰(d+e-i)] K2 & ⇩[s, 0, i] L2 ≡ K2.ⓑ{I}W.
#L1 #L2 #d #e #HL12 #I #K1 #W #s #i #HLK1 #Hdi #Hide
elim (leq_drop_trans_be … (leq_sym … HL12) … HLK1) // -L1 -Hdi -Hide
/3 width=3 by leq_sym, ex2_intro/
qed-.

lemma drop_O1_ex: ∀K2,i,L1. |L1| = |K2| + i →
                  ∃∃L2. L1 ⩬[0, i] L2 & ⇩[i] L2 ≡ K2.
#K2 #i @(nat_ind_plus … i) -i
[ /3 width=3 by leq_O2, ex2_intro/
| #i #IHi #Y #Hi elim (drop_O1_lt (Ⓕ) Y 0) //
  #I #L1 #V #H lapply (drop_inv_O2 … H) -H #H destruct
  normalize in Hi; elim (IHi L1) -IHi
  /3 width=5 by drop_drop, leq_pair, injective_plus_l, ex2_intro/
]
qed-.

lemma dedropable_sn_TC: ∀R. dedropable_sn R → dedropable_sn (TC … R).
#R #HR #L1 #K1 #s #d #e #HLK1 #K2 #H elim H -K2
[ #K2 #HK12 elim (HR … HLK1 … HK12) -HR -K1
  /3 width=4 by inj, ex3_intro/
| #K #K2 #_ #HK2 * #L #H1L1 #HLK #H2L1 elim (HR … HLK … HK2) -HR -K
  /3 width=6 by leq_trans, step, ex3_intro/
]
qed-.

(* Inversion lemmas on equivalence ******************************************)

lemma drop_O1_inj: ∀i,L1,L2,K. ⇩[i] L1 ≡ K → ⇩[i] L2 ≡ K → L1 ⩬[i, ∞] L2.
#i @(nat_ind_plus … i) -i
[ #L1 #L2 #K #H <(drop_inv_O2 … H) -K #H <(drop_inv_O2 … H) -L1 //
| #i #IHi * [2: #L1 #I1 #V1 ] * [2,4: #L2 #I2 #V2 ] #K #HLK1 #HLK2 //
  lapply (drop_fwd_length … HLK1)
  <(drop_fwd_length … HLK2) [ /4 width=5 by drop_inv_drop1, leq_succ/ ]
  normalize <plus_n_Sm #H destruct
]
qed-.
