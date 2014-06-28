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

include "ground_2/ynat/ynat_plus.ma".
include "basic_2/notation/relations/lrsubeq_4.ma".
include "basic_2/substitution/drop.ma".

(* LOCAL ENVIRONMENT REFINEMENT FOR EXTENDED SUBSTITUTION *******************)

inductive lsuby: relation4 ynat ynat lenv lenv ≝
| lsuby_atom: ∀L,d,e. lsuby d e L (⋆)
| lsuby_zero: ∀I1,I2,L1,L2,V1,V2.
              lsuby 0 0 L1 L2 → lsuby 0 0 (L1.ⓑ{I1}V1) (L2.ⓑ{I2}V2)
| lsuby_pair: ∀I1,I2,L1,L2,V,e. lsuby 0 e L1 L2 →
              lsuby 0 (⫯e) (L1.ⓑ{I1}V) (L2.ⓑ{I2}V)
| lsuby_succ: ∀I1,I2,L1,L2,V1,V2,d,e.
              lsuby d e L1 L2 → lsuby (⫯d) e (L1.ⓑ{I1}V1) (L2.ⓑ{I2}V2)
.

interpretation
  "local environment refinement (extended substitution)"
  'LRSubEq L1 d e L2 = (lsuby d e L1 L2).

(* Basic properties *********************************************************)

lemma lsuby_pair_lt: ∀I1,I2,L1,L2,V,e. L1 ⊆[0, ⫰e] L2 → 0 < e →
                     L1.ⓑ{I1}V ⊆[0, e] L2.ⓑ{I2}V.
#I1 #I2 #L1 #L2 #V #e #HL12 #He <(ylt_inv_O1 … He) /2 width=1 by lsuby_pair/
qed.

lemma lsuby_succ_lt: ∀I1,I2,L1,L2,V1,V2,d,e. L1 ⊆[⫰d, e] L2 → 0 < d →
                     L1.ⓑ{I1}V1 ⊆[d, e] L2. ⓑ{I2}V2.
#I1 #I2 #L1 #L2 #V1 #V2 #d #e #HL12 #Hd <(ylt_inv_O1 … Hd) /2 width=1 by lsuby_succ/
qed.

lemma lsuby_pair_O_Y: ∀L1,L2. L1 ⊆[0, ∞] L2 →
                      ∀I1,I2,V. L1.ⓑ{I1}V ⊆[0,∞] L2.ⓑ{I2}V.
#L1 #L2 #HL12 #I1 #I2 #V lapply (lsuby_pair I1 I2 … V … HL12) -HL12 //
qed.

lemma lsuby_refl: ∀L,d,e. L ⊆[d, e] L.
#L elim L -L //
#L #I #V #IHL #d elim (ynat_cases … d) [| * #x ]
#Hd destruct /2 width=1 by lsuby_succ/
#e elim (ynat_cases … e) [| * #x ]
#He destruct /2 width=1 by lsuby_zero, lsuby_pair/
qed.

lemma lsuby_O2: ∀L2,L1,d. |L2| ≤ |L1| → L1 ⊆[d, yinj 0] L2.
#L2 elim L2 -L2 // #L2 #I2 #V2 #IHL2 * normalize
[ #d #H elim (le_plus_xSy_O_false … H)
| #L1 #I1 #V1 #d #H lapply (le_plus_to_le_r … H) -H #HL12
 elim (ynat_cases d) /3 width=1 by lsuby_zero/
 * /3 width=1 by lsuby_succ/
]
qed.

lemma lsuby_sym: ∀d,e,L1,L2. L1 ⊆[d, e] L2 → |L1| = |L2| → L2 ⊆[d, e] L1.
#d #e #L1 #L2 #H elim H -d -e -L1 -L2
[ #L1 #d #e #H >(length_inv_zero_dx … H) -L1 //
| /2 width=1 by lsuby_O2/
| #I1 #I2 #L1 #L2 #V #e #_ #IHL12 #H lapply (injective_plus_l … H)
  /3 width=1 by lsuby_pair/
| #I1 #I2 #L1 #L2 #V1 #V2 #d #e #_ #IHL12 #H lapply (injective_plus_l … H)
  /3 width=1 by lsuby_succ/
]
qed-.

(* Basic inversion lemmas ***************************************************)

fact lsuby_inv_atom1_aux: ∀L1,L2,d,e. L1 ⊆[d, e] L2 → L1 = ⋆ → L2 = ⋆.
#L1 #L2 #d #e * -L1 -L2 -d -e //
[ #I1 #I2 #L1 #L2 #V1 #V2 #_ #H destruct
| #I1 #I2 #L1 #L2 #V #e #_ #H destruct
| #I1 #I2 #L1 #L2 #V1 #V2 #d #e #_ #H destruct
]
qed-.

lemma lsuby_inv_atom1: ∀L2,d,e. ⋆ ⊆[d, e] L2 → L2 = ⋆.
/2 width=5 by lsuby_inv_atom1_aux/ qed-.

fact lsuby_inv_zero1_aux: ∀L1,L2,d,e. L1 ⊆[d, e] L2 →
                          ∀J1,K1,W1. L1 = K1.ⓑ{J1}W1 → d = 0 → e = 0 →
                          L2 = ⋆ ∨
                          ∃∃J2,K2,W2. K1 ⊆[0, 0] K2 & L2 = K2.ⓑ{J2}W2.
#L1 #L2 #d #e * -L1 -L2 -d -e /2 width=1 by or_introl/
[ #I1 #I2 #L1 #L2 #V1 #V2 #HL12 #J1 #K1 #W1 #H #_ #_ destruct
  /3 width=5 by ex2_3_intro, or_intror/
| #I1 #I2 #L1 #L2 #V #e #_ #J1 #K1 #W1 #_ #_ #H
  elim (ysucc_inv_O_dx … H)
| #I1 #I2 #L1 #L2 #V1 #V2 #d #e #_ #J1 #K1 #W1 #_ #H
  elim (ysucc_inv_O_dx … H)
]
qed-.

lemma lsuby_inv_zero1: ∀I1,K1,L2,V1. K1.ⓑ{I1}V1 ⊆[0, 0] L2 →
                       L2 = ⋆ ∨
                       ∃∃I2,K2,V2. K1 ⊆[0, 0] K2 & L2 = K2.ⓑ{I2}V2.
/2 width=9 by lsuby_inv_zero1_aux/ qed-.

fact lsuby_inv_pair1_aux: ∀L1,L2,d,e. L1 ⊆[d, e] L2 →
                          ∀J1,K1,W. L1 = K1.ⓑ{J1}W → d = 0 → 0 < e →
                          L2 = ⋆ ∨
                          ∃∃J2,K2. K1 ⊆[0, ⫰e] K2 & L2 = K2.ⓑ{J2}W.
#L1 #L2 #d #e * -L1 -L2 -d -e /2 width=1 by or_introl/
[ #I1 #I2 #L1 #L2 #V1 #V2 #_ #J1 #K1 #W #_ #_ #H
  elim (ylt_yle_false … H) //
| #I1 #I2 #L1 #L2 #V #e #HL12 #J1 #K1 #W #H #_ #_ destruct
  /3 width=4 by ex2_2_intro, or_intror/
| #I1 #I2 #L1 #L2 #V1 #V2 #d #e #_ #J1 #K1 #W #_ #H
  elim (ysucc_inv_O_dx … H)
]
qed-.

lemma lsuby_inv_pair1: ∀I1,K1,L2,V,e. K1.ⓑ{I1}V ⊆[0, e] L2 → 0 < e →
                       L2 = ⋆ ∨
                       ∃∃I2,K2. K1 ⊆[0, ⫰e] K2 & L2 = K2.ⓑ{I2}V.
/2 width=6 by lsuby_inv_pair1_aux/ qed-.

fact lsuby_inv_succ1_aux: ∀L1,L2,d,e. L1 ⊆[d, e] L2 →
                          ∀J1,K1,W1. L1 = K1.ⓑ{J1}W1 → 0 < d →
                          L2 = ⋆ ∨
                          ∃∃J2,K2,W2. K1 ⊆[⫰d, e] K2 & L2 = K2.ⓑ{J2}W2.
#L1 #L2 #d #e * -L1 -L2 -d -e /2 width=1 by or_introl/
[ #I1 #I2 #L1 #L2 #V1 #V2 #_ #J1 #K1 #W1 #_ #H
  elim (ylt_yle_false … H) //
| #I1 #I2 #L1 #L2 #V #e #_ #J1 #K1 #W1 #_ #H
  elim (ylt_yle_false … H) //
| #I1 #I2 #L1 #L2 #V1 #V2 #d #e #HL12 #J1 #K1 #W1 #H #_ destruct
  /3 width=5 by ex2_3_intro, or_intror/
]
qed-.

lemma lsuby_inv_succ1: ∀I1,K1,L2,V1,d,e. K1.ⓑ{I1}V1 ⊆[d, e] L2 → 0 < d →
                       L2 = ⋆ ∨
                       ∃∃I2,K2,V2. K1 ⊆[⫰d, e] K2 & L2 = K2.ⓑ{I2}V2.
/2 width=5 by lsuby_inv_succ1_aux/ qed-.

fact lsuby_inv_zero2_aux: ∀L1,L2,d,e. L1 ⊆[d, e] L2 →
                          ∀J2,K2,W2. L2 = K2.ⓑ{J2}W2 → d = 0 → e = 0 →
                          ∃∃J1,K1,W1. K1 ⊆[0, 0] K2 & L1 = K1.ⓑ{J1}W1.
#L1 #L2 #d #e * -L1 -L2 -d -e
[ #L1 #d #e #J2 #K2 #W1 #H destruct
| #I1 #I2 #L1 #L2 #V1 #V2 #HL12 #J2 #K2 #W2 #H #_ #_ destruct
  /2 width=5 by ex2_3_intro/
| #I1 #I2 #L1 #L2 #V #e #_ #J2 #K2 #W2 #_ #_ #H
  elim (ysucc_inv_O_dx … H)
| #I1 #I2 #L1 #L2 #V1 #V2 #d #e #_ #J2 #K2 #W2 #_ #H
  elim (ysucc_inv_O_dx … H)
]
qed-.

lemma lsuby_inv_zero2: ∀I2,K2,L1,V2. L1 ⊆[0, 0] K2.ⓑ{I2}V2 →
                       ∃∃I1,K1,V1. K1 ⊆[0, 0] K2 & L1 = K1.ⓑ{I1}V1.
/2 width=9 by lsuby_inv_zero2_aux/ qed-.

fact lsuby_inv_pair2_aux: ∀L1,L2,d,e. L1 ⊆[d, e] L2 →
                          ∀J2,K2,W. L2 = K2.ⓑ{J2}W → d = 0 → 0 < e →
                          ∃∃J1,K1. K1 ⊆[0, ⫰e] K2 & L1 = K1.ⓑ{J1}W.
#L1 #L2 #d #e * -L1 -L2 -d -e
[ #L1 #d #e #J2 #K2 #W #H destruct
| #I1 #I2 #L1 #L2 #V1 #V2 #_ #J2 #K2 #W #_ #_ #H
  elim (ylt_yle_false … H) //
| #I1 #I2 #L1 #L2 #V #e #HL12 #J2 #K2 #W #H #_ #_ destruct
  /2 width=4 by ex2_2_intro/
| #I1 #I2 #L1 #L2 #V1 #V2 #d #e #_ #J2 #K2 #W #_ #H
  elim (ysucc_inv_O_dx … H)
]
qed-.

lemma lsuby_inv_pair2: ∀I2,K2,L1,V,e. L1 ⊆[0, e] K2.ⓑ{I2}V → 0 < e →
                       ∃∃I1,K1. K1 ⊆[0, ⫰e] K2 & L1 = K1.ⓑ{I1}V.
/2 width=6 by lsuby_inv_pair2_aux/ qed-.

fact lsuby_inv_succ2_aux: ∀L1,L2,d,e. L1 ⊆[d, e] L2 →
                          ∀J2,K2,W2. L2 = K2.ⓑ{J2}W2 → 0 < d →
                          ∃∃J1,K1,W1. K1 ⊆[⫰d, e] K2 & L1 = K1.ⓑ{J1}W1.
#L1 #L2 #d #e * -L1 -L2 -d -e
[ #L1 #d #e #J2 #K2 #W2 #H destruct
| #I1 #I2 #L1 #L2 #V1 #V2 #_ #J2 #K2 #W2 #_ #H
  elim (ylt_yle_false … H) //
| #I1 #I2 #L1 #L2 #V #e #_ #J2 #K1 #W2 #_ #H
  elim (ylt_yle_false … H) //
| #I1 #I2 #L1 #L2 #V1 #V2 #d #e #HL12 #J2 #K2 #W2 #H #_ destruct
  /2 width=5 by ex2_3_intro/
]
qed-.

lemma lsuby_inv_succ2: ∀I2,K2,L1,V2,d,e. L1 ⊆[d, e] K2.ⓑ{I2}V2 → 0 < d →
                       ∃∃I1,K1,V1. K1 ⊆[⫰d, e] K2 & L1 = K1.ⓑ{I1}V1.
/2 width=5 by lsuby_inv_succ2_aux/ qed-.

(* Basic forward lemmas *****************************************************)

lemma lsuby_fwd_length: ∀L1,L2,d,e. L1 ⊆[d, e] L2 → |L2| ≤ |L1|.
#L1 #L2 #d #e #H elim H -L1 -L2 -d -e normalize /2 width=1 by le_S_S/
qed-.

(* Properties on basic slicing **********************************************)

lemma lsuby_drop_trans_be: ∀L1,L2,d,e. L1 ⊆[d, e] L2 →
                           ∀I2,K2,W,s,i. ⇩[s, 0, i] L2 ≡ K2.ⓑ{I2}W →
                           d ≤ i → i < d + e →
                           ∃∃I1,K1. K1 ⊆[0, ⫰(d+e-i)] K2 & ⇩[s, 0, i] L1 ≡ K1.ⓑ{I1}W.
#L1 #L2 #d #e #H elim H -L1 -L2 -d -e
[ #L1 #d #e #J2 #K2 #W #s #i #H
  elim (drop_inv_atom1 … H) -H #H destruct
| #I1 #I2 #L1 #L2 #V1 #V2 #_ #_ #J2 #K2 #W #s #i #_ #_ #H
  elim (ylt_yle_false … H) //
| #I1 #I2 #L1 #L2 #V #e #HL12 #IHL12 #J2 #K2 #W #s #i #H #_ >yplus_O1
  elim (drop_inv_O1_pair1 … H) -H * #Hi #HLK1 [ -IHL12 | -HL12 ]
  [ #_ destruct -I2 >ypred_succ
    /2 width=4 by drop_pair, ex2_2_intro/
  | lapply (ylt_inv_O1 i ?) /2 width=1 by ylt_inj/
    #H <H -H #H lapply (ylt_inv_succ … H) -H
    #Hie elim (IHL12 … HLK1) -IHL12 -HLK1 // -Hie
    >yminus_succ <yminus_inj /3 width=4 by drop_drop_lt, ex2_2_intro/
  ]
| #I1 #I2 #L1 #L2 #V1 #V2 #d #e #_ #IHL12 #J2 #K2 #W #s #i #HLK2 #Hdi
  elim (yle_inv_succ1 … Hdi) -Hdi
  #Hdi #Hi <Hi >yplus_succ1 #H lapply (ylt_inv_succ … H) -H
  #Hide lapply (drop_inv_drop1_lt … HLK2 ?) -HLK2 /2 width=1 by ylt_O/
  #HLK1 elim (IHL12 … HLK1) -IHL12 -HLK1 <yminus_inj >yminus_SO2
  /4 width=4 by ylt_O, drop_drop_lt, ex2_2_intro/
]
qed-.
