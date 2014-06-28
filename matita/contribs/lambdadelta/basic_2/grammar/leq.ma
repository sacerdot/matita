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

include "ground_2/ynat/ynat_lt.ma".
include "basic_2/notation/relations/midiso_4.ma".
include "basic_2/grammar/lenv_length.ma".

(* EQUIVALENCE FOR LOCAL ENVIRONMENTS ***************************************)

inductive leq: relation4 ynat ynat lenv lenv ≝
| leq_atom: ∀d,e. leq d e (⋆) (⋆)
| leq_zero: ∀I1,I2,L1,L2,V1,V2.
            leq 0 0 L1 L2 → leq 0 0 (L1.ⓑ{I1}V1) (L2.ⓑ{I2}V2)
| leq_pair: ∀I,L1,L2,V,e. leq 0 e L1 L2 →
            leq 0 (⫯e) (L1.ⓑ{I}V) (L2.ⓑ{I}V)
| leq_succ: ∀I1,I2,L1,L2,V1,V2,d,e.
            leq d e L1 L2 → leq (⫯d) e (L1.ⓑ{I1}V1) (L2.ⓑ{I2}V2)
.

interpretation
  "equivalence (local environment)"
  'MidIso d e L1 L2 = (leq d e L1 L2).

(* Basic properties *********************************************************)

lemma leq_pair_lt: ∀I,L1,L2,V,e. L1 ⩬[0, ⫰e] L2 → 0 < e →
                   L1.ⓑ{I}V ⩬[0, e] L2.ⓑ{I}V.
#I #L1 #L2 #V #e #HL12 #He <(ylt_inv_O1 … He) /2 width=1 by leq_pair/
qed.

lemma leq_succ_lt: ∀I1,I2,L1,L2,V1,V2,d,e. L1 ⩬[⫰d, e] L2 → 0 < d →
                   L1.ⓑ{I1}V1 ⩬[d, e] L2. ⓑ{I2}V2.
#I1 #I2 #L1 #L2 #V1 #V2 #d #e #HL12 #Hd <(ylt_inv_O1 … Hd) /2 width=1 by leq_succ/
qed.

lemma leq_pair_O_Y: ∀L1,L2. L1 ⩬[0, ∞] L2 →
                    ∀I,V. L1.ⓑ{I}V ⩬[0, ∞] L2.ⓑ{I}V.
#L1 #L2 #HL12 #I #V lapply (leq_pair I … V … HL12) -HL12 //
qed.

lemma leq_refl: ∀L,d,e. L ⩬[d, e] L.
#L elim L -L //
#L #I #V #IHL #d elim (ynat_cases … d) [| * #x ]
#Hd destruct /2 width=1 by leq_succ/
#e elim (ynat_cases … e) [| * #x ]
#He destruct /2 width=1 by leq_zero, leq_pair/
qed.

lemma leq_O2: ∀L1,L2,d. |L1| = |L2| → L1 ⩬[d, yinj 0] L2.
#L1 elim L1 -L1 [| #L1 #I1 #V1 #IHL1 ]
* // [1,3: #L2 #I2 #V2 ] #d normalize
[1,3: <plus_n_Sm #H destruct ]
#H lapply (injective_plus_l … H) -H #HL12
elim (ynat_cases d) /3 width=1 by leq_zero/
* /3 width=1 by leq_succ/
qed.

lemma leq_sym: ∀d,e. symmetric … (leq d e).
#d #e #L1 #L2 #H elim H -L1 -L2 -d -e
/2 width=1 by leq_zero, leq_pair, leq_succ/
qed-.

(* Basic inversion lemmas ***************************************************)

fact leq_inv_atom1_aux: ∀L1,L2,d,e. L1 ⩬[d, e] L2 → L1 = ⋆ → L2 = ⋆.
#L1 #L2 #d #e * -L1 -L2 -d -e //
[ #I1 #I2 #L1 #L2 #V1 #V2 #_ #H destruct
| #I #L1 #L2 #V #e #_ #H destruct
| #I1 #I2 #L1 #L2 #V1 #V2 #d #e #_ #H destruct
]
qed-.

lemma leq_inv_atom1: ∀L2,d,e. ⋆ ⩬[d, e] L2 → L2 = ⋆.
/2 width=5 by leq_inv_atom1_aux/ qed-.

fact leq_inv_zero1_aux: ∀L1,L2,d,e. L1 ⩬[d, e] L2 →
                        ∀J1,K1,W1. L1 = K1.ⓑ{J1}W1 → d = 0 → e = 0 →
                        ∃∃J2,K2,W2. K1 ⩬[0, 0] K2 & L2 = K2.ⓑ{J2}W2.
#L1 #L2 #d #e * -L1 -L2 -d -e
[ #d #e #J1 #K1 #W1 #H destruct
| #I1 #I2 #L1 #L2 #V1 #V2 #HL12 #J1 #K1 #W1 #H #_ #_ destruct
  /2 width=5 by ex2_3_intro/
| #I #L1 #L2 #V #e #_ #J1 #K1 #W1 #_ #_ #H
  elim (ysucc_inv_O_dx … H)
| #I1 #I2 #L1 #L2 #V1 #V2 #d #e #_ #J1 #K1 #W1 #_ #H
  elim (ysucc_inv_O_dx … H)
]
qed-.

lemma leq_inv_zero1: ∀I1,K1,L2,V1. K1.ⓑ{I1}V1 ⩬[0, 0] L2 →
                     ∃∃I2,K2,V2. K1 ⩬[0, 0] K2 & L2 = K2.ⓑ{I2}V2.
/2 width=9 by leq_inv_zero1_aux/ qed-.

fact leq_inv_pair1_aux: ∀L1,L2,d,e. L1 ⩬[d, e] L2 →
                        ∀J,K1,W. L1 = K1.ⓑ{J}W → d = 0 → 0 < e →
                        ∃∃K2. K1 ⩬[0, ⫰e] K2 & L2 = K2.ⓑ{J}W.
#L1 #L2 #d #e * -L1 -L2 -d -e
[ #d #e #J #K1 #W #H destruct
| #I1 #I2 #L1 #L2 #V1 #V2 #_ #J #K1 #W #_ #_ #H
  elim (ylt_yle_false … H) //
| #I #L1 #L2 #V #e #HL12 #J #K1 #W #H #_ #_ destruct
  /2 width=3 by ex2_intro/
| #I1 #I2 #L1 #L2 #V1 #V2 #d #e #_ #J #K1 #W #_ #H
  elim (ysucc_inv_O_dx … H)
]
qed-.

lemma leq_inv_pair1: ∀I,K1,L2,V,e. K1.ⓑ{I}V ⩬[0, e] L2 → 0 < e →
                     ∃∃K2. K1 ⩬[0, ⫰e] K2 & L2 = K2.ⓑ{I}V.
/2 width=6 by leq_inv_pair1_aux/ qed-.

lemma leq_inv_pair: ∀I1,I2,L1,L2,V1,V2,e. L1.ⓑ{I1}V1 ⩬[0, e] L2.ⓑ{I2}V2 → 0 < e →
                    ∧∧ L1 ⩬[0, ⫰e] L2 & I1 = I2 & V1 = V2.
#I1 #I2 #L1 #L2 #V1 #V2 #e #H #He elim (leq_inv_pair1 … H) -H //
#Y #HL12 #H destruct /2 width=1 by and3_intro/
qed-.

fact leq_inv_succ1_aux: ∀L1,L2,d,e. L1 ⩬[d, e] L2 →
                        ∀J1,K1,W1. L1 = K1.ⓑ{J1}W1 → 0 < d →
                        ∃∃J2,K2,W2. K1 ⩬[⫰d, e] K2 & L2 = K2.ⓑ{J2}W2.
#L1 #L2 #d #e * -L1 -L2 -d -e
[ #d #e #J1 #K1 #W1 #H destruct
| #I1 #I2 #L1 #L2 #V1 #V2 #_ #J1 #K1 #W1 #_ #H
  elim (ylt_yle_false … H) //
| #I #L1 #L2 #V #e #_ #J1 #K1 #W1 #_ #H
  elim (ylt_yle_false … H) //
| #I1 #I2 #L1 #L2 #V1 #V2 #d #e #HL12 #J1 #K1 #W1 #H #_ destruct
  /2 width=5 by ex2_3_intro/
]
qed-.

lemma leq_inv_succ1: ∀I1,K1,L2,V1,d,e. K1.ⓑ{I1}V1 ⩬[d, e] L2 → 0 < d →
                     ∃∃I2,K2,V2. K1 ⩬[⫰d, e] K2 & L2 = K2.ⓑ{I2}V2.
/2 width=5 by leq_inv_succ1_aux/ qed-.

lemma leq_inv_atom2: ∀L1,d,e. L1 ⩬[d, e] ⋆ → L1 = ⋆.
/3 width=3 by leq_inv_atom1, leq_sym/
qed-.

lemma leq_inv_succ: ∀I1,I2,L1,L2,V1,V2,d,e. L1.ⓑ{I1}V1 ⩬[d, e] L2.ⓑ{I2}V2 → 0 < d →
                    L1 ⩬[⫰d, e] L2.
#I1 #I2 #L1 #L2 #V1 #V2 #d #e #H #Hd elim (leq_inv_succ1 … H) -H //
#Z #Y #X #HL12 #H destruct //
qed-.

lemma leq_inv_zero2: ∀I2,K2,L1,V2. L1 ⩬[0, 0] K2.ⓑ{I2}V2 →
                     ∃∃I1,K1,V1. K1 ⩬[0, 0] K2 & L1 = K1.ⓑ{I1}V1.
#I2 #K2 #L1 #V2 #H elim (leq_inv_zero1 … (leq_sym … H)) -H 
/3 width=5 by leq_sym, ex2_3_intro/
qed-.

lemma leq_inv_pair2: ∀I,K2,L1,V,e. L1 ⩬[0, e] K2.ⓑ{I}V → 0 < e →
                     ∃∃K1. K1 ⩬[0, ⫰e] K2 & L1 = K1.ⓑ{I}V.
#I #K2 #L1 #V #e #H #He elim (leq_inv_pair1 … (leq_sym … H)) -H
/3 width=3 by leq_sym, ex2_intro/
qed-.

lemma leq_inv_succ2: ∀I2,K2,L1,V2,d,e. L1 ⩬[d, e] K2.ⓑ{I2}V2 → 0 < d →
                     ∃∃I1,K1,V1. K1 ⩬[⫰d, e] K2 & L1 = K1.ⓑ{I1}V1.
#I2 #K2 #L1 #V2 #d #e #H #Hd elim (leq_inv_succ1 … (leq_sym … H)) -H 
/3 width=5 by leq_sym, ex2_3_intro/
qed-.

(* Basic forward lemmas *****************************************************)

lemma leq_fwd_length: ∀L1,L2,d,e. L1 ⩬[d, e] L2 → |L1| = |L2|.
#L1 #L2 #d #e #H elim H -L1 -L2 -d -e normalize //
qed-.

(* Advanced inversion lemmas ************************************************)

fact leq_inv_O_Y_aux: ∀L1,L2,d,e. L1 ⩬[d, e] L2 → d = 0 → e = ∞ → L1 = L2.
#L1 #L2 #d #e #H elim H -L1 -L2 -d -e //
[ #I1 #I2 #L1 #L2 #V1 #V2 #_ #_ #_ #H destruct
| /4 width=1 by eq_f3, ysucc_inv_Y_dx/
| #I1 #I2 #L1 #L2 #V1 #V2 #d #e #_ #_ #H elim (ysucc_inv_O_dx … H)
]
qed-.

lemma leq_inv_O_Y: ∀L1,L2. L1 ⩬[0, ∞] L2 → L1 = L2.
/2 width=5 by leq_inv_O_Y_aux/ qed-.
