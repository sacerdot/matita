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

include "ground_2A/ynat/ynat_lt.ma".
include "basic_2A/notation/relations/midiso_4.ma".
include "basic_2A/grammar/lenv_length.ma".

(* EQUIVALENCE FOR LOCAL ENVIRONMENTS ***************************************)

inductive lreq: relation4 ynat ynat lenv lenv ≝
| lreq_atom: ∀l,m. lreq l m (⋆) (⋆)
| lreq_zero: ∀I1,I2,L1,L2,V1,V2.
             lreq 0 0 L1 L2 → lreq 0 0 (L1.ⓑ{I1}V1) (L2.ⓑ{I2}V2)
| lreq_pair: ∀I,L1,L2,V,m. lreq 0 m L1 L2 →
             lreq 0 (⫯m) (L1.ⓑ{I}V) (L2.ⓑ{I}V)
| lreq_succ: ∀I1,I2,L1,L2,V1,V2,l,m.
             lreq l m L1 L2 → lreq (⫯l) m (L1.ⓑ{I1}V1) (L2.ⓑ{I2}V2)
.

interpretation
  "equivalence (local environment)"
  'MidIso l m L1 L2 = (lreq l m L1 L2).

(* Basic properties *********************************************************)

lemma lreq_pair_lt: ∀I,L1,L2,V,m. L1 ⩬[0, ⫰m] L2 → 0 < m →
                    L1.ⓑ{I}V ⩬[0, m] L2.ⓑ{I}V.
#I #L1 #L2 #V #m #HL12 #Hm <(ylt_inv_O1 … Hm) /2 width=1 by lreq_pair/
qed.

lemma lreq_succ_lt: ∀I1,I2,L1,L2,V1,V2,l,m. L1 ⩬[⫰l, m] L2 → 0 < l →
                    L1.ⓑ{I1}V1 ⩬[l, m] L2. ⓑ{I2}V2.
#I1 #I2 #L1 #L2 #V1 #V2 #l #m #HL12 #Hl <(ylt_inv_O1 … Hl) /2 width=1 by lreq_succ/
qed.

lemma lreq_pair_O_Y: ∀L1,L2. L1 ⩬[0, ∞] L2 →
                     ∀I,V. L1.ⓑ{I}V ⩬[0, ∞] L2.ⓑ{I}V.
#L1 #L2 #HL12 #I #V lapply (lreq_pair I … V … HL12) -HL12 //
qed.

lemma lreq_refl: ∀L,l,m. L ⩬[l, m] L.
#L elim L -L //
#L #I #V #IHL #l elim (ynat_cases … l) [| * #x ]
#Hl destruct /2 width=1 by lreq_succ/
#m elim (ynat_cases … m) [| * #x ]
#Hm destruct /2 width=1 by lreq_zero, lreq_pair/
qed.

lemma lreq_O2: ∀L1,L2,l. |L1| = |L2| → L1 ⩬[l, yinj 0] L2.
#L1 elim L1 -L1 [| #L1 #I1 #V1 #IHL1 ]
* // [1,3: #L2 #I2 #V2 ] #l normalize
[1,3: <plus_n_Sm #H destruct ]
#H lapply (injective_plus_l … H) -H #HL12
elim (ynat_cases l) /3 width=1 by lreq_zero/
* /3 width=1 by lreq_succ/
qed.

lemma lreq_sym: ∀l,m. symmetric … (lreq l m).
#l #m #L1 #L2 #H elim H -L1 -L2 -l -m
/2 width=1 by lreq_zero, lreq_pair, lreq_succ/
qed-.

(* Basic inversion lemmas ***************************************************)

fact lreq_inv_atom1_aux: ∀L1,L2,l,m. L1 ⩬[l, m] L2 → L1 = ⋆ → L2 = ⋆.
#L1 #L2 #l #m * -L1 -L2 -l -m //
[ #I1 #I2 #L1 #L2 #V1 #V2 #_ #H destruct
| #I #L1 #L2 #V #m #_ #H destruct
| #I1 #I2 #L1 #L2 #V1 #V2 #l #m #_ #H destruct
]
qed-.

lemma lreq_inv_atom1: ∀L2,l,m. ⋆ ⩬[l, m] L2 → L2 = ⋆.
/2 width=5 by lreq_inv_atom1_aux/ qed-.

fact lreq_inv_zero1_aux: ∀L1,L2,l,m. L1 ⩬[l, m] L2 →
                         ∀J1,K1,W1. L1 = K1.ⓑ{J1}W1 → l = 0 → m = 0 →
                         ∃∃J2,K2,W2. K1 ⩬[0, 0] K2 & L2 = K2.ⓑ{J2}W2.
#L1 #L2 #l #m * -L1 -L2 -l -m
[ #l #m #J1 #K1 #W1 #H destruct
| #I1 #I2 #L1 #L2 #V1 #V2 #HL12 #J1 #K1 #W1 #H #_ #_ destruct
  /2 width=5 by ex2_3_intro/
| #I #L1 #L2 #V #m #_ #J1 #K1 #W1 #_ #_ #H
  elim (ysucc_inv_O_dx … H)
| #I1 #I2 #L1 #L2 #V1 #V2 #l #m #_ #J1 #K1 #W1 #_ #H
  elim (ysucc_inv_O_dx … H)
]
qed-.

lemma lreq_inv_zero1: ∀I1,K1,L2,V1. K1.ⓑ{I1}V1 ⩬[0, 0] L2 →
                      ∃∃I2,K2,V2. K1 ⩬[0, 0] K2 & L2 = K2.ⓑ{I2}V2.
/2 width=9 by lreq_inv_zero1_aux/ qed-.

fact lreq_inv_pair1_aux: ∀L1,L2,l,m. L1 ⩬[l, m] L2 →
                         ∀J,K1,W. L1 = K1.ⓑ{J}W → l = 0 → 0 < m →
                         ∃∃K2. K1 ⩬[0, ⫰m] K2 & L2 = K2.ⓑ{J}W.
#L1 #L2 #l #m * -L1 -L2 -l -m
[ #l #m #J #K1 #W #H destruct
| #I1 #I2 #L1 #L2 #V1 #V2 #_ #J #K1 #W #_ #_ #H
  elim (ylt_yle_false … H) //
| #I #L1 #L2 #V #m #HL12 #J #K1 #W #H #_ #_ destruct
  /2 width=3 by ex2_intro/
| #I1 #I2 #L1 #L2 #V1 #V2 #l #m #_ #J #K1 #W #_ #H
  elim (ysucc_inv_O_dx … H)
]
qed-.

lemma lreq_inv_pair1: ∀I,K1,L2,V,m. K1.ⓑ{I}V ⩬[0, m] L2 → 0 < m →
                      ∃∃K2. K1 ⩬[0, ⫰m] K2 & L2 = K2.ⓑ{I}V.
/2 width=6 by lreq_inv_pair1_aux/ qed-.

lemma lreq_inv_pair: ∀I1,I2,L1,L2,V1,V2,m. L1.ⓑ{I1}V1 ⩬[0, m] L2.ⓑ{I2}V2 → 0 < m →
                    ∧∧ L1 ⩬[0, ⫰m] L2 & I1 = I2 & V1 = V2.
#I1 #I2 #L1 #L2 #V1 #V2 #m #H #Hm elim (lreq_inv_pair1 … H) -H //
#Y #HL12 #H destruct /2 width=1 by and3_intro/
qed-.

fact lreq_inv_succ1_aux: ∀L1,L2,l,m. L1 ⩬[l, m] L2 →
                         ∀J1,K1,W1. L1 = K1.ⓑ{J1}W1 → 0 < l →
                         ∃∃J2,K2,W2. K1 ⩬[⫰l, m] K2 & L2 = K2.ⓑ{J2}W2.
#L1 #L2 #l #m * -L1 -L2 -l -m
[ #l #m #J1 #K1 #W1 #H destruct
| #I1 #I2 #L1 #L2 #V1 #V2 #_ #J1 #K1 #W1 #_ #H
  elim (ylt_yle_false … H) //
| #I #L1 #L2 #V #m #_ #J1 #K1 #W1 #_ #H
  elim (ylt_yle_false … H) //
| #I1 #I2 #L1 #L2 #V1 #V2 #l #m #HL12 #J1 #K1 #W1 #H #_ destruct
  /2 width=5 by ex2_3_intro/
]
qed-.

lemma lreq_inv_succ1: ∀I1,K1,L2,V1,l,m. K1.ⓑ{I1}V1 ⩬[l, m] L2 → 0 < l →
                      ∃∃I2,K2,V2. K1 ⩬[⫰l, m] K2 & L2 = K2.ⓑ{I2}V2.
/2 width=5 by lreq_inv_succ1_aux/ qed-.

lemma lreq_inv_atom2: ∀L1,l,m. L1 ⩬[l, m] ⋆ → L1 = ⋆.
/3 width=3 by lreq_inv_atom1, lreq_sym/
qed-.

lemma lreq_inv_succ: ∀I1,I2,L1,L2,V1,V2,l,m. L1.ⓑ{I1}V1 ⩬[l, m] L2.ⓑ{I2}V2 → 0 < l →
                     L1 ⩬[⫰l, m] L2.
#I1 #I2 #L1 #L2 #V1 #V2 #l #m #H #Hl elim (lreq_inv_succ1 … H) -H //
#Z #Y #X #HL12 #H destruct //
qed-.

lemma lreq_inv_zero2: ∀I2,K2,L1,V2. L1 ⩬[0, 0] K2.ⓑ{I2}V2 →
                      ∃∃I1,K1,V1. K1 ⩬[0, 0] K2 & L1 = K1.ⓑ{I1}V1.
#I2 #K2 #L1 #V2 #H elim (lreq_inv_zero1 … (lreq_sym … H)) -H 
/3 width=5 by lreq_sym, ex2_3_intro/
qed-.

lemma lreq_inv_pair2: ∀I,K2,L1,V,m. L1 ⩬[0, m] K2.ⓑ{I}V → 0 < m →
                      ∃∃K1. K1 ⩬[0, ⫰m] K2 & L1 = K1.ⓑ{I}V.
#I #K2 #L1 #V #m #H #Hm elim (lreq_inv_pair1 … (lreq_sym … H)) -H
/3 width=3 by lreq_sym, ex2_intro/
qed-.

lemma lreq_inv_succ2: ∀I2,K2,L1,V2,l,m. L1 ⩬[l, m] K2.ⓑ{I2}V2 → 0 < l →
                      ∃∃I1,K1,V1. K1 ⩬[⫰l, m] K2 & L1 = K1.ⓑ{I1}V1.
#I2 #K2 #L1 #V2 #l #m #H #Hl elim (lreq_inv_succ1 … (lreq_sym … H)) -H 
/3 width=5 by lreq_sym, ex2_3_intro/
qed-.

(* Basic forward lemmas *****************************************************)

lemma lreq_fwd_length: ∀L1,L2,l,m. L1 ⩬[l, m] L2 → |L1| = |L2|.
#L1 #L2 #l #m #H elim H -L1 -L2 -l -m normalize //
qed-.

(* Advanced inversion lemmas ************************************************)

fact lreq_inv_O_Y_aux: ∀L1,L2,l,m. L1 ⩬[l, m] L2 → l = 0 → m = ∞ → L1 = L2.
#L1 #L2 #l #m #H elim H -L1 -L2 -l -m //
[ #I1 #I2 #L1 #L2 #V1 #V2 #_ #_ #_ #H destruct
| /4 width=1 by eq_f3, ysucc_inv_Y_dx/
| #I1 #I2 #L1 #L2 #V1 #V2 #l #m #_ #_ #H elim (ysucc_inv_O_dx … H)
]
qed-.

lemma lreq_inv_O_Y: ∀L1,L2. L1 ⩬[0, ∞] L2 → L1 = L2.
/2 width=5 by lreq_inv_O_Y_aux/ qed-.
