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

include "ground_2/ynat/ynat_succ.ma".
include "basic_2/notation/relations/iso_4.ma".
include "basic_2/grammar/lenv_length.ma".

(* EQUIVALENCE FOR LOCAL ENVIRONMENTS ***************************************)

inductive leq: ynat → ynat → relation lenv ≝
| leq_atom: ∀d,e. leq d e (⋆) (⋆)
| leq_zero: ∀I,L1,L2,V. leq 0 0 L1 L2 → leq 0 0 (L1.ⓑ{I}V) (L2.ⓑ{I}V)
| leq_pair: ∀I1,I2,L1,L2,V1,V2,e.
            leq 0 e L1 L2 → leq 0 (⫯e) (L1.ⓑ{I1}V1) (L2.ⓑ{I2}V2)
| leq_succ: ∀I,L1,L2,V,d,e. leq d e L1 L2 → leq (⫯d) e (L1.ⓑ{I}V) (L2.ⓑ{I}V)
.

interpretation
   "equivalence (local environment)"
   'Iso d e L1 L2 = (leq d e L1 L2).

(* Basic properties *********************************************************)

lemma leq_refl: ∀L,d,e. L ≃[d, e] L.
#L elim L -L /2 width=1 by/
#L #I #V #IHL #d #e elim (ynat_cases … d) [ | * /2 width=1 by leq_succ/ ]
elim (ynat_cases … e) [ | * ]
/2 width=1 by leq_zero, leq_pair/
qed.

lemma leq_sym: ∀L1,L2,d,e. L1 ≃[d, e] L2 → L2 ≃[d, e] L1.
#L1 #L2 #d #e #H elim H -L1 -L2 -d -e
/2 width=1 by leq_atom, leq_zero, leq_pair, leq_succ/
qed-.

lemma leq_O_Y: ∀L1,L2. |L1| = |L2| → L1 ≃[0, ∞] L2.
#L1 elim L1 -L1
[ #X #H lapply (length_inv_zero_sn … H) -H //
| #L1 #I1 #V1 #IHL1 #X #H elim (length_inv_pos_sn … H) -H
  #L2 #I2 #V2 #HL12 #H destruct
  @(leq_pair … (∞)) /2 width=1 by/ (**) (* explicit constructor *)
]
qed.

(* Basic forward lemmas *****************************************************)

lemma leq_fwd_length: ∀L1,L2,d,e. L1 ≃[d, e] L2 → |L1| = |L2|.
#L1 #L2 #d #e #H elim H -L1 -L2 -d -e normalize //
qed-.

(* Basic inversion lemmas ***************************************************)

fact leq_inv_O2_aux: ∀L1,L2,d,e. L1 ≃[d, e] L2 → e = 0 → L1 = L2.
#L1 #L2 #d #e #H elim H -L1 -L2 -d -e /3 width=1 by eq_f3/
#I1 #I2 #L1 #L2 #V1 #V2 #e #_ #_ #H elim (ysucc_inv_O_dx … H)
qed-.

lemma leq_inv_O2: ∀L1,L2,d. L1 ≃[d, 0] L2 → L1 = L2.
/2 width=4 by leq_inv_O2_aux/ qed-.

fact leq_inv_Y1_aux: ∀L1,L2,d,e. L1 ≃[d, e] L2 → d = ∞ → L1 = L2.
#L1 #L2 #d #e #H elim H -L1 -L2 -d -e /3 width=1 by eq_f3/
[ #I1 #I2 #L1 #L2 #V1 #V2 #e #_ #_ #H destruct
| #I #L1 #L2 #V #d #e #_ #IHL12 #H lapply (ysucc_inv_Y_dx … H) -H
  /3 width=1 by eq_f3/
]
qed-.

lemma leq_inv_Y1: ∀L1,L2,e. L1 ≃[∞, e] L2 → L1 = L2.
/2 width=4 by leq_inv_Y1_aux/ qed-.
