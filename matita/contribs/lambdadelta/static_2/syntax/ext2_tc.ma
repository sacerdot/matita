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

include "ground_2/lib/star.ma".
include "static_2/syntax/ext2.ma".

(* EXTENSION TO BINDERS OF A RELATION FOR TERMS *****************************)

(* Properties with transitive closure ***************************************)

lemma ext2_tc_pair: ∀R,I,V1,V2. TC … R V1 V2 →
                    TC … (ext2 R) (BPair I V1) (BPair I V2).
#R #I #V1 #V2 #H elim H -H -V2
/3 width=3 by ext2_pair, step, inj/
qed.

lemma ext2_tc_inj: ∀R,I1,I2. ext2 R I1 I2 → ext2 (TC … R) I1 I2.
#R #I1 #I2 * -I1 -I2
/3 width=1 by ext2_unit, ext2_pair, inj/
qed.

(* Main properties with transitive closure **********************************)

theorem ext2_tc_step: ∀R,I1,I. ext2 (TC … R) I1 I →
                      ∀I2. ext2 R I I2 → ext2 (TC … R) I1 I2.
#R #I1 #I * -I1 -I
[ #I #Z #H >(ext2_inv_unit_sn … H) -Z /2 width=1 by ext2_unit/
| #I #V1 #V #HV1 #Z #H
  elim (ext2_inv_pair_sn … H) -H #V2 #HV2 #H destruct
  /3 width=3 by ext2_pair, step/
]
qed-.

(* Advanced properties with transitive closure ******************************)

lemma ext2_tc: ∀R,I1,I2. TC … (ext2 R) I1 I2 → ext2 (TC … R) I1 I2.
#R #I1 #I2 #H elim H -I2
/2 width=3 by ext2_tc_step, ext2_tc_inj/
qed.

(* Advanced inversion lemmas with transitive closure ************************)

lemma ext2_inv_tc: ∀R,I1,I2. ext2 (TC … R) I1 I2 → TC … (ext2 R) I1 I2.
#R #I1 #I2 * -I1 -I2
/3 width=1 by ext2_tc_pair, ext2_unit, inj/
qed-.
