(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2.
*)

include "ground/subsets/subset_and_le.ma".
include "convergence/directions/direction_struct.ma".
include "convergence/notation/functions/category_d_p_1.ma".

(* DIRECTION ****************************************************************)

(* Postulates ***************************************************************)

record direction_postulates (X) (D:𝔻𝗌 X): Prop ≝
{
(*
  dir_D_le (i) (j):
  i ≍ j → D＠❨i❩ ⊆ D＠𝘀❨j❩

; dir_d_eq (i) (j):
  i ≍❪𝗜𝗱𝘅 D❫ j → 𝗱＠❨i❩ ≍ 𝗱＠❨j❩
*)
  dir_a_le (i1) (i2):
  D＠❨i1*i2❩ ⊆ D＠❨i1❩ ∩ D＠❨i2❩
(*
; dir_a_eq_ff:
  ∀i1,j1. i1 ≍ j1 → ∀i2,j2. i2 ≍ j2 → i1*i2 ≍❪𝗜𝗱𝘅 D❫ j1*j2
*)
}.

interpretation
  "postulates (direction)"
  'CategoryD_p X = (direction_postulates X).

(* Corollaries **************************************************************)
(*
lemma dir_M_le (X) (D:𝔻𝗌 X):
      D 𝛆 𝔻𝗽 →
      ∀i1,i2. i1 ≍ i2 → D＠❨i1❩ ⊆ D＠❨i2❩.
/3 width=3 by subset_le_and_sx_refl_sx, subset_and_in, dir_D_le/
qed.
*)
lemma dir_a_le_sx (X) (D:𝔻𝗌 X):
      D ϵ¹ 𝔻𝗽 →
      ∀i1,i2. D＠❨i1*i2❩ ⊆ D＠❨i1❩.
/3 width=4 by dir_a_le, subset_le_and_inv_dx_sx/
qed.

lemma dir_a_le_dx (X) (D:𝔻𝗌 X):
      D ϵ¹ 𝔻𝗽 →
      ∀i1,i2. D＠❨i1*i2❩ ⊆ D＠❨i2❩.
/3 width=4 by dir_a_le, subset_le_and_inv_dx_dx/
qed.
