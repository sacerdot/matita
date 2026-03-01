(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2.
*)

include "ground/subsets/subset_and_le.ma".
include "convergence/domains/domain_eq.ma".
include "convergence/directions/direction_struct.ma".
include "convergence/notation/functions/at_3.ma".
include "convergence/notation/functions/category_d_p_1.ma".

(* DIRECTION ****************************************************************)

(* Postulates ***************************************************************)

definition dir_M (X) (D:𝔻𝗌 X) (i): 𝒫❨X❩ ≝
           (𝗗𝗼𝗺 X ∩ D＠𝘀❨i❩)
.

interpretation
  "member (direction structure)"
  'At X D i = (dir_M X D i).

record direction_postulates (X) (D:𝔻𝗌 X): Prop ≝
{ dir_D_le (i) (j):
  i ≍ j → D＠❨i❩ ⊆ D＠𝘀❨j❩

; dir_i_in:
  (𝗶) ϵ 𝗜𝗱𝘅 D

; dir_d_in_sx (i):
  i ϵ 𝗜𝗱𝘅 D → 𝗱＠❨i❩ ϵ X
; dir_d_in_dx (i):
  i ϵ 𝗜𝗱𝘅 D → 𝗱＠❨i❩ ϵ D＠𝘀❨i❩
; dir_d_eq (i) (j):
  i ≍❪𝗜𝗱𝘅 D❫ j → 𝗱＠❨i❩ ≍ 𝗱＠❨j❩

; dir_a_in (i1) (i2):
  i1 ϵ 𝗜𝗱𝘅 D → i2 ϵ 𝗜𝗱𝘅 D → i1*i2 ϵ 𝗜𝗱𝘅 D
; dir_s_sx (i1) (i2):
  i1 ϵ 𝗜𝗱𝘅 D → i2 ϵ 𝗜𝗱𝘅 D → D＠❨i1*i2❩ ⊆ D＠𝘀❨i1❩
; dir_s_dx (i1) (i2):
  i1 ϵ 𝗜𝗱𝘅 D → i2 ϵ 𝗜𝗱𝘅 D → D＠❨i1*i2❩ ⊆ D＠𝘀❨i2❩
; dir_a_eq_ff:
  ∀i1,j1. i1 ≍ j1 → ∀i2,j2. i2 ≍ j2 → i1*i2 ≍❪𝗜𝗱𝘅 D❫ j1*j2
}.

interpretation
  "postulates (direction)"
  'CategoryD_p X = (direction_postulates X).

(* Corollaries **************************************************************)

lemma dir_M_le (X) (D:𝔻𝗌 X):
      D 𝛆 𝔻𝗽 →
      ∀i1,i2. i1 ≍ i2 → D＠❨i1❩ ⊆ D＠❨i2❩.
/3 width=3 by subset_le_and_sx_refl_sx, subset_and_in, dir_D_le/
qed.

lemma dir_d_in (X) (D:𝔻𝗌 X):
      D 𝛆 𝔻𝗽 →
      ∀i. i ϵ 𝗜𝗱𝘅 D → 𝗱＠❨i❩ ϵ D＠❨i❩.
/3 width=1 by subset_and_in, dir_d_in_sx, dir_d_in_dx/
qed.

lemma dir_a_sx (X) (D:𝔻𝗌 X):
      D 𝛆 𝔻𝗽 →
      ∀i1,i2. i1 ϵ 𝗜𝗱𝘅 D → i2 ϵ 𝗜𝗱𝘅 D → D＠❨i1*i2❩ ⊆ D＠❨i1❩.
/3 width=3 by subset_le_and_sx_refl_sx, subset_and_in, dir_s_sx/
qed.

lemma dir_a_dx (X) (D:𝔻𝗌 X):
      D 𝛆 𝔻𝗽 →
      ∀i1,i2. i1 ϵ 𝗜𝗱𝘅 D → i2 ϵ 𝗜𝗱𝘅 D → D＠❨i1*i2❩ ⊆ D＠❨i2❩.
/3 width=3 by subset_le_and_sx_refl_sx, subset_and_in, dir_s_dx/
qed.
