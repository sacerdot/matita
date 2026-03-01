(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2.
*)

include "ground/subsets/subset_le.ma".
include "convergence/directions/direction_struct.ma".
include "convergence/notation/functions/set_ctr_2.ma".

(* DIRECTION ****************************************************************)

definition dir_ctr (X:ℂ𝟬𝗌) (D): 𝒫❨X❩ ≝
           {x | ∀i. x ϵ D＠❨i❩ }
.

interpretation
  "center (direction)"
  'SetCTR X D = (dir_ctr X D).

(* Corollaries **************************************************************)

lemma dir_ctr_in (X:ℂ𝟬𝗌) (D) (x):
      (∀i. x ϵ D＠❨i❩) → x ϵ 𝗖𝘁𝗿 D.
/2 width=2 by/
qed.

lemma dir_ctr_le (X:ℂ𝟬𝗌) (D) (i):
      (𝗖𝘁𝗿 D) ⊆ D＠❨i❩.
/2 width=2 by/
qed.

lemma dir_ctr_ge (X:ℂ𝟬𝗌) (D) (u):
      (∀i. u ⊆ D＠❨i❩) → u ⊆ 𝗖𝘁𝗿 D.
/2 width=2 by/
qed.
