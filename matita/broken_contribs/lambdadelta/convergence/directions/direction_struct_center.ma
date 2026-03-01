(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2.
*)

include "ground/subsets/subset_le.ma".
include "convergence/directions/direction_struct.ma".
include "convergence/notation/functions/set_ctr_2.ma".

(* CENTER FOR DIRECTION *****************************************************)

definition dir_ctr (X:ℂ𝟬𝗌) (D): 𝒫❨X❩ ≝
           {x | ∀i. x ϵ D＠❨i❩ }
.

interpretation
  "center (direction)"
  'SetCTR X D = (dir_ctr X D).

(* Corollaries **************************************************************)

lemma dir_ctr_in (X) (D:𝔻𝗌 X) (x):
      (∀i. x ϵ D＠❨i❩) → x ϵ 𝗖𝘁𝗿 D.
/2 width=1 by/
qed.

lemma dir_ctr_le (X) (D:𝔻𝗌 X) (i):
      (𝗖𝘁𝗿 D) ⊆ D＠❨i❩.
/2 width=1 by/
qed.

lemma dir_ctr_ge (X) (D:𝔻𝗌 X) (u):
      (∀i. u ⊆ D＠❨i❩) → u ⊆ 𝗖𝘁𝗿 D.
#X #D #u #H0 #x #Hx #i
@H0 // (**) (* full auto fails *)
qed.
