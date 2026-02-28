(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2.
*)

include "convergence/directions/direction.ma".
include "convergence/notation/functions/set_ctr_2.ma".

(* DIRECTION ****************************************************************)

definition dir_ctr (X) (D:𝔻 X): 𝒫❨X❩ ≝
           {x | ∀i. i ∈ 𝗜𝗱𝘅 D → x ϵ D＠❨i❩ }
.

interpretation
  "center (direction)"
  'SetCTR X D = (dir_ctr X D).

(* Corollaries **************************************************************)

lemma dir_ctr_in (X) (D:𝔻 X) (d):
      (∀i. i ∈ 𝗜𝗱𝘅 D → d ϵ D＠❨i❩) → d ϵ 𝗖𝘁𝗿 D.
/2 width=1 by/
qed.

lemma dir_ctr_le (X) (D:𝔻 X) (i):
      i ∈ 𝗜𝗱𝘅 D → 𝗖𝘁𝗿 D ⊆ D＠❨i❩.
/2 width=1 by/
qed.

lemma dir_ctr_ge (X) (D:𝔻 X) (u):
      (∀i. i ∈ 𝗜𝗱𝘅 D → u ⊆ D＠❨i❩) → u ⊆ 𝗖𝘁𝗿 D.
/2 width=1 by/
qed.
