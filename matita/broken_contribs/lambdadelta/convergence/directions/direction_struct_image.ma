(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2.
*)

include "ground/subsets/subset_eq.ma".
include "convergence/subsets/subset_ext.ma".
include "convergence/directions/direction_struct.ma".
include "convergence/notation/functions/at_s_4.ma".

(* IMAGE FOR DIRECTION ******************************************************)

(* Structure ****************************************************************)

definition dir_img_s (X:ℂ𝟬𝗌) (Y:ℂ𝟬𝗌) (f:X→Y) (D:𝔻𝗌 X): 𝔻𝗌 Y ≝ ?.
@mk_direction_structure
@({v | ∃∃u. u ϵ D & v ⇔ f＠❨u❩})
defined.

interpretation
  "structure (direction image)"
  'At_s X Y f D = (dir_img_s X Y f D).

(* Corollaries **************************************************************)

lemma dir_img_s_in (X:ℂ𝟬𝗌) (Y:ℂ𝟬𝗌) (f:X→Y) (D:𝔻𝗌 X) (u):
      u ϵ D → f＠❨u❩ ϵ f＠𝗌❨D❩.
/2 width=3 by ex2_intro/
qed.
