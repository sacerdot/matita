(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2.
*)

include "convergence/directions/direction.ma".
include "convergence/directions/direction_posts_image.ma".

(* IMAGE FOR DIRECTION ******************************************************)

(* Object *******************************************************************)

definition dir_img (X:ℂ𝟬𝗌) (Y:ℂ𝟬𝗌) (f:X→Y) (D:𝔻 X): 𝔻 Y ≝ ?.
@mk_subset_sigma
[ @(f＠𝗌❨D❩)
| /2 width=1 by subset_sigma_P, dir_img_p/
]
defined.

interpretation
  "object (direction image)"
  'At X Y f D = (dir_img X Y f D).
