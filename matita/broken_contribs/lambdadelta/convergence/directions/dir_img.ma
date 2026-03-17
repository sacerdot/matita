(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2.
*)

include "convergence/directions/dir.ma".
include "convergence/directions/dir_img_p.ma".

(* IMAGE FOR DIRECTION ******************************************************)

(* Object *******************************************************************)

definition dir_img (X:ℂ𝟬𝗌) (Y:ℂ𝟬𝗌) (f:X→Y) (D:𝔻 X): 𝔻 Y ≝ ?.
@mk_subset_sigma
[ @(f＠𝗌❨D❩)
| /2 width=1 by dir_img_p/
]
defined.

interpretation
  "image (direction)"
  'At X Y f D = (dir_img X Y f D).
