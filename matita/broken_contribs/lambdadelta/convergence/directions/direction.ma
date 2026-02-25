(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2.
*)

include "convergence/directions/direction_posts.ma".
include "convergence/notation/functions/category_d_1.ma".

(* DIRECTION ****************************************************************)

(* Object *******************************************************************)

record direction (S:𝔻𝟬): Type[1] ≝
{ dir_S: 𝔻𝗌❨S❩
; dir_P: 𝔻𝗽❨dir_S❩
}.

interpretation
  "direction (category)"
  'CategoryD S = (direction S).

coercion dir_S.

coercion dir_P.
