(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2.
*)

include "convergence/directions/direction_posts.ma".
include "convergence/notation/functions/category_d_1.ma".

(* DIRECTION ****************************************************************)

(* Object *******************************************************************)

record direction (X): Type[1] ≝
{ dir_S:> 𝔻𝗌 X
; dir_P:> dir_S ϵ¹ 𝔻𝗽
}.

interpretation
  "direction (category)"
  'CategoryD X = (direction X).
