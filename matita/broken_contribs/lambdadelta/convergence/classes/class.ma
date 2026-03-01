(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2.
*)

include "convergence/classes/class_posts.ma".
include "convergence/notation/functions/category_c0_0.ma".

(* CLASS ********************************************************************)

(* Object *******************************************************************)

record class: Type[1] ≝
{ cls_S:> ℂ𝟬𝗌
; cls_P:> cls_S ϵ¹ ℂ𝟬𝗽
}.

interpretation
  "class (category)"
  'CategoryC0 = (class).
