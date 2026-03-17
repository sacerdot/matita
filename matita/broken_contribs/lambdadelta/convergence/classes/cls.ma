(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2.
*)

include "convergence/classes/cls_p.ma".
include "convergence/notation/functions/category_c0_0.ma".

(* CLASS ********************************************************************)

(* Object *******************************************************************)

record cls: Type[1] ≝
{ cls_s:> ℂ𝟬𝗌
; cls_p:> cls_s ϵ¹ ℂ𝟬𝗉
}.

interpretation
  "class (category)"
  'CategoryC0 = (cls).
