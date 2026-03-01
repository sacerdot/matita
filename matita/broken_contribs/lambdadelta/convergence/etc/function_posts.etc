(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2.
*)

include "convergence/domains/domain_eq.ma".
include "convergence/notation/functions/right_double_arrow_p_2.ma".

(* ABSTRACT FUNCTION ********************************************************)

(* Postulates ***************************************************************)

record function_postulates (X:𝔻𝟬) (Y:𝔻𝟬) (f:X→Y): Prop ≝
{ fun_in (x):
  x ϵ X → f x ϵ Y
; fun_eq_f (x1) (x2):
  x1 ≍ x2 → f x1 ≍ f x2
}.

interpretation
  "postulates (function)"
  'RightDoubleArrow_p X Y = (function_postulates X Y).
