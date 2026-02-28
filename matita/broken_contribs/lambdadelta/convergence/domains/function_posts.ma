(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2.
*)

include "convergence/domains/domain_eq.ma".
include "convergence/notation/functions/right_double_arrow_p_2.ma".

(* ABSTRACT FUNCTION ********************************************************)

(* Postulates ***************************************************************)

record function_postulates (D:𝔻𝟬) (C:𝔻𝟬) (f:D→C): Prop ≝
{ fun_in (d):
  d ∈ D → f d ∈ C
; fun_eq_f (d1) (d2):
  d1 ≍ d2 → f d1 ≍ f d1
}.

interpretation
  "postulates (function)"
  'RightDoubleArrow_p D C = (function_postulates D C).
