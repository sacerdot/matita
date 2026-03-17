(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2.
*)

include "convergence/classes/cls_s.ma".
include "convergence/notation/functions/function_k_s_3.ma".
include "convergence/notation/functions/function_k_s_4.ma".

(* CONSTANT ABSTRACT FUNCTION ***********************************************)

definition fun_const_s (X:ℂ𝟬𝗌) (Y:ℂ𝟬𝗌) (y): X → Y ≝
           λ_. y.

interpretation
  "structure (constant function)"
  'FunctionK_s X Y y = (fun_const_s X Y y).

interpretation
  "structure (applied constant function)"
  'FunctionK_s X Y y x = (fun_const_s X Y y x).

(* Corollaries **************************************************************)

lemma fun_const_s_appl (X:ℂ𝟬𝗌) (Y:ℂ𝟬𝗌) (x:X) (y:Y):
      y = (𝗞𝗌 y) x.
//
qed.
