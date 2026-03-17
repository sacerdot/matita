(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2.
*)

include "convergence/classes/cls_s.ma".
include "convergence/notation/functions/function_i_s_1.ma".
include "convergence/notation/functions/function_i_s_2.ma".

(* IDENTITY ABSTRACT FUNCTION ***********************************************)

definition fun_id_s (X:ℂ𝟬𝗌): X → X ≝
           λx. x.

interpretation
  "structure (identity function)"
  'FunctionI_s X = (fun_id_s X).

interpretation
  "structure (applied identity function)"
  'FunctionI_s X x = (fun_id_s X x).

(* Corollaries **************************************************************)

lemma fun_id_s_appl (X:ℂ𝟬𝗌) (x:X):
      x = 𝗜𝗌 x.
//
qed.
