(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2.
*)

include "convergence/domains/element.ma".
include "convergence/domains/function_posts.ma".
include "convergence/notation/functions/function_k_s_3.ma".

(* CONSTANT ABSTRACT FUNCTION ***********************************************)

definition fun_const_s (X:𝔻𝟬) (Y) (y:𝗘𝘅𝘁 Y): X → Y ≝
           λ_. y.

interpretation
  "structure (constant function)"
  'FunctionK_s X Y y = (fun_const_s X Y y).

(* Corollaries **************************************************************)

lemma fun_const_s_in_p (X) (Y) (y):
      (𝗞𝗌 y) ϵ X ⇒𝗽 Y.
/3 width=1 by elt_P, mk_function_postulates, dom_eq_refl/
qed.
