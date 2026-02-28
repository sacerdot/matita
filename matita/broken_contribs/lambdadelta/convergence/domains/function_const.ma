(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2.
*)

include "convergence/domains/function.ma".
include "convergence/domains/function_const_posts.ma".
include "convergence/notation/functions/function_k_3.ma".

(* CONSTANT ABSTRACT FUNCTION ***********************************************)

definition fun_const (X) (Y) (y:𝗘𝘅𝘁 Y): X ⇒ Y.
#X #Y #y
@mk_function
[ @(𝗞𝗌 y) | /2 width=1 by fun_const_s_in_p/ ]
defined.

interpretation
  "constant function (domain)"
  'FunctionK X Y y = (fun_const X Y y).

(* Corollaries **************************************************************)

(**) (* explicit coercion *) 
lemma fun_const_appl (X:𝔻𝟬) (Y) (x:X) (y:𝗘𝘅𝘁 Y):
      (elt_S ? y) = (𝗞 y) x.
//
qed.
