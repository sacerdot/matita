(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2.
*)
include "convergence/subsets/subset_sigma.ma".
include "convergence/directions/direction_posts.ma".
include "convergence/notation/functions/category_d_1.ma".

(* DIRECTION ****************************************************************)

(* Object *******************************************************************)

(* Note: D is a direction iff D is a base for a filter  *)
(* Note: source: Tulio Valent handouts, proposition 1.1 *)
definition direction (X): Type[0] ≝ 𝝨(𝔻𝗌 X).𝔻𝗉.

interpretation
  "direction (category)"
  'CategoryD X = (direction X).

definition dir_S (X) (D: 𝔻 X): 𝔻𝗌 X ≝
           subset_sigma_S … D.

coercion dir_S.

definition dir_P (X) (D: 𝔻 X): 𝔻𝗉 … D ≝
           subset_sigma_P … D.

coercion dir_P.
