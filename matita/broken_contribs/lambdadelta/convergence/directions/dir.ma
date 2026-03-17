(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2.
*)

include "convergence/subsets/subset_sigma.ma".
include "convergence/directions/dir_p.ma".
include "convergence/notation/functions/category_d_1.ma".

(* DIRECTION ****************************************************************)

(* Object *******************************************************************)

(* Note: a direction is a filter base *)
definition dir (X): Type[0] ≝ 𝝨(𝔻𝗌 X).𝔻𝗉.

interpretation
  "direction (category)"
  'CategoryD X = (dir X).

definition dir_s (X) (D: 𝔻 X): 𝔻𝗌 X ≝
           subset_sigma_s … D.

coercion dir_s.

definition dir_p (X) (D: 𝔻 X): 𝔻𝗉 … D ≝
           subset_sigma_p … D.

coercion dir_p.
