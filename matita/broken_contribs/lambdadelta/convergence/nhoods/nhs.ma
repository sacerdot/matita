(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2.
*)

include "convergence/subsets/subset_sigma.ma".
include "convergence/nhoods/nhs_p.ma".
include "convergence/notation/functions/category_f_1.ma".

(* NHOODS *******************************************************************)

(* Object *******************************************************************)

definition nhs (X): Type[0] ≝ 𝝨(𝔽𝗌 X).𝔽𝗉.

interpretation
  "nhoods (category)"
  'CategoryF X = (nhs X).

definition nhs_s (X) (F: 𝔽 X): 𝔽𝗌 X ≝
           subset_sigma_s … F.

coercion nhs_s.

definition nhs_p (X) (F: 𝔽 X): 𝔽𝗉 … F ≝
           subset_sigma_p … F.

coercion nhs_p.
