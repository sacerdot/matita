(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2.
*)

include "ground/subsets/subset.ma".
include "convergence/notation/functions/sigma_2.ma".

(* DISJOINT SUM FOR SUBSETS *************************************************)

record subset_sigma (X) (u:𝒫❨X❩): Type[0] ≝
{ subset_sigma_s: X
; subset_sigma_p: subset_sigma_s ϵ u
}.

interpretation
  "disjoint sum (subset)"
  'Sigma X u = (subset_sigma X u).
