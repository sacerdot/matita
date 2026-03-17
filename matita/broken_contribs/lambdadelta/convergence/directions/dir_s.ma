(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2.
*)

(* A THEORY OF CONVERGENCE
   Initial invocation: - Patience on me to gain peace and perfection! -
*)

include "convergence/classes/cls_s.ma".
include "convergence/notation/functions/category_d_s_1.ma".

(* DIRECTION ****************************************************************)

(* Structure ****************************************************************)

record dir_S (X:ℂ𝟬𝗌): Type[0] ≝
{ dir_sd:> 𝒫❨𝒫❨X❩❩
}.

interpretation
  "structure (direction)"
  'CategoryD_s X = (dir_S X).
