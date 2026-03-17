(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2.
*)

include "convergence/classes/cls_s.ma".
include "convergence/notation/functions/category_f_s_1.ma".
include "convergence/notation/functions/at_s_3.ma".

(* NHOODS *******************************************************************)

(* Structure ****************************************************************)

record nhs_S (X:ℂ𝟬𝗌): Type[0] ≝
{ nhs_sp: X → 𝒫❨𝒫❨X❩❩
}.

(* The notation 𝔽 recalls that the nhoods of a point are a filter *)
interpretation
  "structure (nhoods)"
  'CategoryF_s X = (nhs_S X).

interpretation
  "of a point (nhoods)"
  'At_s X F x = (nhs_sp X F x).

definition nhs_ss (X) (F:𝔽𝗌 X) (v): 𝒫❨𝒫❨X❩❩ ≝
           { u | ∀x. x ϵ v → u ϵ F＠𝗌❨x❩ }
.

interpretation
  "of a subset (nhoodss)"
  'At_s X F v = (nhs_ss X F v).
