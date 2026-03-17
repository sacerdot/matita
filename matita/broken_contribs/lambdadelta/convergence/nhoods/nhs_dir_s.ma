(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2.
*)

include "convergence/directions/dir_s.ma".
include "convergence/nhoods/nhs_s.ma".
include "convergence/notation/functions/function_delta_s_3.ma".

(* DIRECTION FOR NHOODS *****************************************************)

(* Structure ****************************************************************)

definition nhs_dir_s (X) (F:𝔽𝗌 X) (x:X): 𝔻𝗌 X ≝ ?.
@mk_dir_S
@(F＠𝗌❨x❩)
defined.

interpretation
  "structure (direction for nhoods)"
  'FunctionDelta_s X F x = (nhs_dir_s X F x).

(* Corollaries **************************************************************)

lemma in_nhs_dir_s (X) (F:𝔽𝗌 X) (x:X) (u):
      u ϵ F＠𝗌❨x❩ → u ϵ 𝝙𝗌[F]❨x❩.
//
qed.

lemma in_nhs_dir_s_inv (X) (F:𝔽𝗌 X) (x:X) (u):
      u ϵ 𝝙𝗌[F]❨x❩ → u ϵ F＠𝗌❨x❩.
//
qed.
