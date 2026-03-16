(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2.
*)

include "convergence/nhoods/nhoods_dir_struct.ma".
include "convergence/nhoods/nhoods_limit_struct.ma".
include "convergence/limits/limit_struct.ma".

(* LIMIT ********************************************************************)

(* Properties with nhoods ***************************************************)

(* Note: main result: our convergence includes the one of general topology *)
theorem limit_nhs (X:ℂ𝟬𝗌) (Y:ℂ𝟬𝗌) (f:X→Y) (F:𝔽𝗌 X) (G:𝔽𝗌 Y) (x0:X) (y0:Y):
        (𝗹𝗶𝗺[x0,F,G]f ≘ y0) → 𝗹𝗶𝗺[𝝙𝗌[F]❨x0❩]f ≘ 𝝙𝗌[G]❨y0❩.
/3 width=4 by mk_limit_alt, nhs_limit_inv_alt/
qed.
