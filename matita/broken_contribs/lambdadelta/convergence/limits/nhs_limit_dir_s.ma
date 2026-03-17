(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2.
*)

include "convergence/nhoods/nhs_dir_s.ma".
include "convergence/limits/dir_limit_s.ma".
include "convergence/limits/nhs_limit_s.ma".

(* LIMIT FOR NHOODS *********************************************************)

(* Properties with nhs_dir_s *************************************************)

theorem nhs_limit_dir_s (X:ℂ𝟬𝗌) (Y:ℂ𝟬𝗌) (f:X→Y) (F:𝔽𝗌 X) (G:𝔽𝗌 Y) (x0:X) (y0:Y):
        (𝗹𝗶𝗺[x0,F,G]f ≘ y0) → 𝗹𝗶𝗺[𝝙𝗌[F]❨x0❩]f ≘ 𝝙𝗌[G]❨y0❩.
/3 width=4 by mk_dir_limit_alt, nhs_limit_inv_alt/
qed.

theorem nhs_limit_inv_dir_s (X:ℂ𝟬𝗌) (Y:ℂ𝟬𝗌) (f:X→Y) (F:𝔽𝗌 X) (G:𝔽𝗌 Y) (x0:X) (y0:Y):
        (𝗹𝗶𝗺[𝝙𝗌[F]❨x0❩]f ≘ 𝝙𝗌[G]❨y0❩) → 𝗹𝗶𝗺[x0,F,G]f ≘ y0.
#X #Y #f #F #G #x0 #y0 #HFG
lapply (dir_limit_inv_alt … HFG) -HFG #HFG
/3 width=4 by mk_nhs_limit_alt/
qed-.
