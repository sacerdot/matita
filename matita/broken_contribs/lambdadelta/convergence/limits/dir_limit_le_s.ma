(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2.
*)

include "convergence/directions/dir_img_le_s.ma".
include "convergence/limits/dir_limit_s.ma".

(* LIMIT FOR DIRECTION ******************************************************)

(* Properties with dir_le ***************************************************)

lemma dir_limit_le_bi (X:ℂ𝟬𝗌) (Y:ℂ𝟬𝗌) (f:X→Y) (D1) (D2) (C1) (C2):
      D1 ⊑ D2 → 𝗹𝗶𝗺[D1] f ≘ C1 → C2 ⊑ C1 → 𝗹𝗶𝗺[D2] f ≘ C2.
/4 width=5 by dir_le_img_bi, dir_le_trans/
qed-.
