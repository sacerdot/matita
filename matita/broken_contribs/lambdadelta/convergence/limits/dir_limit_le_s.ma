(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2.
*)

include "convergence/directions/dir_le_s.ma".
include "convergence/limits/dir_limit_s.ma".

(* LIMIT FOR DIRECTION ******************************************************)

(* Properties with dir_le ***************************************************)

lemma dir_limit_le_bi (X:ℂ𝟬𝗌) (Y:ℂ𝟬𝗌) (f:X→Y) (D1) (D2) (C1) (C2):
      D1 ⊑ D2 → 𝗹𝗶𝗺[D1] f ≘ C1 → C2 ⊑ C1 → 𝗹𝗶𝗺[D2] f ≘ C2.
#X #Y #f #D1 #D2 #C1 #C2 #HD12 #HDC1 #HC21
@mk_dir_limit_alt #v2 #Hv2
elim (HC21 … Hv2) -HC21 #v1 #Hv1 #Hv12
elim (dir_limit_inv_alt … HDC1 … Hv1) -HDC1 #u1 #Hu1 #Huv1
elim (HD12 … Hu1) -HD12 #u2 #Hu2 #Hu21
/5 width=3 by ex2_intro/
qed-.
