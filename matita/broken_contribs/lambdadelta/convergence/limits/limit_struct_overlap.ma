(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2.
*)

include "convergence/directions/direction_struct_overlap.ma".
include "convergence/limits/limit_struct.ma".

(* LIMIT ********************************************************************)

(* Properties with dir_ol ***************************************************)

theorem limit_des_ol (X:ℂ𝟬𝗌) (Y:ℂ𝟬𝗌) (f:X→Y) (D1) (D2) (C1) (C2):
        (𝗹𝗶𝗺[D1] f ≘ C1) → (𝗹𝗶𝗺[D2] f ≘ C2) →
        D1 ♡ D2 → C1 ♡ C2.
#X #Y #f #D1 #D2 #C1 #C2 #H1f #H2f #HD12 #v1 #v2 #Hv1 #Hv2
elim (limit_inv_alt … H1f … Hv1) -H1f #u1 #Hu1 #H1f
elim (limit_inv_alt … H2f … Hv2) -H2f #u2 #Hu2 #H2f
elim (HD12 … Hu1 Hu2) -HD12 #x #H1x #H2x
/3 width=3 by subset_ol_i/
qed-.
