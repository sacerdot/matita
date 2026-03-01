(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2.
*)

include "convergence/directions/direction_struct_overlap.ma".
include "convergence/limits/limit_struct.ma".

(* LIMIT ********************************************************************)

(* Properties with overlap **************************************************)

lemma limit_des_ol (X:ℂ𝟬𝗌) (Y:ℂ𝟬𝗌) (f:X→Y) (D1) (D2) (C1) (C2):
      (𝗹𝗶𝗺[D1] f ≘ C1) → (𝗹𝗶𝗺[D2] f ≘ C2) →
      D1 ≬ D2 → C1 ≬ C2.
#X #Y #f #D1 #D2 #C1 #C2 #H1f #H2f #HD12 #j1 #j2
elim (limit_inv_alt … H1f j1) -H1f #i1 #H1f
elim (limit_inv_alt … H2f j2) -H2f #i2 #H2f
elim (HD12 i1 i2) -HD12 #x #H1x #H2x
/3 width=3 by subset_ol_i/
qed-.
