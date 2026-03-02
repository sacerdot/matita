(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2.
*)

include "convergence/directions/direction_struct_order.ma".
include "convergence/limits/limit_struct.ma".

(* LIMIT ********************************************************************)

(* Properties with order **************************************************)

lemma limit_le_bi (X:ℂ𝟬𝗌) (Y:ℂ𝟬𝗌) (f:X→Y) (D1) (D2) (C1) (C2):
      D1 ⊑ D2 → 𝗹𝗶𝗺[D1] f ≘ C1 → C2 ⊑ C1 → 𝗹𝗶𝗺[D2] f ≘ C2.
#X #Y #f #D1 #D2 #C1 #C2 #HD12 #HDC1 #HC21
@mk_limit_alt #j2
elim (HC21 j2) -HC21 #j1 #HC12
elim (limit_inv_alt … HDC1 j1) -HDC1 #i1 #HDC1
elim (HD12 i1) -HD12 #i2 #HD21
/7 width=3 by subset_sigma_P, mk_subset_sigma, ex_intro/
qed-.
