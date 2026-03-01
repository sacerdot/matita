(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2.
*)

include "convergence/directions/direction.ma".
include "convergence/directions/direction_struct_overlap.ma".

(* OVERLAP FOR DIRECTION ****************************************************)

(* Advanced properties ******************************************************)

lemma dir_ol_refl (X) (D:𝔻 X):
      D ≬ D.
/3 width=4 by dir_a_le_dx, dir_a_le_sx, dir_P, dir_d, subset_sigma_P, subset_ol_i/
qed.
