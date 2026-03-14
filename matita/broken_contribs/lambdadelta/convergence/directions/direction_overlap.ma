(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2.
*)

include "ground/subsets/subset_ol_le.ma". 
include "convergence/directions/direction.ma".
include "convergence/directions/direction_struct_overlap.ma".

(* OVERLAP FOR DIRECTION ****************************************************)

(* Advanced properties ******************************************************)

lemma dir_ol_refl (X) (D:𝔻 X):
      D ♡ D.
#X #D #u1 #u2 #Hu1 #Hu2
elim (dir_a_alt … Hu1 Hu2) // #u0 #Hu0 #Hu01 #Hu02
/3 width=5 by dir_d, subset_ol_le_repl/
qed.
