(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2.
*)

include "ground/xoa/ex_3_1.ma".
include "ground/subsets/subset_eq.ma".
include "ground/subsets/subset_and_le.ma".
include "ground/subsets/subsets_inhabited.ma".
include "convergence/directions/direction_struct.ma".
include "convergence/notation/functions/category_d_p_1.ma".

(* DIRECTION ****************************************************************)

(* Postulates ***************************************************************)

record direction_postulates (X) (D:𝔻𝗌 X): Prop ≝
{ dir_e_bw (u1) (u2):
  u1 ⇔ u2 → u2 ϵ D → u1 ϵ D
; dir_i:
  D ϵ ⊙
; dir_d (u):
  u ϵ D → u ϵ ⊙
; dir_a (u1) (u2):
  u1 ϵ D → u2 ϵ D → ∃∃u. u ϵ D & u ⊆ u1 ∩ u2
}.

interpretation
  "postulates (direction)"
  'CategoryD_p X = (direction_postulates X).

(* Corollaries **************************************************************)

lemma dir_e_fw (X) (D:𝔻𝗌 X):
      D ϵ 𝔻𝗉 →
      ∀u1,u2. u1 ⇔ u2 → u1 ϵ D → u2 ϵ D.
/3 width=3 by dir_e_bw, subset_eq_sym/
qed.

lemma dir_a_alt (X) (D:𝔻𝗌 X):
      D ϵ 𝔻𝗉 →
      ∀u1,u2. u1 ϵ D → u2 ϵ D → ∃∃u. u ϵ D & u ⊆ u1 & u ⊆ u2.
#X #D #HD #u1 #u2 #Hu1 #Hu2
elim (dir_a … HD … Hu1 Hu2) #u #Hu #H0
@(ex3_intro … u)
/2 width=4 by subset_le_and_inv_dx_sx, subset_le_and_inv_dx_dx/
qed-. 
