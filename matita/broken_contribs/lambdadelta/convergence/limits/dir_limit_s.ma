(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2.
*)

include "convergence/directions/dir_le_s.ma".
include "convergence/directions/dir_img_s.ma".
include "convergence/notation/relations/lim_5.ma".

(* LIMIT FOR DIRECTION ******************************************************)

(* Note: C is not finer than f＠𝗌❨D❩ *)
definition dir_limit (X:ℂ𝟬𝗌) (Y:ℂ𝟬𝗌) (f:X→Y) (D:𝔻𝗌 X) (C:𝔻𝗌 Y): Prop ≝
           C ⊑ f＠𝗌❨D❩.

interpretation
  "limit (direction)"
  'Lim X Y f D C = (dir_limit X Y f D C).

(* Corollarires *************************************************************)

lemma mk_dir_limit_alt (X:ℂ𝟬𝗌) (Y:ℂ𝟬𝗌) (f:X→Y) (D:𝔻𝗌 X) (C:𝔻𝗌 Y):
      ( ∀v. v ϵ C → ∃∃u. u ϵ D & ∀x. x ϵ u → f x ϵ v
      ) → 𝗹𝗶𝗺[D]f ≘ C.
#X #Y #f #D #C #H0 #v #Hv
elim (H0 … Hv) -H0 #u #Hu #Hf
@(ex2_intro … @ dir_img_s_in … f … Hu) #y * #x #Hx #H0 destruct
/2 width=1 by/
qed.

lemma dir_limit_inv_alt (X:ℂ𝟬𝗌) (Y:ℂ𝟬𝗌) (f:X→Y) (D) (C):
      (𝗹𝗶𝗺[D]f ≘ C) →
      ∀v. v ϵ C → ∃∃u. u ϵ D & ∀x. x ϵ u → f x ϵ v.
#X #Y #f #D #C #H0 #v1 #Hv1
elim (H0 … Hv1) -H0 #v2 * #u2 #Hu2 * #_ #Huv2 #Hv21
lapply (subset_le_trans … Huv2 … Hv21) -v2 #H0
/4 width=3 by subset_in_ext_f1_dx, ex2_intro/
qed-.
