(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2.
*)

include "ground/subsets/subset_le.ma".
include "ground/subsets/subset_ext.ma".
include "convergence/directions/direction_struct.ma".
include "convergence/notation/functions/element_ext_3.ma".
include "convergence/notation/functions/element_ext_4.ma".
include "convergence/notation/relations/lim_5.ma".

(* LIMIT ********************************************************************)

interpretation
  "extended function of one argument (subset)"
  'ElementExt X Y f = (subset_ext_f1 X Y f).

interpretation
  "applied extended function of one argument (subset)"
  'ElementExt X Y f u = (subset_ext_f1 X Y f u).

definition limit (X:ℂ𝟬𝗌) (Y:ℂ𝟬𝗌) (f:X→Y) (D:𝔻𝗌 X) (C:𝔻𝗌 Y): Prop ≝
           ∀v. v ϵ C → ∃∃u. u ϵ D & (𝗲𝘅𝘁 f) u ⊆ v.

interpretation
  "limit (limit)"
  'Lim X Y f D C = (limit X Y f D C).

(* Corollarires *************************************************************)

lemma mk_limit_alt (X:ℂ𝟬𝗌) (Y:ℂ𝟬𝗌) (f:X→Y) (D:𝔻𝗌 X) (C:𝔻𝗌 Y):
      ( ∀v. v ϵ C → ∃∃u. u ϵ D & ∀x. x ϵ u → f x ϵ v
      ) → 𝗹𝗶𝗺[D]f ≘ C.
#X #Y #f #D #C #H0 #v #Hv
elim (H0 … Hv) -H0 #u #Hu #Hf
@(ex2_intro … Hu) #y * #x #Hx #H0 destruct
/2 width=1 by/
qed.

lemma limit_inv_alt (X:ℂ𝟬𝗌) (Y:ℂ𝟬𝗌) (f:X→Y) (D) (C):
      (𝗹𝗶𝗺[D]f ≘ C) →
      ∀v. v ϵ C → ∃∃u. u ϵ D & ∀x. x ϵ u → f x ϵ v.
#X #Y #f #D #C #H0 #v #Hv
elim (H0 … Hv) -H0 #u #Hu #Hf
/4 width=3 by subset_in_ext_f1_dx, ex2_intro/
qed-.
