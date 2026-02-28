(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2.
*)

include "ground/subsets/subset_ext.ma".
include "convergence/domains/function.ma".
include "convergence/directions/direction.ma".
include "convergence/notation/functions/element_ext_3.ma".
include "convergence/notation/relations/lim_5.ma".

(* LIMIT ********************************************************************)

interpretation
  "extended function of one argument (subset)"
  'ElementExt X Y f = (subset_ext_f1 X Y f).

definition limit (X) (Y) (f:X⇒Y) (D:𝔻 …) (C:𝔻 …): Prop ≝
           ∀j. j ϵ 𝗜𝗱𝘅 C → ∃∃i. i ϵ 𝗜𝗱𝘅 D & (𝗲𝘅𝘁 f) (D＠❨i❩) ⊆ C＠❨j❩.

interpretation
  "limit (limit)"
  'Lim X Y f D C = (limit X Y f D C).

(* Corollarires *************************************************************)

lemma mk_limit_alt (X) (Y) (f:X⇒Y) (D:𝔻 …) (C:𝔻 …):
      ( ∀j. j ϵ 𝗜𝗱𝘅 C → ∃∃i. i ϵ 𝗜𝗱𝘅 D & ∀x. x ϵ D＠❨i❩ → f x ϵ C＠❨j❩
      ) → 𝗹𝗶𝗺[D]f ≘ C.
#X #Y #f #D #C #H0 #j #Hj
elim (H0 … Hj) -H0 -Hj #i #Hi #Hf
@(ex2_intro … Hi) -Hi #y * #x #Hx #H0 destruct
/2 width=1 by/
qed.

lemma limit_inv_alt (X) (Y) (f:X⇒Y) (D:𝔻 …) (C:𝔻 …):
      (𝗹𝗶𝗺[D]f ≘ C) →
      ∀j. j ϵ 𝗜𝗱𝘅 C → ∃∃i. i ϵ 𝗜𝗱𝘅 D & ∀x. x ϵ D＠❨i❩ → f x ϵ C＠❨j❩.
#X #Y #f #D #C #H0 #j #Hj
elim (H0 … Hj) -H0 -Hj #i #Hi #Hf
@(ex2_intro … Hi) -Hi #y #Hy
/3 width=1 by subset_in_ext_f1_dx/
qed-.
