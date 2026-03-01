(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2.
*)

include "ground/subsets/subset_le.ma".
include "ground/subsets/subset_ext.ma".
include "convergence/directions/direction_struct.ma".
include "convergence/notation/functions/element_ext_3.ma".
include "convergence/notation/relations/lim_5.ma".

(* LIMIT ********************************************************************)

interpretation
  "extended function of one argument (subset)"
  'ElementExt X Y f = (subset_ext_f1 X Y f).

definition limit (X:ℂ𝟬𝗌) (Y:ℂ𝟬𝗌) (f:X→Y) (D) (C): Prop ≝
           ∀j. ∃i. (𝗲𝘅𝘁 f) (D＠❨i❩) ⊆ C＠❨j❩.

interpretation
  "limit (limit)"
  'Lim X Y f D C = (limit X Y f D C).

(* Corollarires *************************************************************)

lemma mk_limit_alt (X:ℂ𝟬𝗌) (Y:ℂ𝟬𝗌) (f:X→Y) (D) (C):
      ( ∀j. ∃i. ∀x. x ϵ D＠❨i❩ → f x ϵ C＠❨j❩
      ) → 𝗹𝗶𝗺[D]f ≘ C.
#X #Y #f #D #C #H0 #j
elim (H0 j) -H0 #i #Hf
@(ex_intro … i) #y * #x #Hx #H0 destruct
/2 width=1 by/
qed.

lemma limit_inv_alt (X:ℂ𝟬𝗌) (Y:ℂ𝟬𝗌) (f:X→Y) (D) (C):
      (𝗹𝗶𝗺[D]f ≘ C) →
      ∀j. ∃i. ∀x. x ϵ D＠❨i❩ → f x ϵ C＠❨j❩.
#X #Y #f #D #C #H0 #j
elim (H0 j) -H0 #i #Hf
@(ex_intro … i) #y #Hy
@Hf -Hf (**) (* full auto fails *)
/2 width=1 by subset_in_ext_f1_dx/
qed-.
