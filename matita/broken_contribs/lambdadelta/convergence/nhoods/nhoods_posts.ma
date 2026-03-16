(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2.
*)

include "ground/subsets/subset_eq.ma".
include "ground/subsets/subset_and.ma".
include "ground/subsets/subsets_inhabited.ma".
include "convergence/nhoods/nhoods_struct.ma".
include "convergence/notation/functions/category_f_p_1.ma".

(* NHOODS *******************************************************************)

(* Postulates ***************************************************************)

record nhoods_postulates (X) (F:𝔽𝗌 X): Prop ≝
{ nhs_e_bw (x:X) (u1) (u2):
  u1 ⇔ u2 → u2 ϵ F＠𝗌❨x❩ → u1 ϵ F＠𝗌❨x❩
; nhs_i (x:X):
  F＠𝗌❨x❩ ϵ ⊙
; nhs_d (x:X) (u):
  u ϵ F＠𝗌❨x❩ → x ϵ u
; nhs_a (x:X) (u1) (u2):
  u1 ϵ F＠𝗌❨x❩ → u2 ϵ F＠𝗌❨x❩ → u1 ∩ u2 ϵ F＠𝗌❨x❩
; nhs_o (x:X) (u):
  ∃∃v. v ϵ F＠𝗌❨x❩ & u ϵ F＠𝗌❨v❩
; nhs_s (x:X) (u1) (u2):
  u1 ⊆ u2 → u1 ϵ F＠𝗌❨x❩ → u2 ϵ F＠𝗌❨x❩
}.

interpretation
  "postulates (nhoods)"
  'CategoryF_p X = (nhoods_postulates X).

(* Corollaries **************************************************************)

lemma nhs_e_fw (X) (F:𝔽𝗌 X):
      F ϵ 𝔽𝗉 →
      ∀x:X. ∀u1,u2. u1 ⇔ u2 → u1 ϵ F＠𝗌❨x❩ → u2 ϵ F＠𝗌❨x❩.
/3 width=3 by nhs_e_bw, subset_eq_sym/
qed.
