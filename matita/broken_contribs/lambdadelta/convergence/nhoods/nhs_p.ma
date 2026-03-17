(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2.
*)

include "ground/subsets/subset_eq.ma".
include "ground/subsets/subset_and.ma".
include "ground/subsets/subsets_inhabited.ma".
include "convergence/nhoods/nhs_s.ma".
include "convergence/notation/functions/category_f_p_1.ma".

(* NHOODS *******************************************************************)

(* Postulates ***************************************************************)

record nhs_P (X) (F:𝔽𝗌 X): Prop ≝
{ nhs_pe_bw (x:X) (u1) (u2):
  u1 ⇔ u2 → u2 ϵ F＠𝗌❨x❩ → u1 ϵ F＠𝗌❨x❩
; nhs_pi (x:X):
  F＠𝗌❨x❩ ϵ ⊙
; nhs_pd (x:X) (u):
  u ϵ F＠𝗌❨x❩ → x ϵ u
; nhs_pa (x:X) (u1) (u2):
  u1 ϵ F＠𝗌❨x❩ → u2 ϵ F＠𝗌❨x❩ → u1 ∩ u2 ϵ F＠𝗌❨x❩
; nhs_po (x:X) (u):
  u ϵ F＠𝗌❨x❩ → ∃∃v. v ϵ F＠𝗌❨x❩ & u ϵ F＠𝗌❨v❩
; nhs_ps (x:X) (u1) (u2):
  u1 ⊆ u2 → u1 ϵ F＠𝗌❨x❩ → u2 ϵ F＠𝗌❨x❩
}.

interpretation
  "postulates (nhoods)"
  'CategoryF_p X = (nhs_P X).

(* Corollaries **************************************************************)

lemma nhs_pe_fw (X) (F:𝔽𝗌 X):
      F ϵ 𝔽𝗉 →
      ∀x:X. ∀u1,u2. u1 ⇔ u2 → u1 ϵ F＠𝗌❨x❩ → u2 ϵ F＠𝗌❨x❩.
/3 width=3 by nhs_pe_bw, subset_eq_sym/
qed.
