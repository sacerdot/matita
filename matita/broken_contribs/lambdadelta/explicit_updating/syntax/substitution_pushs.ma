(**************************************************************************)
(*       ___                                                              *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||         The HELM team.                                      *)
(*      ||A||         http://helm.cs.unibo.it                             *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU General Public License Version 2                  *)
(*                                                                        *)
(**************************************************************************)

include "explicit_updating/syntax/substitution_push.ma".

(* ITERATED PUSH FOR SUBSTITUTION *******************************************)

definition subst_pushs (n:ℕ): 𝕊 → 𝕊 ≝
           (λS.⫯S)^n.

interpretation
  "iterated push (substitution)"
  'UpSpoonStar n S = (subst_pushs n S).

(* Basic constructions ******************************************************)

lemma subst_pushs_zero (S):
      S = ⫯*[𝟎]S.
// qed.

lemma subst_pushs_unit (S):
      (⫯S) = ⫯*[⁤𝟏]S.
// qed-.

lemma subst_pushs_push (n) (S):
      (⫯⫯*[n]S) = ⫯*[n]⫯S.
#n #S @(niter_appl … (λS.⫯S))
qed.

lemma subst_pushs_pos (p) (S):
      (⫯⫯*[↓p]S) = ⫯*[⁤p]S.
#p #S @(niter_pos_ppred … (λS.⫯S))
qed.

lemma subst_pushs_succ (n) (S:𝕊):
      (⫯⫯*[n]S) = ⫯*[⁤↑n]S.
#n #S @(niter_succ … (λS.⫯S))
qed.

lemma subst_pushs_pos_swap (p) (S):
      (⫯*[↓p]⫯S) = ⫯*[⁤p]S.
// qed.

lemma subst_pushs_succ_swap (n) (S:𝕊):
      (⫯*[n]⫯S) = ⫯*[⁤↑n]S.
// qed.
