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

include "delayed_updating/syntax/path_structure.ma".
include "delayed_updating/syntax/path_balanced.ma".
include "delayed_updating/syntax/path_closed.ma".
include "delayed_updating/syntax/path_beta.ma".
include "delayed_updating/notation/functions/subset_r_4.ma".

(* EXPLICIT β-REDEX POINTER *************************************************)

(* Note: β-redex pointers (active paths) are paths to reducible variables *)
definition pxr (p) (b) (q) (n): 𝒫❨ℙ❩ ≝
           {r | ∧∧ 𝐫❨p,b,q,⁤↑n❩ = r & ⊗b ϵ 𝐁 & q ϵ 𝐂❨n❩}
.

interpretation
  "explicit β-redex pointer (subset of paths)"
  'SubsetR p b q n = (pxr p b q n).

(* Basic constructions ******************************************************)

lemma pxr_mk (p) (b) (q) (n):
      ⊗b ϵ 𝐁 → q ϵ 𝐂❨n❩ →
      (𝐫❨p,b,q,⁤↑n❩) ϵ 𝐑❨p,b,q,n❩.
/2 width=1 by and3_intro/
qed.

(* Basic destructions *******************************************************)

lemma pxr_des_eq (r) (p) (b) (q) (n):
      r ϵ 𝐑❨p,b,q,n❩ → 𝐫❨p,b,q,⁤↑n❩ = r.
#r #p #b #q #n * #H0 #_ #_ //
qed-.

lemma pxr_des_b (r) (p) (b) (q) (n):
      r ϵ 𝐑❨p,b,q,n❩ → ⊗b ϵ 𝐁.
#r #p #b #q #n * #_ #H0 #_ //
qed-.

lemma pxr_des_q (r) (p) (b) (q) (n):
      r ϵ 𝐑❨p,b,q,n❩ → q ϵ 𝐂❨n❩.
#r #p #b #q #n * #_ #_ #H0 //
qed-.

(* Advanced destructions ****************************************************)

lemma path_rcons_in_pxr_des_eq (x) (p) (b) (q) (l) (n):
      x◖l ϵ 𝐑❨p,b,q,n❩ →
      ∧∧ 𝐫❨p,b,q❩ = x & 𝗱(⁤↑n) = l.
#x #p #b #q #l #n #H0
lapply (pxr_des_eq … H0) -H0
>path_p3beta_rcons_d #H0 destruct
/2 width=1 by conj/
qed-.
