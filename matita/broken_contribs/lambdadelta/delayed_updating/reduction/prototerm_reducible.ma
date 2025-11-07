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

include "ground/xoa/and_4.ma".
include "delayed_updating/syntax/path_structure.ma".
include "delayed_updating/syntax/path_balanced.ma".
include "delayed_updating/syntax/path_closed.ma".
include "delayed_updating/syntax/path_beta_clear.ma".
include "delayed_updating/notation/functions/subset_r_5.ma".

(* EXPLICIT REDEX POINTER ***************************************************)

(* Note: redex pointers (active paths) are cleared paths to reducible variables *)
(* Note: thus we can compare them in computation steps *)
definition xprc (t) (p) (b) (q) (n): 𝒫❨ℙ❩ ≝
           {r | ∧∧ ⓪𝐫❨p,b,q,⁤↑n❩ = r & ⊗b ϵ 𝐁 & q ϵ 𝐂❨n❩ & 𝐫❨p,b,q,⁤↑n❩ ϵ t}
.

interpretation
  "explicit redex pointer (subset of paths)"
  'SubsetR t p b q n = (xprc t p b q n).

(* Basic constructions ******************************************************)

lemma xprc_mk (t) (p) (b) (q) (n):
      (𝐫❨p,b,q,⁤↑n❩) ϵ t → ⊗b ϵ 𝐁 → q ϵ 𝐂❨n❩ →
      (⓪𝐫❨p,b,q,⁤↑n❩) ϵ 𝐑❨t,p,b,q,n❩.
/2 width=1 by and4_intro/
qed.

(* Basic destructions *******************************************************)

lemma xprc_des_r (t) (r) (p) (b) (q) (n):
      r ϵ 𝐑❨t,p,b,q,n❩ → ⓪(𝐫❨p,b,q,⁤↑n❩) = r.
#t #r #p #b #q #n * #H0 #_ #_ #_ //
qed-.

lemma xprc_des_b (t) (r) (p) (b) (q) (n):
      r ϵ 𝐑❨t,p,b,q,n❩ → ⊗b ϵ 𝐁.
#t #r #p #b #q #n * #_ #H0 #_ #_ //
qed-.

lemma xprc_des_q (t) (r) (p) (b) (q) (n):
      r ϵ 𝐑❨t,p,b,q,n❩ → q ϵ 𝐂❨n❩.
#t #r #p #b #q #n * #_ #_ #H0 #_ //
qed-.

lemma xprc_des_n (t) (r) (p) (b) (q) (n):
      r ϵ 𝐑❨t,p,b,q,n❩ → 𝐫❨p,b,q,⁤↑n❩ ϵ t.
#t #r #p #b #q #n * #_ #_ #_ #H0 //
qed-.

lemma xprc_des_clear (t) (r) (p) (b) (q) (n):
      r ϵ 𝐑❨t,p,b,q,n❩ → ⓪r = r.
#t #r #p #b #q #n #Hr
lapply (xprc_des_r … Hr) -Hr #H0 destruct //
qed-.

lemma path_rcons_in_xprc_des_r (t) (x) (p) (b) (q) (l) (n):
      x◖l ϵ 𝐑❨t,p,b,q,n❩ →
      ∧∧ (⓪𝐫❨p,b,q❩) = x & 𝗱𝟎 = l.
#t #x #p #b #q #l #n #H0
lapply (xprc_des_r … H0) -H0
<path_clear_beta <path_clear_p3beta
>path_p3beta_rcons_d #H0 destruct
/2 width=1 by conj/
qed-.
