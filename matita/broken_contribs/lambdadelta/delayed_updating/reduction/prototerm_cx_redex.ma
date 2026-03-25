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

include "ground/subsets/subset_and.ma".
include "delayed_updating/reduction/prototerm_x_redex.ma".
include "delayed_updating/notation/functions/subset_r_5.ma".

(* COMPLETE EXPLICIT β-REDEX POINTER ****************************************)

definition pcxr (t) (p) (b) (q) (n): 𝒫❨ℙ❩ ≝
           t ∩ 𝐑❨p,b,q,n❩.

interpretation
  "complete explicit β-redex pointer (subset of paths)"
  'SubsetR t p b q n = (pcxr t p b q n).

(* Basic constructions ******************************************************)

lemma pcxr_mk (t) (p) (b) (q) (n):
      (𝐫❨p,b,q,⁤↑n❩) ϵ t → ⊗b ϵ 𝐁 → q ϵ 𝐂❨n❩ →
      (𝐫❨p,b,q,⁤↑n❩) ϵ 𝐑❨t,p,b,q,n❩.
/3 width=1 by subset_and_in, pxr_mk/
qed.

(* Basic destructions *******************************************************)

lemma pcxr_des_r (t) (r) (p) (b) (q) (n):
      r ϵ 𝐑❨t,p,b,q,n❩ → r ϵ t.
#t #r #p #b #q #n * #Hr #_ //
qed-.

lemma pcxr_des_x (t) (r) (p) (b) (q) (n):
      r ϵ 𝐑❨t,p,b,q,n❩ → r ϵ 𝐑❨p,b,q,n❩.
#t #r #p #b #q #n * #_ #H0 //
qed-.

lemma pcxr_des_eq (t) (r) (p) (b) (q) (n):
      r ϵ 𝐑❨t,p,b,q,n❩ → 𝐫❨p,b,q,⁤↑n❩ = r.
#t #r #p #b #q #n * #_
/2 width=1 by pxr_des_eq/
qed-.

lemma pcxr_des_b (t) (r) (p) (b) (q) (n):
      r ϵ 𝐑❨t,p,b,q,n❩ → ⊗b ϵ 𝐁.
#t #r #p #b #q #n * #_ #H0
/2 width=5 by pxr_des_b/
qed-.

lemma pcxr_des_q (t) (r) (p) (b) (q) (n):
      r ϵ 𝐑❨t,p,b,q,n❩ → q ϵ 𝐂❨n❩.
#t #r #p #b #q #n * #_
/2 width=4 by pxr_des_q/
qed-.

lemma pcxr_des_n (t) (r) (p) (b) (q) (n):
      r ϵ 𝐑❨t,p,b,q,n❩ → 𝐫❨p,b,q,⁤↑n❩ ϵ t.
#t #r #p #b #q #n * #Hr #H0
>(pxr_des_eq … H0) -p -b -q -n //
qed-.

(* Advanced destructions ****************************************************)

lemma path_rcons_in_pcxr_des_eq (t) (x) (p) (b) (q) (l) (n):
      x◖l ϵ 𝐑❨t,p,b,q,n❩ →
      ∧∧ 𝐫❨p,b,q❩ = x & 𝗱(⁤↑n) = l.
#t #x #p #b #q #l #n * #_ #H0
/2 width=1 by path_rcons_in_pxr_des_eq/
qed-.
