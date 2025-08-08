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

include "ground/xoa/ex_1_4.ma".
include "delayed_updating/reduction/prototerm_reducible.ma".
include "delayed_updating/notation/functions/subset_r_1.ma".

(* SUBSET OF REDEX POINTERS *************************************************)

definition prc (t): 𝒫❨ℙ❩ ≝
           {r | ∃∃p,b,q,n. r ϵ 𝐑❨t,p,b,q,n❩}
.

interpretation
  "redex pointer (subset of paths)"
  'SubsetR t = (prc t).

(* Basic constructions ******************************************************)

lemma prc_mk (t) (r) (p) (b) (q) (n):
      r ϵ 𝐑❨t,p,b,q,n❩ → r ϵ 𝐑❨t❩.
/2 width=5 by ex1_4_intro/
qed.

lemma prc_mk_old (t) (p) (b) (q) (n):
      (𝐫❨p,b,q,⁤↑n❩) ϵ t → ⊗b ϵ 𝐁 → q ϵ 𝐂❨n❩ →
      (⓪𝐫❨p,b,q,⁤↑n❩) ϵ 𝐑❨t❩.
/3 width=5 by xprc_mk, prc_mk/
qed.

(* Basic destructions *******************************************************)

lemma prc_des_clear (t) (r):
      r ϵ 𝐑❨t❩ → ⓪r = r.
#t #r * #p #b #q #n
/2 width=6 by xprc_des_clear/
qed-.
