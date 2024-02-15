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

include "ground/xoa/ex_4_4.ma".
include "delayed_updating/notation/functions/subset_r_1.ma".
include "delayed_updating/syntax/path_structure.ma".
include "delayed_updating/syntax/path_clear.ma".
include "delayed_updating/syntax/path_balanced.ma".
include "delayed_updating/syntax/path_closed.ma".

(* SUBSET OF REDEX POINTERS *************************************************)

(* Note: redex pointers are cleared paths to reducible variables *)
(* Note: thus we can compare them in computation steps *)
definition prc (t): 𝒫❨ℙ❩ ≝
           {r | ∃∃p,b,q,n. ⓪(p●𝗔◗b●𝗟◗q) = r &
                           ⊗b ϵ 𝐁 & q ϵ 𝐂❨n❩ & (p●𝗔◗b●𝗟◗q)◖𝗱(⁤↑n) ϵ t
           }
.

interpretation
  "redex pointer (subset of paths)"
  'SubsetR t = (prc t).

(* Basic constructions ******************************************************)

lemma prc_mk (t) (p) (b) (q) (n):
      (p●𝗔◗b●𝗟◗q)◖𝗱(⁤↑n) ϵ t → ⊗b ϵ 𝐁 → q ϵ 𝐂❨n❩ →
      (⓪(p●𝗔◗b●𝗟◗q)) ϵ 𝐑❨t❩.
/2 width=8 by ex4_4_intro/
qed.

(* Basic destructions *******************************************************)

lemma prc_des_clear (t) (r):
      r ϵ 𝐑❨t❩ → ⓪r = r.
#t #r * #p #b #q #n #H0 #_ #_ #_ destruct //
qed-.
