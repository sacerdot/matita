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

include "ground/xoa/ex_3_3.ma".
include "delayed_updating/syntax/path_clear.ma".
include "delayed_updating/syntax/path_proper.ma".
include "delayed_updating/notation/functions/subset_f_1.ma".

(* SUBSET OF FIRED PATHS ****************************************************)

(* Note: fired paths are cleared paths not containing outer references *)
(* Note: thus we can compare them in computation steps *)
definition pfc (t): 𝒫❨ℙ❩ ≝
           {r | ∃∃p,q,n. ⓪(p●𝗱n◗q) = r & q ϵ 𝐏 & p●𝗱n◗q ϵ t}
.

interpretation
  "fired (path subset)"
  'SubsetF t = (pfc t).

(* Basic constructions ******************************************************)

lemma pfc_mk (t) (p) (q) (n):
      q ϵ 𝐏 → p●𝗱n◗q ϵ t → ⓪(p●𝗱n◗q) ϵ 𝐅❨t❩.
/2 width=6 by ex3_3_intro/
qed.
