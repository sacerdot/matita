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

include "delayed_updating/syntax/path.ma".
include "delayed_updating/notation/functions/subset_f_0.ma".
include "ground/lib/subset.ma".

(* FREE CONDITION FOR PATH **************************************************)

definition pfc: 𝒫❨ℙ❩ ≝
           ❴r ❘ ∀p,q,n. r = p●𝗱n◗q → 𝐞 = q❵
.

interpretation
  "Nederpelt's Tfre (path)"
  'SubsetF = (pfc).

(* Basic constructions ******************************************************)

lemma pfc_empty:
      (𝐞) ϵ 𝐅.
#p #q #n #H0
elim (eq_inv_list_empty_append … H0) -H0 #H0 #_
elim (eq_inv_list_empty_append … H0) -H0 #_ #H0 destruct
qed.
