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

include "ground/xoa/ex_1_2.ma".
include "ground/lib/list_append.ma".
include "ground/lib/subset.ma".
include "ground/notation/functions/circled_collection_f_1.ma".

(* SUBSET WITH LISTED ELEMENTS **********************************************)

definition subset_listed (A) (l): 𝒫❨A❩ ≝
           {a | ∃∃l1,l2. l1 ⨁ a ⨮ l2 = l}.

interpretation
  "listed (subset)"
  'SubsetX A l = (subset_listed A l).
