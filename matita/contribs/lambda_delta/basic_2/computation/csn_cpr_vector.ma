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

include "basic_2/computation/csn_cpr.ma".
include "basic_2/computation/csn_vector.ma".

(* Advanced forward lemmas **************************************************)

lemma csn_fwd_applv: ∀L,T,Vs. L ⊢ ⬇* Ⓐ Vs. T → L ⊢ ⬇* Vs ∧ L ⊢ ⬇* T.
#L #T #Vs elim Vs -Vs /2 width=1/
#V #Vs #IHVs #HVs
lapply (csn_fwd_pair_sn … HVs) #HV
lapply (csn_fwd_flat_dx … HVs) -HVs #HVs
elim (IHVs HVs) -IHVs -HVs /3 width=1/
qed-.
