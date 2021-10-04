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

include "ground/relocation/pr_isi_pat.ma".
include "ground/relocation/pr_ist.ma".

(* TOTALITY CONDITION FOR PARTIAL RELOCATION MAPS ***************************)

(* Advanced constructions with pr_isi ***************************************)

(*** isid_at_total *)
lemma pr_isi_pat_total: ∀f. 𝐓❪f❫ → (∀i1,i2. @❪i1,f❫ ≘ i2 → i1 = i2) → 𝐈❪f❫.
#f #H1f #H2f @pr_isi_pat
#i lapply (H1f i) -H1f *
#j #Hf >(H2f … Hf) in ⊢ (???%); -H2f //
qed.
