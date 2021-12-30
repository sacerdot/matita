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

include "ground/relocation/pr_id.ma".
include "ground/relocation/pr_isi_eq.ma".

(* IDENTITY CONDITION FOR PARTIAL RELOCATION MAPS ***************************)

(* Constructions with pr_id *************************************************)

(*** id_isid *)
lemma pr_isi_id: 𝐈❨𝐢❩.
/2 width=1 by pr_eq_push_isi/ qed.

(* Alternative definition with pr_id and pr_eq ******************************)

(*** eq_id_isid *)
lemma pr_eq_id_isi (f): 𝐢 ≐ f → 𝐈❨f❩.
/2 width=3 by pr_isi_eq_repl_back/ qed.

(*** eq_id_inv_isid *)
lemma pr_isi_inv_eq_id (f): 𝐈❨f❩ → 𝐢 ≐ f.
/2 width=1 by pr_isi_inv_eq_repl/ qed-.
