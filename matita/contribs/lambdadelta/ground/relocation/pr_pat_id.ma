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

include "ground/relocation/pr_id_eq.ma".
include "ground/relocation/pr_pat_eq.ma".

(* POSITIVE APPLICATION FOR PARTIAL RELOCATION MAPS *************************)

(* Constructions with pr_id *************************************************)

(*** id_at *)
lemma pr_pat_id (i): @❨i,𝐢❩ ≘ i.
/2 width=1 by pr_pat_eq, pr_eq_refl/ qed.

(* Inversions with pr_id ****************************************************)

(*** id_inv_at *)
lemma pr_pat_inv_id (f):
      (∀i. @❨i,f❩ ≘ i) → 𝐢 ≡ f.
/3 width=1 by pr_pat_inv_eq, pr_id_eq/
qed-.
