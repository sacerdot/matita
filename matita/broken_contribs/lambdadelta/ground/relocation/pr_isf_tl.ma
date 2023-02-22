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

include "ground/relocation/pr_tl.ma".
include "ground/relocation/pr_isf.ma".

(* FINITE COLENGTH CONDITION FOR PARTIAL RELOCATION MAPS ********************)

(* Constructions with pr_tl *************************************************)

(*** isfin_tl *)
lemma pr_isf_tl (f): 𝐅❨f❩ → 𝐅❨⫰f❩.
#f elim (pr_map_split_tl f) * #Hf
/3 width=3 by pr_isf_inv_push, pr_isf_inv_next/
qed.

(* Inversions with pr_tl ****************************************************)

(*** isfin_inv_tl *)
lemma pr_isf_inv_tl (g): 𝐅❨⫰g❩ → 𝐅❨g❩.
#f elim (pr_map_split_tl f) * #Hf
/2 width=1 by pr_isf_next, pr_isf_push/
qed-.
