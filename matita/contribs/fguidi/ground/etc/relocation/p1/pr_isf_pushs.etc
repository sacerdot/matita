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

include "ground/relocation/p1/pr_pushs.ma".
include "ground/relocation/p1/pr_isf.ma".

(* FINITE COLENGTH CONDITION FOR PARTIAL RELOCATION MAPS ********************)

(* Constructions with pr_pushs **********************************************)

(*** isfin_pushs *)
lemma pr_isf_pushs (n) (f): 𝐅❨f❩ → 𝐅❨⫯*[n]f❩.
#n @(nat_ind_succ … n) -n /3 width=3 by pr_isf_push/
qed.

(* Inversions with pr_pushs *************************************************)

(*** isfin_inv_pushs *)
lemma pr_isf_inv_pushs (n) (g): 𝐅❨⫯*[n]g❩ → 𝐅❨g❩.
#n @(nat_ind_succ … n) -n /3 width=3 by pr_isf_inv_push/
qed-.
