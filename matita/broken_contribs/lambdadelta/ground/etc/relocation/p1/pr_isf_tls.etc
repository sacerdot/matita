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

include "ground/relocation/p1/pr_tls.ma".
include "ground/relocation/p1/pr_isf_tl.ma".

(* FINITE COLENGTH CONDITION FOR PARTIAL RELOCATION MAPS ********************)

(* Constructions with pr_tls ************************************************)

lemma pr_isf_tls (n) (f): 𝐅❨f❩ → 𝐅❨⫰*[n]f❩.
#n @(nat_ind_succ … n) -n /3 width=1 by pr_isf_tl/
qed.

(* Inversions with pr_tls ***************************************************)

(*** isfin_inv_tls *)
lemma pr_isf_inv_tls (n) (g): 𝐅❨⫰*[n]g❩ → 𝐅❨g❩.
#n @(nat_ind_succ … n) -n /3 width=1 by pr_isf_inv_tl/
qed-.
