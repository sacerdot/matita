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

include "ground/relocation/pr_isu.ma".
include "ground/relocation/pr_isf.ma".

(* FINITE COLENGTH CONDITION FOR PARTIAL RELOCATION MAPS ********************)

(* Constructions with pr_isu ************************************************)

(*** isuni_fwd_isfin *)
lemma pr_isf_isu (f): 𝐔❨f❩ → 𝐅❨f❩.
#f #H elim H -f
/3 width=1 by pr_isf_next, pr_isf_isi/
qed.
