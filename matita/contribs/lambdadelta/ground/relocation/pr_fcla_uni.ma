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

include "ground/relocation/pr_isi_uni.ma".
include "ground/relocation/pr_fcla.ma".

(* FINITE COLENGTH ASSIGNMENT FOR PARTIAL RELOCATION MAPS *******************)

(* Constructions with pr_uni ************************************************)

(*** fcla_uni *)
lemma pr_fcla_uni (n): šāØš®āØnā©ā© ā n.
#n @(nat_ind_succ ā¦ n) -n
/2 width=1 by pr_fcla_isi, pr_fcla_next/
qed.
