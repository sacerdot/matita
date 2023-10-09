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
include "ground/relocation/p1/pr_uni.ma".
(* * it should not depend on pr_isi *)
include "ground/relocation/p1/pr_coafter_isi.ma".

(* RELATIONAL CO-COMPOSITION FOR PARTIAL RELOCATION MAPS ********************)

(* Constructions with pr_uni and pr_pushs ***********************************)

(*** coafter_uni_sn *)
lemma pr_coafter_uni_sn_pushs (n):
      ∀f. 𝐮❨n❩ ~⊚ f ≘ ⫯*[n] f.
#n @(nat_ind_succ … n) -n
/2 width=5 by pr_coafter_isi_sn, pr_coafter_next/
qed.
