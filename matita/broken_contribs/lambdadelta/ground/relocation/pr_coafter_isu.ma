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

include "ground/relocation/pr_isi_pushs.ma".
include "ground/relocation/pr_isu_uni.ma".
include "ground/relocation/pr_coafter_uni_pushs.ma".

(* RELATIONAL CO-COMPOSITION FOR PARTIAL RELOCATION MAPS ********************)

(* Constructions with pr_isu and pr_isi *************************************)

(*** coafter_isuni_isid *)
lemma pr_coafter_isu_isi:
      ∀f2. 𝐈❨f2❩ → ∀f1. 𝐔❨f1❩ → f1 ~⊚ f2 ≘ f2.
#f #Hf #g #H
elim (pr_isu_inv_uni … H) -H #n #H
/5 width=4 by pr_isi_pushs, pr_isi_inv_eq_repl, pr_coafter_eq_repl_back, pr_coafter_eq_repl_back_sn/
qed.
