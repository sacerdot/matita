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

include "ground/relocation/pr_isu_uni.ma".
include "ground/relocation/pr_after_uni.ma".

(* RELATIONAL COMPOSITION FOR PARTIAL RELOCATION MAPS ***********************)

(* Constructions with pr_isu ************************************************)

(*** after_isid_isuni *)
lemma pr_after_isu_isi_next:
      ∀f1,f2. 𝐈❪f2❫ → 𝐔❪f1❫ → f1 ⊚ ↑f2 ≘ ↑f1.
#f1 #f2 #Hf2 #H
elim (pr_isu_inv_uni … H) -H #h #H
/5 width=7 by pr_after_uni_isi_next, pr_after_eq_repl_back, pr_after_eq_repl_back_sn, pr_eq_next/
qed.

(*** after_uni_next2 *)
lemma pr_after_isu_next_sn:
      ∀f2. 𝐔❪f2❫ → ∀f1,f. ↑f2 ⊚ f1 ≘ f → f2 ⊚ ↑f1 ≘ f.
#f2 #H #f1 #f #Hf
elim (pr_isu_inv_uni … H) -H #h #H
/5 width=7 by pr_after_uni_next_sn, pr_after_eq_repl_fwd_sn, pr_after_eq_repl_back_sn, pr_eq_next/
qed.
