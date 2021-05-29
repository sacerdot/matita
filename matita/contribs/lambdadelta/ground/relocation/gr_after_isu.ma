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

include "ground/relocation/gr_isu_uni.ma".
include "ground/relocation/gr_after_uni.ma".

(* RELATIONAL COMPOSITION FOR GENERIC RELOCATION MAPS ***********************)

(* Constructions with gr_isu ************************************************)

(*** after_isid_isuni *)
lemma gr_after_isu_isi_next:
      ∀f1,f2. 𝐈❪f2❫ → 𝐔❪f1❫ → f1 ⊚ ↑f2 ≘ ↑f1.
#f1 #f2 #Hf2 #H
elim (gr_isu_inv_uni … H) -H #h #H
/5 width=7 by gr_after_uni_isi_next, gr_after_eq_repl_back, gr_after_eq_repl_back_sn, gr_eq_next/
qed.

(*** after_uni_next2 *)
lemma gr_after_isu_next_sn:
      ∀f2. 𝐔❪f2❫ → ∀f1,f. ↑f2 ⊚ f1 ≘ f → f2 ⊚ ↑f1 ≘ f.
#f2 #H #f1 #f #Hf
elim (gr_isu_inv_uni … H) -H #h #H
/5 width=7 by gr_after_uni_next_sn, gr_after_eq_repl_fwd_sn, gr_after_eq_repl_back_sn, gr_eq_next/
qed.
