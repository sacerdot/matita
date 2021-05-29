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

include "ground/relocation/gr_isi_pushs.ma".
include "ground/relocation/gr_isu_uni.ma".
include "ground/relocation/gr_coafter_uni_pushs.ma".

(* RELATIONAL CO-COMPOSITION FOR GENERIC RELOCATION MAPS ********************)

(* Constructions with gr_isu and gr_isi *************************************)

(*** coafter_isuni_isid *)
lemma gr_coafter_isu_isi:
      ∀f2. 𝐈❪f2❫ → ∀f1. 𝐔❪f1❫ → f1 ~⊚ f2 ≘ f2.
#f #Hf #g #H
elim (gr_isu_inv_uni … H) -H #n #H
/5 width=4 by gr_isi_pushs, gr_isi_inv_eq_repl, gr_coafter_eq_repl_back, gr_coafter_eq_repl_back_sn/
qed.
