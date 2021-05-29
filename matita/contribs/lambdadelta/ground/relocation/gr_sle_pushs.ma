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

include "ground/relocation/gr_pushs.ma".
include "ground/relocation/gr_sle.ma".

(* INCLUSION FOR GENERIC RELOCATION MAPS ************************************)

(* Constructions with gr_pushs **********************************************)

(*** sle_pushs *)
lemma gr_sle_pushs:
      ∀f1,f2. f1 ⊆ f2 → ∀n. ⫯*[n] f1 ⊆ ⫯*[n] f2.
#f1 #f2 #Hf12 #n @(nat_ind_succ … n) -n
/2 width=5 by gr_sle_push/
qed.
