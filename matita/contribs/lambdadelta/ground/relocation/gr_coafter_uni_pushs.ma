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
include "ground/relocation/gr_uni.ma".
(* * it should not depend on gr_isi *)
include "ground/relocation/gr_coafter_isi.ma".

(* RELATIONAL CO-COMPOSITION FOR GENERIC RELOCATION MAPS ********************)

(* Constructions with gr_uni and gr_pushs ***********************************)

(*** coafter_uni_sn *)
lemma gr_coafter_uni_sn_pushs (n):
      ∀f. 𝐮❨n❩ ~⊚ f ≘ ⫯*[n] f.
#n @(nat_ind_succ … n) -n
/2 width=5 by gr_coafter_isi_sn, gr_coafter_next/
qed.
