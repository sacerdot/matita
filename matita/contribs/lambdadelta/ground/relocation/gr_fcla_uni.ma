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

include "ground/relocation/gr_isi_uni.ma".
include "ground/relocation/gr_fcla.ma".

(* FINITE COLENGTH ASSIGNMENT FOR GENERIC RELOCATION MAPS *******************)

(* Constructions with gr_uni ************************************************)

(*** fcla_uni *)
lemma gr_fcla_uni (n): 𝐂❪𝐮❨n❩❫ ≘ n.
#n @(nat_ind_succ … n) -n
/2 width=1 by gr_fcla_isi, gr_fcla_next/
qed.
