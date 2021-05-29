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

include "ground/relocation/gr_tls.ma".
include "ground/relocation/gr_isd_tl.ma".

(* DIVERGENCE CONDITION FOR GENERIC RELOCATION MAPS *************************)

(* Constructions with gr_tls ************************************************)

(*** isdiv_tls *)
lemma gr_isd_tls (n) (g): 𝛀❪g❫ → 𝛀❪⫱*[n]g❫.
#n @(nat_ind_succ … n) -n /3 width=1 by gr_isd_tl/
qed.
