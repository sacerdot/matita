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

include "ground/relocation/gr_fcla_uni.ma".
include "ground/relocation/gr_isf.ma".

(* FINITE COLENGTH CONDITION FOR GENERIC RELOCATION MAPS *)

(* Properties with gr_uni ***************************)

(*** isfin_uni *)
lemma gr_isf_uni (n): 𝐅❪𝐮❨n❩❫.
/3 width=2 by ex_intro/ qed.
