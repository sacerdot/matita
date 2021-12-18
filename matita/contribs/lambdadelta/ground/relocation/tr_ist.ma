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

include "ground/relocation/pr_ist.ma".
include "ground/relocation/tr_pap_pat.ma".

(* TOTAL RELOCATION MAPS ****************************************************)

(* Constructions with pr_ist ************************************************)

(*** at_istot *)
lemma tr_ist (f): 𝐓❨𝐭❨f❩❩.
/2 width=2 by ex_intro/ qed.
