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

include "ground/relocation/gr_nexts.ma".
include "ground/relocation/gr_isd.ma".

(* DIVERGENCE CONDITION FOR GENERIC RELOCATION MAPS ***********************************************************)

(* Properties with iterated next ********************************************)

(*** isdiv_nexts *)
lemma gr_isd_nexts (n) (f): 𝛀❪f❫ → 𝛀❪↑*[n]f❫.
#n @(nat_ind_succ … n) -n /3 width=3 by gr_isd_next/
qed.

(* Inversion lemmas with iterated next **************************************)

(*** isdiv_inv_nexts *)
lemma gr_isd_inv_nexts (n) (g): 𝛀❪↑*[n]g❫ → 𝛀❪g❫.
#n @(nat_ind_succ … n) -n /3 width=3 by gr_isd_inv_next/
qed-.
