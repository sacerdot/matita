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
include "ground/relocation/gr_isf.ma".

(* FINITE COLENGTH CONDITION FOR GENERIC RELOCATION MAPS *)

(* Properties with iterated push ********************************************)

(*** isfin_pushs *)
lemma gr_isf_pushs (n) (f): 𝐅❪f❫ → 𝐅❪⫯*[n]f❫.
#n @(nat_ind_succ … n) -n /3 width=3 by gr_isf_push/
qed.

(* Inversion lemmas with iterated push **************************************)

(*** isfin_inv_pushs *)
lemma gr_isf_inv_pushs (n) (g): 𝐅❪⫯*[n]g❫ → 𝐅❪g❫.
#n @(nat_ind_succ … n) -n /3 width=3 by gr_isf_inv_push/
qed-.
