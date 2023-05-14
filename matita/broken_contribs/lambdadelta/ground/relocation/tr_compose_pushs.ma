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

include "ground/relocation/tr_pushs.ma".
include "ground/relocation/tr_compose_pn.ma".

(* COMPOSITION FOR TOTAL RELOCATION MAPS ************************************)

(* Constructions with tr_pushs **********************************************)

lemma tr_compose_pushs_bi (n) (f2) (f1):
      (⫯*[n](f2∘f1)) = (⫯*[n]f2)∘(⫯*[n]f1).
#n @(nat_ind_succ … n) -n //
qed.
