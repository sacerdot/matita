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

include "ground/relocation/trz_tls.ma".
include "ground/relocation/trz_after.ma".

(* ITERATED TAIL FOR TOTAL RELOCATION MAPS WITH INTEGERS ********************)

(* Constructions with trz_after *********************************************)

theorem trz_tls_after_dapp (z) (f2) (f1):
        (⫰*[f1＠⧣❨z❩]f2)•(⫰*[z]f1) ≐ ⫰*[z](f2•f1).
#z #f2 #f1 #z0
<trz_after_dapp <trz_tls_dapp <trz_tls_dapp
<zminus_plus_simpl //
qed.
