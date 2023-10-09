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

include "ground/relocation/tz/tzr_tls.ma".
include "ground/relocation/tz/tzr_after.ma".

(* ITERATED TAIL FOR TOTAL RELOCATION MAPS WITH INTEGERS ********************)

(* Constructions with tzr_after *********************************************)

theorem tzr_tls_after_dapp (z) (f2) (f1):
        (⫰*[f1＠⧣❨z❩]f2)•(⫰*[z]f1) ≐ ⫰*[z](f2•f1).
#z #f2 #f1 #z0
<tzr_after_dapp <tzr_tls_dapp <tzr_tls_dapp
<zminus_plus_simpl //
qed.
