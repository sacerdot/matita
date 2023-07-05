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

include "ground/relocation/fu/fur_uni_eq.ma".
include "ground/relocation/fu/fur_nexts_dapp.ma".

(* UNIFORM ELEMENTS FOR FINITE RELOCATION MAPS FOR UNWIND *******************)

(* Constructions with fur_nexts *********************************************)

lemma tr_nexts_uni (m) (n):
      (𝐮❨n+m❩) ≐ ↑*[m]𝐮❨n❩.
#m #n #a
<fur_dapp_uni <fur_dapp_nexts //
qed.
