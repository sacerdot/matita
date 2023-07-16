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

include "ground/relocation/fu/fur_height.ma".
include "ground/relocation/fu/fur_pushs.ma".

(* HEIGHT FOR FINITE RELOCATION MAPS FOR UNWIND *****************************)

(* Constructions with fur_pushs *********************************************)

lemma fur_height_pushs (n) (f):
      ♯f = ♯⫯*[n]f.
#n @(nat_ind_succ … n) -n //
qed.
