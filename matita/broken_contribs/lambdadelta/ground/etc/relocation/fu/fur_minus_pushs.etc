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

include "ground/relocation/fu/fur_minus.ma".
include "ground/relocation/fu/fur_pushs.ma".

(* RIGHT SUBTRACTION FOR FINITE RELOCATION MAPS FOR UNWIND ******************)

(* Constructions with fur_pushs *********************************************)

lemma fur_minus_pushs_sn (r) (k) (f) :
      (⫯*[k](f-r)) = (⫯*[k]f)-r.
#r #k @(nat_ind_succ … k) -k //
#k #IH #f <fur_pushs_swap <fur_pushs_swap //
qed.
