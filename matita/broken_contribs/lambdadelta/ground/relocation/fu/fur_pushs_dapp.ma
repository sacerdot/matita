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

include "ground/relocation/fu/fur_pushs.ma".
include "ground/relocation/fu/fur_dapp.ma".
include "ground/arith/nat_plus_rplus.ma".

(* ITERATED PUSH FOR FINITE RELOCATION MAPS FOR UNWIND **********************)

(* Inversions with fur_dapp *************************************************)

lemma fur_dapp_pushs (n) (f) (p):
      f＠⧣❨p❩+n = (⫯*[n]f)＠⧣❨p+n❩.
#n @(nat_ind_succ … n) -n //
qed.
