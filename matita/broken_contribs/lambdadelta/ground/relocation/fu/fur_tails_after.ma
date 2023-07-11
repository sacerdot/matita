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

include "ground/relocation/fu/fur_tails_xapp.ma".
include "ground/relocation/fu/fur_after_xapp.ma".
include "ground/relocation/fu/fur_xapp_eq.ma".
include "ground/arith/nat_le_minus_plus.ma".

(* ITERATED TAIL FOR FINITE RELOCATION MAPS FOR UNWIND **********************)

(* Advanced constructions with fur_after ************************************)

lemma fur_tails_after (n) (f2) (f1):
      (⫰*[f1＠❨n❩]f2)•(⫰*[n]f1) ≐ ⫰*[n](f2•f1).
#n #f2 #f1
@fur_eq_xapp #n
<fur_xapp_after <fur_xapp_tails <fur_xapp_tails
<fur_xapp_tails <fur_xapp_after <fur_xapp_after
<nplus_minus_sn_refl_sn //
qed.
