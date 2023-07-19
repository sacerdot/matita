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

include "ground/relocation/fu/fur_dapp.ma".
include "ground/arith/pnat_lt_nrplus.ma".

(* DEPTH APPLICATION FOR FINITE RELOCATION MAPS FOR UNWIND ******************)

(* Constructions with plt ***************************************************)

lemma fur_dapp_increasing (f) (p1) (p2):
      p1 < p2 → f＠⧣❨p1❩ < f＠⧣❨p2❩.
#f elim f -f [| * [| #k ] #f #IH ] #p1 #p2 #Hp
[ //
| @(plt_ind_alt … Hp) -p1 -p2
  /3 width=1 by plt_succ_bi/
| /3 width=1 by plt_nrplus_bi_dx/
]
qed.

(* Constructions with ple ***************************************************)

lemma fur_dapp_le (f) (p):
      p ≤ f＠⧣❨p❩.
#f #p elim p -p
/4 width=3 by fur_dapp_increasing, ple_trans, ple_succ_bi/
qed.
