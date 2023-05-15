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

include "delayed_updating/relocation/tr_minus.ma".
include "ground/relocation/tr_pn.ma".
include "ground/arith/nat_succ.ma".

(* RIGHT SUBTRACTION FOR TOTAL RELOCATION MAPS ******************************)

(* Constructions with tr_push ***********************************************)

lemma tr_minus_push_succ (f) (n:ℕ):
      (⫯(f-↑n)) = (⫯f)-↑n.
#f #n <tr_minus_cons_inj //
qed.

(* Constructions with tr_next ***********************************************)

lemma tr_minus_next_succ (n) (f:tr_map):
      f-n = (↑f)-↑n.
* [| #n ] * #p #f
<tr_minus_cons_inj
[ <tr_minus_zero_dx <pminus_unit_dx <ppred_succ
  >npsucc_succ >npsucc_inj <nminus_succ_bi
  >(nsucc_pnpred p) <nminus_succ_bi //
| <tr_minus_cons_inj //
]
qed.
