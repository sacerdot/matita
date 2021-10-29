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

include "ground/relocation/pr_nexts_eq.ma".
include "ground/relocation/tr_nexts.ma".

(* TOTAL RELOCATION MAPS ****************************************************)

(* Constructions with pr_eq and stream_eq ***********************************)

corec lemma eq_tr_inj_bi (f1) (f2): f1 ≗ f2 → 𝐭❨f1❩ ≡ 𝐭❨f2❩.
* -f1 -f2 #p1 #p2 #f1 #f2 * -p2 #H
cases p1 -p1
[ @pr_eq_push /2 width=5 by/
| #p @pr_eq_next [3:|*: //]
  cases tr_inj_fold cases tr_inj_fold
  /3 width=5 by stream_eq_cons/
]
qed.

(* Inversions with pr_eq and stream_eq **************************************)

corec lemma eq_inv_tr_inj_bi (f1) (f2): 𝐭❨f1❩ ≡ 𝐭❨f2❩ → f1 ≗ f2.
cases f1 -f1 #p1 #f1 cases f2 -f2 #p2 #f2
cases tr_inj_unfold cases tr_inj_unfold #H
cases (pr_eq_inv_nexts_push_bi … H) -H #H1 #H2
@stream_eq_cons /2 width=1 by/
qed-.
