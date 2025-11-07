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

include "ground/arith/nat_lt_psucc_plt.ma".
include "ground/relocation/fb/fbr_lapp.ma".
include "ground/relocation/fb/fbr_dapp_lt.ma".

(* ** move to arith *)
lemma nle_pnpred_bi (p1) (p2):
      p1 ≤ p2 → ↓p1 ≤ ↓p2.
#p1 #p2 #H0 elim H0 -p2 //
#p2 #_ #IH >nsucc_pnpred_swap
/2 width=1 by nle_succ_dx/
qed.

(* ** move to arith *)
lemma nlt_pnpred_bi (p1) (p2):
      p1 < p2 → ↓p1 < ↓p2.
#p1 #p2 #H0
/2 width=1 by nle_pnpred_bi/
qed.

(* LEVEL APPLICATION FOR FINITE RELOCATION MAPS WITH BOOLEANS ***************)

(* Constructions with nlt ***************************************************)

lemma fbr_lapp_increasing (f) (n1) (n2):
      n1 < n2 → f＠§❨n1❩ < f＠§❨n2❩.
#f #n1 #n2 #Hn
/4 width=1 by fbr_dapp_increasing, nlt_pnpred_bi, plt_npsucc_bi/
qed.

(* Constructions with nle ***************************************************)

lemma fbr_lapp_le (f) (n):
      n ≤ f＠§❨n❩.
#f #n
>(pnpred_npsucc n) in ⊢ (?%?);
/2 width=1 by nle_pnpred_bi/
qed.

(* Advanced constructions ***************************************************)

lemma is_fbr_lapp_dec (f) (n2):
      Decidable (∃n1. n2 = f＠§❨n1❩).
#f #n2 elim (is_fbr_dapp_dec f (↑n2))
[ * /3 width=2 by ex_intro, or_introl/
| #H @or_intror * /3 width=2 by ex_intro/
]
qed-.

(* Advanced inversions ******************************************************)

lemma eq_inv_fbr_lapp_bi (f):
      injective_2_fwd … (eq …) (eq …) (λn.f＠§❨n❩).
#f #n1 #n2 #Hn
/4 width=2 by eq_inv_fbr_dapp_bi, eq_inv_pnpred_bi, eq_inv_npsucc_bi/
qed-.
