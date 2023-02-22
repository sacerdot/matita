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

include "static_2/syntax/tueq.ma".

(* TAIL SORT-IRRELEVANT EQUIVALENCE ON TERMS ********************************)

(* Main properties **********************************************************)

theorem tueq_trans: Transitive … tueq.
#T1 #T #H elim H -T1 -T
[ #s1 #s #X #H
  elim (tueq_inv_sort1 … H) -s /2 width=1 by tueq_sort/
| #i1 #i #H //
| #l1 #l #H //
| #p #I #V #T1 #T #_ #IHT #X #H
  elim (tueq_inv_bind1 … H) -H /3 width=1 by tueq_bind/
| #V #T1 #T #_ #IHT #X #H
  elim (tueq_inv_appl1 … H) -H /3 width=1 by tueq_appl/
| #V1 #V #T1 #T #_ #_ #IHV #IHT #X #H
  elim (tueq_inv_cast1 … H) -H /3 width=1 by tueq_cast/
]
qed-.

theorem tueq_canc_sn: left_cancellable … tueq.
/3 width=3 by tueq_trans, tueq_sym/ qed-.

theorem tueq_canc_dx: right_cancellable … tueq.
/3 width=3 by tueq_trans, tueq_sym/ qed-.

theorem tueq_repl: ∀T1,T2. T1 ≅ T2 →
                   ∀U1. T1 ≅ U1 → ∀U2. T2 ≅ U2 → U1 ≅ U2.
/3 width=3 by tueq_canc_sn, tueq_trans/ qed-.
