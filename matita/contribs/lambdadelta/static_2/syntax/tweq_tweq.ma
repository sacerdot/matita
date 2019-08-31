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

include "static_2/syntax/tweq.ma".

(* SORT-IRRELEVANT WHD EQUIVALENCE ON TERMS *********************************)

(* Main properties **********************************************************)

theorem tweq_trans: Transitive … tweq.
#T1 #T #H elim H -T1 -T
[ #s1 #s #X #H
  elim (tweq_inv_sort_sn … H) -s #s2 destruct
  /2 width=1 by tweq_sort/
| #i1 #i #H //
| #l1 #l #H //
| #p #V1 #V #T1 #T #_ #IHT #X #H
  elim (tweq_inv_abbr_sn … H) -H #V2 #T2 #HT #H destruct
  /4 width=1 by tweq_abbr/
| #p #V1 #V #T1 #T #X #H
  elim (tweq_inv_abst_sn … H) -H #V2 #T2 #H destruct
  /2 width=1 by tweq_abst/
| #V1 #V #T1 #T #_ #IHT #X #H
  elim (tweq_inv_appl_sn … H) -H #V2 #T2 #HT #H destruct
  /3 width=1 by tweq_appl/
| #V1 #V #T1 #T #_ #_ #IHV #IHT #X #H
  elim (tweq_inv_cast_sn … H) -H #V2 #T2 #HV #HT #H destruct
  /3 width=1 by tweq_cast/
]
qed-.

theorem tweq_canc_sn: left_cancellable … tweq.
/3 width=3 by tweq_trans, tweq_sym/ qed-.

theorem tweq_canc_dx: right_cancellable … tweq.
/3 width=3 by tweq_trans, tweq_sym/ qed-.

theorem tweq_repl:
        ∀T1,T2. T1 ≅ T2 → ∀U1. T1 ≅ U1 → ∀U2. T2 ≅ U2 → U1 ≅ U2.
/3 width=3 by tweq_canc_sn, tweq_trans/ qed-.
