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

include "basic_2/syntax/tdeq.ma".

(* DEGREE-BASED EQUIVALENCE ON TERMS ****************************************)

(* Main properties **********************************************************)

theorem tdeq_trans: ∀h,o. Transitive … (tdeq h o).
#h #o #T1 #T #H elim H -T1 -T
[ #s1 #s #d #Hs1 #Hs #X #H
  elim (tdeq_inv_sort1_deg … H … Hs) -s /2 width=3 by tdeq_sort/
| #i1 #i #H <(tdeq_inv_lref1 … H) -H //
| #l1 #l #H <(tdeq_inv_gref1 … H) -H //
| #I #V1 #V #T1 #T #_ #_ #IHV #IHT #X #H destruct
  elim (tdeq_inv_pair1 … H) -H /3 width=1 by tdeq_pair/
]
qed-.
