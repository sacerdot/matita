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

include "basic_2/static/lsuba_aaa.ma".

(* LOCAL ENVIRONMENT REFINEMENT FOR ATOMIC ARITY ASSIGNMENT *****************)

(* Main properties **********************************************************)

theorem lsuba_trans: ∀L1,L. L1 ÷⊑ L → ∀L2. L ÷⊑ L2 → L1 ÷⊑ L2.
#L1 #L #H elim H -L1 -L
[ #X #H >(lsuba_inv_atom1 … H) -H //
| #I #L1 #L #V #HL1 #IHL1 #X #H
  elim (lsuba_inv_pair1 … H) -H * #L2
  [ #HL2 #H destruct /3 width=1/
  | #V #A #HLV #HL2V #HL2 #H1 #H2 destruct /3 width=3/
  ]
| #L1 #L #V1 #W #A1 #HV1 #HW #HL1 #IHL1 #X #H
  elim (lsuba_inv_pair1 … H) -H * #L2
  [ #HL2 #H destruct /3 width=5/
  | #V #A2 #_ #_ #_ #_ #H destruct
  ]
]
qed.
