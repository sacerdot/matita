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

theorem lsuba_trans: ∀G,L1,L. G ⊢ L1 ⫃⁝ L → ∀L2. G ⊢ L ⫃⁝ L2 → G ⊢ L1 ⫃⁝ L2.
#G #L1 #L #H elim H -L1 -L
[ #X #H >(lsuba_inv_atom1 … H) -H //
| #I #L1 #L #Y #HL1 #IHL1 #X #H
  elim (lsuba_inv_pair1 … H) -H * #L2
  [ #HL2 #H destruct /3 width=1/
  | #W #V #A #HV #HW #HL2 #H1 #H2 #H3 destruct
    /3 width=3 by lsuba_beta, lsuba_aaa_trans/
  ]
| #L1 #L #W #V #A #HV #HW #HL1 #IHL1 #X #H
  elim (lsuba_inv_pair1 … H) -H * #L2
  [ #HL2 #H destruct /3 width=5 by lsuba_beta, lsuba_aaa_conf/
  | #W0 #V0 #A0 #_ #_ #_ #H destruct
  ]
]
qed-.
