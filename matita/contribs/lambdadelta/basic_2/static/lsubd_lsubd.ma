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

include "basic_2/static/lsubd_da.ma".

(* LOCAL ENVIRONMENT REFINEMENT FOR DEGREE ASSIGNMENT ***********************)

(* Main properties **********************************************************)

theorem lsubd_trans: ∀h,g,G. Transitive … (lsubd h g G).
#h #g #G #L1 #L #H elim H -L1 -L
[ #X #H >(lsubd_inv_atom1 … H) -H //
| #I #L1 #L #Y #HL1 #IHL1 #X #H
  elim (lsubd_inv_pair1 … H) -H * #L2
  [ #HL2 #H destruct /3 width=1/
  | #W #V #l #HV #HW #HL2 #H1 #H2 #H3 destruct
    /3 width=3 by lsubd_beta, lsubd_da_trans/
  ]
| #L1 #L #W #V #l #HV #HW #HL1 #IHL1 #X #H
  elim (lsubd_inv_pair1 … H) -H * #L2
  [ #HL2 #H destruct /3 width=5 by lsubd_beta, lsubd_da_conf/
  | #W0 #V0 #l0 #_ #_ #_ #H destruct
  ]
]
qed-.
