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

include "basic_2/rt_computation/jsx_csx.ma".

(* COMPATIBILITY OF STRONG NORMALIZATION FOR UNBOUND RT-TRANSITION **********)

(* Main properties **********************************************************)

theorem jsx_trans (h) (G): Transitive … (jsx h G).
#h #G #L1 #L #H elim H -L1 -L
[ #L2 #H
  >(jsx_inv_atom_sn … H) -L2 //
| #I #K1 #K #_ #IH #L2 #H
  elim (jsx_inv_bind_sn … H) -H *
  [ #K2 #HK2 #H destruct /3 width=1 by jsx_bind/
  | #J #K2 #V #HK2 #HV #H1 #H2 destruct /3 width=1 by jsx_pair/
  ]
| #I #K1 #K #V #_ #HV #IH #L2 #H
  elim (jsx_inv_void_sn … H) -H #K2 #HK2 #H destruct
  /3 width=3 by rsx_jsx_trans, jsx_pair/
]
qed-.
