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

include "basic_2/dynamic/lsubv_cnv.ma".

(* LOCAL ENVIRONMENT REFINEMENT FOR NATIVE VALIDITY *************************)

(* Main properties **********************************************************)

(* Note: not valid in Basic_2A1 *)
theorem lsubv_trans (a) (h) (G): Transitive … (lsubv a h G).
#a #h #G #L1 #L #H elim H -L1 -L //
[ #I #K1 #K #HK1 #IH #Y #H
  elim (lsubv_inv_bind_sn … H) -H *
  [ #K2 #HK2 #H destruct /3 width=1 by lsubv_bind/
  | #K2 #W #V #HWV #HK2 #H1 #H2 destruct /3 width=3 by lsubv_cnv_trans, lsubv_beta/
  ]
| #K1 #K #W #V #HWV #_ #IH #Y #H
  elim (lsubv_inv_abst_sn … H) -H
  #K2 #HK2 #H1 destruct /3 width=1 by lsubv_beta/
]
qed-.
