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

include "basic_2/static/gcp_cr.ma".
include "basic_2/rt_computation/csx_cnx_vector.ma".
include "basic_2/rt_computation/csx_csx_vector.ma".

(* STRONGLY NORMALIZING TERMS FOR UNBOUND PARALLEL RT-TRANSITION ************)

(* Main properties with generic candidates of reducibility ******************)

theorem csx_gcr: ∀h,o. gcr (cpx h) (tdeq h o) (csx h o) (csx h o).
#h #o @mk_gcr //
[ /3 width=1 by csx_applv_cnx/
|2,3,6: /2 width=1 by csx_applv_beta, csx_applv_sort, csx_applv_cast/
| /2 width=7 by csx_applv_delta/
| #G #L #V1b #V2b #HV12b #a #V #T #H #HV
  @(csx_applv_theta … HV12b) -HV12b
  @csx_abbr //
]
qed.
