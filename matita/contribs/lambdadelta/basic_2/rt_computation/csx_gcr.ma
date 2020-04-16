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

include "static_2/static/gcp_cr.ma".
include "basic_2/rt_computation/csx_cnx_vector.ma".
include "basic_2/rt_computation/csx_csx_vector.ma".

(* STRONGLY NORMALIZING TERMS FOR EXTENDED PARALLEL RT-TRANSITION ***********)

(* Main properties with generic candidates of reducibility ******************)

theorem csx_gcr:
        gcr cpx teqx csx csx.
@mk_gcr
[ //
| #G #L #Vs #Hvs #T #HT #H
  @(csx_applv_cnx … H) -H // (**) (* auto fails *)
| /2 width=1 by csx_applv_beta/
| /2 width=7 by csx_applv_delta_drops/
| /3 width=3 by csx_applv_theta, csx_abbr/
| /2 width=1 by csx_applv_cast/
]
qed.
