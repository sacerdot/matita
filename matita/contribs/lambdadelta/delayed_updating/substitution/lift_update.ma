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

include "delayed_updating/substitution/lift_eq.ma".
include "delayed_updating/syntax/path_update.ma".
include "delayed_updating/syntax/path_depth.ma".
include "ground/lib/stream_eq_eq.ma".

(* LIFT FOR PATH ***********************************************************)

(* Constructions with update ***********************************************)

axiom arith1 (p,q:pnat) (n:nat):
      nrplus (pplus p q) n = pplus p (nrplus q n).

lemma pippo (f) (p) (m:pnat):
      ⇂*[ninj (m+⧣p)]f ≗ ⇂*[ninj (m+❘p❘)]↑[p]f.
#f #p @(list_ind_rcons … p) -p [ // ]
#p * [ #n ] #IH #m
[ <update_d_dx <depth_d_dx
  <nplus_comm <nrplus_inj_sn <nrplus_inj_dx <arith1
  @(stream_eq_trans … (lift_rmap_tls_d_dx …))
  @(stream_eq_canc_dx … (IH …)) -IH //
| //
| <update_L_dx <depth_L_dx
  <nrplus_succ_dx >nsucc_inj //
| //
| //
]
qed.  
