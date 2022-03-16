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

lemma lift_rmap_pap_le (f1) (f2) (p) (m:pnat) (l:nat):
      ninj (m+⧣p+l) = ❘p❘ →
      (↑[p]f1)@❨m❩ = (↑[p]f2)@❨m❩.
#f1 #f2 #p @(list_ind_rcons … p) -p
[ #m #l <depth_empty #H0 destruct
| #p * [ #n ] #IH #m #l
  [ <update_d_dx <depth_d_dx <lift_rmap_pap_d_dx <lift_rmap_pap_d_dx
    <nplus_comm <nrplus_inj_sn <nrplus_inj_dx <nrplus_pplus_assoc
    #H0 <(IH … l) -IH //
  | /2 width=2 by/
  | <update_L_dx <depth_L_dx <lift_rmap_L_dx <lift_rmap_L_dx
    cases m -m // #m
    <nrplus_succ_sn <nrplus_succ_sn >nsucc_inj #H0
    <tr_pap_push <tr_pap_push
    <(IH … l) -IH //
  | /2 width=2 by/
  | /2 width=2 by/
  ]
]
qed.

lemma lift_rmap_pap_gt (f) (p) (m):
      f@❨m+⧣p❩+❘p❘ = (↑[p]f)@❨m+❘p❘❩.
#f #p @(list_ind_rcons … p) -p [ // ]
#p * [ #n ] #IH #m
[ <update_d_dx <depth_d_dx
  <nplus_comm <nrplus_inj_sn <nrplus_inj_dx <nrplus_pplus_assoc
  <lift_rmap_pap_d_dx >IH -IH //
| //
| <update_L_dx <depth_L_dx
  <nrplus_succ_dx <nrplus_succ_dx <lift_rmap_L_dx <tr_pap_push //
| //
| //
]
qed.

lemma lift_rmap_tls_gt (f) (p) (m:pnat):
      ⇂*[ninj (m+⧣p)]f ≗ ⇂*[ninj (m+❘p❘)]↑[p]f.
#f #p @(list_ind_rcons … p) -p [ // ]
#p * [ #n ] #IH #m
[ <update_d_dx <depth_d_dx
  <nplus_comm <nrplus_inj_sn <nrplus_inj_dx <nrplus_pplus_assoc
  @(stream_eq_trans … (lift_rmap_tls_d_dx …))
  @(stream_eq_canc_dx … (IH …)) -IH //
| //
| <update_L_dx <depth_L_dx
  <nrplus_succ_dx >nsucc_inj //
| //
| //
]
qed.

lemma lift_rmap_tls_eq (f) (p):
      ⇂*[⧣p]f ≗ ⇂*[↑❘p❘]↑[p]⫯f.
(*
#f #p @(list_ind_rcons … p) -p //
#p * [ #n ] #IH //
<update_d_dx <depth_d_dx <lift_rmap_d_dx
@(stream_eq_trans … (tr_tls_compose_uni_dx …))
*)
