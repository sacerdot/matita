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

include "delayed_updating/substitution/lift.ma".
include "delayed_updating/syntax/path_depth.ma".
include "ground/relocation/tr_id_compose.ma".
include "ground/relocation/tr_compose_compose.ma".
include "ground/relocation/tr_compose_pn.ma".
include "ground/relocation/tr_compose_eq.ma".
include "ground/relocation/tr_pn_eq.ma".
include "ground/lib/stream_eq_eq.ma".

(* LIFT FOR PATH ***********************************************************)

(* Constructions with depth ************************************************)

lemma lift_rmap_decompose (p) (f):
      ↑[p]f ≗ (⫯*[❘p❘]f)∘(↑[p]𝐢).
#p @(list_ind_rcons … p) -p
[ #f <lift_rmap_empty <lift_rmap_empty <tr_pushs_zero //
| #p * [ #n ] #IH #f //
  [ <lift_rmap_d_dx <lift_rmap_d_dx <depth_d_dx
    @(stream_eq_trans … (tr_compose_assoc …))
    /2 width=1 by tr_compose_eq_repl/
  | <lift_rmap_L_dx <lift_rmap_L_dx <depth_L_dx
    <tr_pushs_succ <tr_compose_push_bi
    /2 width=1 by tr_push_eq_repl/
  ]
]
qed.

lemma lift_rmap_pap_le (f) (p) (n):
      (↑[p]𝐢)@❨n❩ < ↑❘p❘ → (↑[p]𝐢)@❨n❩ = (↑[p]f)@❨n❩.
#f #p #n #Hn
>(tr_pap_eq_repl … (↑[p]f) … (lift_rmap_decompose …))
<tr_compose_pap @tr_pap_pushs_le //
qed.
