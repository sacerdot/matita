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

include "delayed_updating/unwind/unwind1_rmap.ma".
include "delayed_updating/syntax/path_tail_depth.ma".
include "delayed_updating/syntax/path_height.ma".

(* BASIC UNWIND MAP FOR PATH ************************************************)

include "ground/relocation/tr_uni_pap.ma".
include "ground/relocation/tr_compose_pap.ma".
include "ground/relocation/tr_pap_pn.ma".
include "ground/notation/functions/applysucc_2.ma".
include "ground/arith/nat_plus_rplus.ma".
include "ground/arith/nat_pred_succ.ma".

definition tr_nap (f) (l:nat): nat ≝
           ↓(f@❨↑l❩).

interpretation
  "functional non-negative application (total relocation maps)"
  'ApplySucc f l = (tr_nap f l).

lemma tr_nap_unfold (f) (l):
      ↓(f@❨↑l❩) = f@↑❨l❩.
// qed.

lemma tr_compose_nap (f2) (f1) (l):
      f2@↑❨f1@↑❨l❩❩ = (f2∘f1)@↑❨l❩.
#f2 #f1 #l
<tr_nap_unfold <tr_nap_unfold <tr_nap_unfold
<tr_compose_pap <npsucc_pred //
qed.

lemma tr_uni_nap (n) (m):
      m + n = 𝐮❨n❩@↑❨m❩.
#n #m
<tr_nap_unfold
<tr_uni_pap <nrplus_npsucc_sn //
qed.

lemma tr_nap_push (f):
      ∀l. ↑(f@↑❨l❩) = (⫯f)@↑❨↑l❩.
#f #l
<tr_nap_unfold <tr_nap_unfold
<tr_pap_push <pnpred_psucc //
qed.

(****)

lemma unwind1_rmap_labels_L (n):
      (𝐢) = ▶(𝗟∗∗n).
#n @(nat_ind_succ … n) -n //
#n #IH
<labels_succ <unwind1_rmap_L_sn //
qed.

lemma unwind1_rmap_tail (p) (n):
      n + ♯(↳[n]p) = (▶↳[n]p)@↑❨n❩.
#p elim p -p //
#l #p #IH #n @(nat_ind_succ … n) -n //
#n #_ cases l [ #m ]
[ <unwind1_rmap_d_sn <tail_d_sn <height_d_sn
  <nplus_assoc >IH -IH <tr_compose_nap //
| <unwind1_rmap_m_sn <tail_m_sn <height_m_sn //
| <unwind1_rmap_L_sn <tail_L_sn <height_L_sn
  <tr_nap_push <npred_succ //
| <unwind1_rmap_A_sn <tail_A_sn <height_A_sn //
| <unwind1_rmap_S_sn <tail_S_sn <height_S_sn //
]
qed.
