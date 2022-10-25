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

include "delayed_updating/unwind/unwind2_rmap_eq.ma".
include "delayed_updating/syntax/path_closed.ma".
include "delayed_updating/syntax/path_depth.ma".
include "ground/relocation/xap.ma".
include "ground/lib/stream_eq_eq.ma".
include "ground/arith/nat_le_plus.ma".
include "ground/arith/nat_le_pred.ma".

(* TAILED UNWIND FOR RELOCATION MAP *****************************************)

(* Destructions with cpp ****************************************************)

lemma unwind2_rmap_append_closed_dx_xap_le (o) (f) (p) (q) (n):
      q ϵ 𝐂❨o,n❩ → ∀m. m ≤ n →
      ▶[f]q＠❨m❩ = ▶[f](p●q)＠❨m❩.
#o #f #p #q #n #Hq elim Hq -q -n
[|*: #q #n [ #k #_ ] #_ #IH ] #m #Hm
[ <(nle_inv_zero_dx … Hm) -m //
| <unwind2_rmap_d_dx <unwind2_rmap_d_dx
  <tr_compose_xap <tr_compose_xap
  @IH -IH (**) (* auto too slow *)
  @nle_trans [| @tr_uni_xap ]
  /2 width=1 by nle_plus_bi_dx/
| <unwind2_rmap_m_dx <unwind2_rmap_m_dx
  /2 width=2 by/
| <unwind2_rmap_L_dx <unwind2_rmap_L_dx
  elim (nle_inv_succ_dx … Hm) -Hm // * #Hm #H0
  >H0 -H0 <tr_xap_push <tr_xap_push
  /3 width=2 by eq_f/
| <unwind2_rmap_A_dx <unwind2_rmap_A_dx
  /2 width=2 by/
| <unwind2_rmap_S_dx <unwind2_rmap_S_dx
  /2 width=2 by/
]
qed-.

lemma unwind2_rmap_append_closed_Lq_dx_nap (o) (f) (p) (q) (n):
      q ϵ 𝐂❨o,n❩ →
      ▶[f](𝗟◗q)＠§❨n❩ = ▶[f](p●𝗟◗q)＠§❨n❩.
#o #f #p #q #n #Hq
lapply (pcc_L_sn … Hq) -Hq #Hq
lapply (unwind2_rmap_append_closed_dx_xap_le o f p … Hq (↑n) ?) -Hq //
<tr_xap_succ_nap <tr_xap_succ_nap #Hq
/2 width=1 by eq_inv_nsucc_bi/
qed-.

lemma unwind2_rmap_push_closed_nap (o) (f) (q) (n):
      q ϵ 𝐂❨o,n❩ →
      ♭q = ▶[⫯f]q＠§❨n❩.
#o #f #q #n #Hq elim Hq -q -n
[|*: #q #n [ #k #_ ] #_ #IH ] //
<unwind2_rmap_d_dx <tr_compose_nap //
qed-.

lemma unwind2_rmap_append_closed_Lq_dx_nap_depth (o) (f) (p) (q) (n):
      q ϵ 𝐂❨o,n❩ →
      ♭q = ▶[f](p●𝗟◗q)＠§❨n❩.
#o #f #p #q #n #Hq
<unwind2_rmap_append_closed_Lq_dx_nap //
/2 width=2 by unwind2_rmap_push_closed_nap/
qed-.

lemma tls_succ_plus_unwind2_rmap_push_closed (o) (f) (q) (n):
      q ϵ 𝐂❨o,n❩ →
      ∀m. ⇂*[m]f ≗ ⇂*[↑(m+n)]▶[⫯f]q.
#o #f #q #n #Hq elim Hq -q -n //
#q #n [ #k #_ ] #_ #IH #m
[ @(stream_eq_trans … (tls_unwind2_rmap_d_dx …))
  >nrplus_inj_dx >nrplus_inj_sn >nsucc_unfold //
| <unwind2_rmap_L_dx <nplus_succ_dx //
]
qed-.

lemma tls_succ_unwind2_rmap_append_closed_Lq_dx (o) (f) (p) (q) (n):
      q ϵ 𝐂❨o,n❩ →
      ▶[f]p ≗ ⇂*[↑n]▶[f](p●𝗟◗q).
/2 width=2 by tls_succ_plus_unwind2_rmap_push_closed/
qed-.

lemma unwind2_rmap_append_closed_Lq_dx_nap_plus (o) (f) (p) (q) (m) (n):
      q ϵ 𝐂❨o,n❩ →
      ▶[f]p＠❨m❩+♭q = ▶[f](p●𝗟◗q)＠§❨m+n❩.
#o #f #p #q #m #n #Hq
<tr_nap_plus @eq_f2
[ <(tr_xap_eq_repl … (tls_succ_unwind2_rmap_append_closed_Lq_dx …)) //
| /2 width=2 by unwind2_rmap_append_closed_Lq_dx_nap_depth/
]
qed-.
