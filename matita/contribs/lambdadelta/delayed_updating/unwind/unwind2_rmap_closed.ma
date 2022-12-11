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
include "ground/relocation/nap.ma".
include "ground/lib/stream_tls_plus.ma".
include "ground/lib/stream_eq_eq.ma".

(* TAILED UNWIND FOR RELOCATION MAP *****************************************)

(* Destructions with cpp ****************************************************)

lemma nap_plus_unwind2_rmap_closed (o) (f) (q) (m) (n):
      q ϵ 𝐂❨o,n❩ →
      f＠§❨m❩+♭q = ▶[f]q＠§❨m+n❩.
#o #f #q #m #n #Hq elim Hq -q -n //
#q #n [ #k #_ ] #_ #IH
[ <depth_d_dx <unwind2_rmap_d_dx
  <tr_compose_nap <tr_uni_nap //
| <depth_L_dx <unwind2_rmap_L_dx
  <tr_nap_push <nplus_succ_dx //
]
qed-.

lemma nap_plus_unwind2_rmap_append_closed_Lq_dx (o) (f) (p) (q) (m) (n):
      q ϵ 𝐂❨o,n❩ →
      (⫯▶[f]p)＠§❨m❩+♭q = ▶[f](p●𝗟◗q)＠§❨m+n❩.
#o #f #p #q #m #n #Hn
/2 width=2 by nap_plus_unwind2_rmap_closed/
qed-.

lemma nap_unwind2_rmap_append_closed_Lq_dx (o) (f) (p) (q) (n):
      q ϵ 𝐂❨o,n❩ →
      ♭q = ▶[f](p●𝗟◗q)＠§❨n❩.
#o #f #p #q #n #Hn
>(nplus_zero_sn n)
<(nap_plus_unwind2_rmap_append_closed_Lq_dx … Hn) -Hn
<nplus_zero_sn //
qed-.

lemma tls_succ_plus_unwind2_rmap_push_closed (o) (f) (q) (n):
      q ϵ 𝐂❨o,n❩ →
      ∀m. ⇂*[m]f ≗ ⇂*[↑(m+n)]▶[⫯f]q.
#o #f #q #n #Hn elim Hn -q -n //
#q #n #k #_ #_ #IH #m
@(stream_eq_trans … (tls_unwind2_rmap_d_dx …))
>nrplus_inj_dx >nrplus_inj_sn >nsucc_unfold //
qed-.

lemma tls_succ_unwind2_rmap_push_closed (o) (f) (q) (n):
      q ϵ 𝐂❨o,n❩ →
      f ≗ ⇂*[↑n]▶[⫯f](q).
#o #f #q #n #Hn
/2 width=2 by tls_succ_plus_unwind2_rmap_push_closed/
qed-.

lemma tls_succ_plus_unwind2_rmap_append_closed_Lq_dx (o) (f) (p) (q) (n):
      q ϵ 𝐂❨o,n❩ →
      ∀m. ⇂*[m]▶[f]p ≗ ⇂*[↑(m+n)]▶[f](p●𝗟◗q).
#o #f #p #q #n #Hn #m
/2 width=2 by tls_succ_plus_unwind2_rmap_push_closed/
qed-.
