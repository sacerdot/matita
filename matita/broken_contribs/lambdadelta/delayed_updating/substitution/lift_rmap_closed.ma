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

include "delayed_updating/substitution/lift_rmap_eq.ma".
include "delayed_updating/syntax/path_closed.ma".
include "ground/relocation/xap.ma".
include "ground/lib/stream_eq_eq.ma".

(* LIFT MAP FOR PATH ********************************************************)

(* Destructions with cpp ****************************************************)

lemma tls_plus_lift_rmap_closed (o) (f) (q) (n):
      q ϵ 𝐂❨o,n,𝟎❩ →
      ∀m. ⇂*[m]f ≗ ⇂*[m+n]🠢[f]q.
#o #f #q #n #Hq elim Hq -q -n //
qed-.

lemma tls_lift_rmap_closed (o) (f) (q) (n):
      q ϵ 𝐂❨o,n,𝟎❩ →
      f ≗ ⇂*[n]🠢[f]q.
#o #f #q #n #H0
/2 width=2 by tls_plus_lift_rmap_closed/
qed-.

lemma tls_lift_rmap_append_closed_dx (o) (f) (p) (q) (n):
      q ϵ 𝐂❨o,n,𝟎❩ →
      (🠢[f]p) ≗ ⇂*[n]🠢[f](p●q).
#o #f #p #q #n #Hq
/2 width=2 by tls_lift_rmap_closed/
qed-.

lemma tls_succ_lift_rmap_append_closed_Lq_dx (o) (f) (p) (q) (n):
      q ϵ 𝐂❨o,n,𝟎❩ →
      (🠢[f]p) ≗ ⇂*[↑n]🠢[f](p●𝗟◗q).
#o #f #p #q #n #Hq
/3 width=2 by tls_lift_rmap_append_closed_dx, pcc_L_sn/
qed-.

lemma tls_succ_plus_lift_rmap_append_closed_bLq_dx (o1) (o2) (f) (p) (b) (q) (m) (n):
      b ϵ 𝐂❨o1,m,𝟎❩ → q ϵ 𝐂❨o2,n,𝟎❩ →
      (🠢[f]p) ≗ ⇂*[↑(m+n)]🠢[f](p●b●𝗟◗q).
#o1 #o2 #f #p #b #q #m #n #Hm #Hn
>nplus_succ_dx <stream_tls_plus
@(stream_eq_trans … (tls_lift_rmap_append_closed_dx … Hm))
/3 width=2 by stream_tls_eq_repl, tls_succ_lift_rmap_append_closed_Lq_dx/
qed-.

lemma nap_plus_lift_rmap_append_closed_Lq_dx (o) (f) (p) (q) (m) (n):
      q ϵ 𝐂❨o,n,𝟎❩ →
      (🠢[f]p＠❨m❩+🠢[f](p●𝗟◗q)＠§❨n❩) = 🠢[f](p●𝗟◗q)＠§❨m+n❩.
#o #f #p #q #m #n #Hq
<tr_nap_plus_dx_xap
/4 width=2 by eq_f2, tr_xap_eq_repl, tls_succ_lift_rmap_append_closed_Lq_dx/
qed-.
