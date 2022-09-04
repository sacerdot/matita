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

include "delayed_updating/substitution/lift_prototerm_id.ma".
include "delayed_updating/substitution/lift_path_uni.ma".
include "delayed_updating/syntax/prototerm_constructors_eq.ma".
include "ground/relocation/nap.ma".

(* LIFT FOR PROTOTERM *******************************************************)

lemma lift_term_iref_pap_sn (f) (t:prototerm) (k:pnat):
      (𝛕f＠⧣❨k❩.↑[⇂*[k]f]t) ⊆ ↑[f](𝛕k.t).
#f #t #k #p * #q * #r #Hr #H1 #H2 destruct
@(ex2_intro … (𝗱k◗𝗺◗r))
/2 width=1 by in_comp_iref/
qed-.

lemma lift_term_iref_pap_dx (f) (t) (k:pnat):
      ↑[f](𝛕k.t) ⊆ 𝛕f＠⧣❨k❩.↑[⇂*[k]f]t.
#f #t #k #p * #q #Hq #H0 destruct
elim (in_comp_inv_iref … Hq) -Hq #p #H0 #Hp destruct
<lift_path_d_sn <lift_path_m_sn
/3 width=1 by in_comp_iref, in_comp_lift_path_term/
qed-.

lemma lift_term_iref_pap (f) (t) (k:pnat):
      (𝛕f＠⧣❨k❩.↑[⇂*[k]f]t) ⇔ ↑[f](𝛕k.t).
/3 width=1 by conj, lift_term_iref_pap_sn, lift_term_iref_pap_dx/
qed.

lemma lift_term_iref_nap (f) (t) (n):
      (𝛕↑(f＠§❨n❩).↑[⇂*[↑n]f]t) ⇔ ↑[f](𝛕↑n.t).
#f #t #n
>tr_pap_succ_nap //
qed.

lemma lift_term_iref_uni (t) (n) (k):
      (𝛕(k+n).t) ⇔ ↑[𝐮❨n❩](𝛕k.t).
#t #n #k
@(subset_eq_trans … (lift_term_iref_pap …))
<tr_uni_pap >nsucc_pnpred <tr_tls_succ_uni
/3 width=1 by iref_eq_repl, lift_term_id/
qed.
