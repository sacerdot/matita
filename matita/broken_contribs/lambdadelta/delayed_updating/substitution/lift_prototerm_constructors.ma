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

(* Constructions with constructors for prototerm ****************************)

lemma lift_term_oref_pap (f) (k):
      (⧣(f＠⧣❨k❩)) ⇔ 🠡[f]⧣k.
#f #k @conj #p *
[ /2 width=1 by in_comp_lift_path_term/
| #q * #H0 destruct //
]
qed.

lemma lift_term_iref_pap_sn (f) (t:prototerm) (k:ℤ⁺):
      (𝛕f＠⧣❨k❩.🠡[⇂*[k]f]t) ⊆ 🠡[f](𝛕k.t).
#f #t #k #p * #q * #r #Hr #H1 #H2 destruct
@(ex2_intro … (𝗱k◗𝗺◗r))
/2 width=1 by in_comp_iref_hd/
qed-.

lemma lift_term_iref_pap_dx (f) (t) (k:ℤ⁺):
      🠡[f](𝛕k.t) ⊆ 𝛕f＠⧣❨k❩.🠡[⇂*[k]f]t.
#f #t #k #p * #q #Hq #H0 destruct
elim (in_comp_inv_iref … Hq) -Hq #p #H0 #Hp destruct
<lift_path_d_sn <lift_path_m_sn
/3 width=1 by in_comp_iref_hd, in_comp_lift_path_term/
qed-.

lemma lift_term_iref_pap (f) (t) (k:ℤ⁺):
      (𝛕f＠⧣❨k❩.🠡[⇂*[k]f]t) ⇔ 🠡[f](𝛕k.t).
/3 width=1 by conj, lift_term_iref_pap_sn, lift_term_iref_pap_dx/
qed.

lemma lift_term_iref_nap (f) (t) (n):
      (𝛕↑(f＠§❨n❩).🠡[⇂*[↑n]f]t) ⇔ 🠡[f](𝛕↑n.t).
#f #t #n
>tr_pap_succ_nap //
qed.

lemma lift_term_iref_uni (t) (n) (k):
      (𝛕(k+n).t) ⇔ 🠡[𝐮❨n❩](𝛕k.t).
#t #n #k
@(subset_eq_trans … (lift_term_iref_pap …))
<tr_uni_pap >nsucc_pnpred <tr_tls_succ_uni
/3 width=1 by iref_eq_repl, lift_term_id/
qed.

lemma lift_term_abst (f) (t):
      (𝛌.🠡[⫯f]t) ⇔ 🠡[f]𝛌.t.
#f #t @conj #p #Hp
[ elim (in_comp_inv_abst … Hp) -Hp #q #H1 * #r #Hr #H2 destruct
  /3 width=1 by in_comp_lift_path_term, in_comp_abst_hd/
| elim Hp -Hp #q #Hq #H0 destruct
  elim (in_comp_inv_abst … Hq) -Hq #r #H0 #Hr destruct 
  /3 width=1 by in_comp_lift_path_term, in_comp_abst_hd/
]
qed.

lemma lift_term_appl (f) (v) (t):
      ＠🠡[f]v.🠡[f]t ⇔ 🠡[f]＠v.t.
#f #v #t @conj #p #Hp
[ elim (in_comp_inv_appl … Hp) -Hp * #q #H1 * #r #Hr #H2 destruct
  /3 width=1 by in_comp_lift_path_term, in_comp_appl_sd, in_comp_appl_hd/
| elim Hp -Hp #q #Hq #H0 destruct
  elim (in_comp_inv_appl … Hq) -Hq * #r #H0 #Hr destruct 
  /3 width=1 by in_comp_lift_path_term, in_comp_appl_sd, in_comp_appl_hd/
]
qed.
