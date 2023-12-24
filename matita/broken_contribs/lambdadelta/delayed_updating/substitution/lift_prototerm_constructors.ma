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

include "delayed_updating/substitution/lift_prototerm_eq.ma".
include "delayed_updating/substitution/lift_path_uni.ma".
include "delayed_updating/syntax/prototerm_constructors_eq.ma".

(* LIFT FOR PROTOTERM *******************************************************)

(* Constructions with constructors for prototerm ****************************)

lemma lift_term_oref_xapp (f) (k):
      (⧣(f＠❨k❩)) ⇔ 🠡[f]⧣k.
#f #k @conj #p *
[ /2 width=1 by in_comp_lift_bi/
| #q * #H0 destruct //
]
qed.

lemma lift_term_iref_xapp_sn (f) (t:𝕋) (k):
      (𝛕f＠❨k❩.🠡[⫰*[k]f]t) ⊆ 🠡[f]𝛕k.t.
#f #t #k #p * #q * #s #Hs #H1 #H2 destruct
/3 width=1 by in_comp_lift_bi, in_comp_iref_hd/
qed-.

lemma lift_term_iref_xapp_dx (f) (t) (k):
      (🠡[f]𝛕k.t) ⊆ 𝛕f＠❨k❩.🠡[⫰*[k]f]t.
#f #t #k #p * #q #Hq #H0 destruct
elim (in_comp_inv_iref … Hq) -Hq #p #H0 #Hp destruct
<lift_path_d_sn
/3 width=1 by in_comp_iref_hd, in_comp_lift_bi/
qed-.

lemma lift_term_iref_xapp (f) (t) (k):
      (𝛕f＠❨k❩.🠡[⫰*[k]f]t) ⇔ 🠡[f](𝛕k.t).
/3 width=1 by conj, lift_term_iref_xapp_sn, lift_term_iref_xapp_dx/
qed.

lemma lift_term_iref_pos_uni (t) (n) (k):
      (𝛕((⁤k)+n).t) ⇔ 🠡[𝐮❨n❩](𝛕(⁤k).t).
#t #n #k
@(subset_eq_trans … (lift_term_iref_xapp …))
<fbr_xapp_uni_pos
/2 width=1 by iref_eq_repl_bi/
qed.

lemma lift_term_abst (f) (t):
      (𝛌.🠡[⫯f]t) ⇔ 🠡[f]𝛌.t.
#f #t @conj #p #Hp
[ elim (in_comp_inv_abst … Hp) -Hp #q #H1 * #r #Hr #H2 destruct
  /3 width=1 by in_comp_lift_bi, in_comp_abst_hd/
| elim Hp -Hp #q #Hq #H0 destruct
  elim (in_comp_inv_abst … Hq) -Hq #r #H0 #Hr destruct 
  /3 width=1 by in_comp_lift_bi, in_comp_abst_hd/
]
qed.

lemma lift_term_appl (f) (v) (t):
      ＠🠡[f]v.🠡[f]t ⇔ 🠡[f]＠v.t.
#f #v #t @conj #p #Hp
[ elim (in_comp_inv_appl … Hp) -Hp * #q #H1 * #r #Hr #H2 destruct
  /3 width=1 by in_comp_lift_bi, in_comp_appl_sd, in_comp_appl_hd/
| elim Hp -Hp #q #Hq #H0 destruct
  elim (in_comp_inv_appl … Hq) -Hq * #r #H0 #Hr destruct 
  /3 width=1 by in_comp_lift_bi, in_comp_appl_sd, in_comp_appl_hd/
]
qed.
