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

include "delayed_updating/syntax/prototerm.ma".
include "delayed_updating/notation/functions/m_hook_1.ma".
include "delayed_updating/notation/functions/hash_1.ma".
include "delayed_updating/notation/functions/tau_2.ma".
include "delayed_updating/notation/functions/tau_3.ma".
include "delayed_updating/notation/functions/lamda_1.ma".
include "delayed_updating/notation/functions/at_2.ma".

(* CONSTRUCTORS FOR PROTOTERM ***********************************************)

definition prototerm_node_0 (l): prototerm ≝
           λp. l◗𝐞 = p.

definition prototerm_node_1 (l): prototerm → prototerm ≝
           λt,p. ∃∃q. q ϵ t & l◗q = p.

definition prototerm_node_1_2 (l1) (l2): prototerm → prototerm ≝
           λt,p. ∃∃q. q ϵ t & l1◗l2◗q = p.

definition prototerm_node_2 (l1) (l2): prototerm → prototerm → prototerm ≝
           λt1,t2,p.
           ∨∨ ∃∃q. q ϵ t1 & l1◗q = p
            | ∃∃q. q ϵ t2 & l2◗q = p.

interpretation
  "mark (prototerm)"
  'MHook t = (prototerm_node_1 label_m t).

interpretation
  "outer variable reference by depth (prototerm)"
  'Hash k = (prototerm_node_0 (label_d k)).

interpretation
  "inner variable reference by depth (prototerm)"
  'Tau k t = (prototerm_node_1_2 (label_d k) label_m t).

interpretation
  "inner variable reference by depth with offset (prototerm)"
  'Tau k d t = (prototerm_node_1_2 (label_d2 k d) label_m t).

interpretation
  "name-free functional abstraction (prototerm)"
  'Lamda t = (prototerm_node_1 label_L t).

interpretation
  "application (prototerm)"
  'At u t = (prototerm_node_2 label_S label_A u t).

(* Basic constructions *******************************************************)

lemma in_comp_iref (t) (q) (k):
      q ϵ t → 𝗱k◗𝗺◗q ϵ 𝛕k.t.
/2 width=3 by ex2_intro/ qed.

lemma in_comp_iref2 (t) (q) (k) (d):
      q ϵ t → 𝗱❨k,d❩◗𝗺◗q ϵ 𝛕❨k,d❩.t.
/2 width=3 by ex2_intro/ qed.

(* Basic inversions *********************************************************)

lemma in_comp_inv_iref (t) (p) (k):
      p ϵ 𝛕k.t →
      ∃∃q. 𝗱k◗𝗺◗q = p & q ϵ t.
#t #p #k * #q #Hq #Hp
/2 width=3 by ex2_intro/
qed-.

lemma in_comp_inv_iref2 (t) (p) (k) (d):
      p ϵ 𝛕❨k,d❩.t →
      ∃∃q. 𝗱❨k,d❩◗𝗺◗q = p & q ϵ t.
#t #p #k #d * #q #Hq #Hp
/2 width=3 by ex2_intro/
qed-.

(* COMMENT
lemma prototerm_in_root_inv_lcons_oref:
      ∀p,l,n. l◗p ϵ ▵#n →
      ∧∧ 𝗱n = l & 𝐞 = p.
#p #l #n * #q
<list_append_lcons_sn #H0 destruct -H0
elim (eq_inv_list_empty_append … e0) -e0 #H0 #_
/2 width=1 by conj/
qed-.

lemma prototerm_in_root_inv_lcons_iref:
      ∀t,p,l,n. l◗p ϵ ▵𝛕n.t →
      ∧∧ 𝗱n = l & p ϵ ▵ɱ.t.
#t #p #l #n * #q * #r #Hr
<list_append_lcons_sn #H0 destruct -H0
/4 width=4 by ex2_intro, ex_intro, conj/
qed-.

lemma prototerm_in_root_inv_lcons_mark:
      ∀t,p,l. l◗p ϵ ▵ɱ.t →
      ∧∧ 𝗺 = l & p ϵ ▵t.
#t #p #l * #q * #r #Hr
<list_append_lcons_sn #H0 destruct
/3 width=2 by ex_intro, conj/
qed-.

lemma prototerm_in_root_inv_lcons_abst:
      ∀t,p,l. l◗p ϵ ▵𝛌.t →
      ∧∧ 𝗟 = l & p ϵ ▵t.
#t #p #l * #q * #r #Hr
<list_append_lcons_sn #H0 destruct
/3 width=2 by ex_intro, conj/
qed-.

lemma prototerm_in_root_inv_lcons_appl:
      ∀u,t,p,l. l◗p ϵ ▵@u.t →
      ∨∨ ∧∧ 𝗦 = l & p ϵ ▵u
       | ∧∧ 𝗔 = l & p ϵ ▵t.
#u #t #p #l * #q * * #r #Hr
<list_append_lcons_sn #H0 destruct
/4 width=2 by ex_intro, or_introl, or_intror, conj/
qed-.
*)
