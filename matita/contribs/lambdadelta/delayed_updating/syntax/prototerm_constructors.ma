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
  "name-free functional abstraction (prototerm)"
  'Lamda t = (prototerm_node_1 label_L t).

interpretation
  "application (prototerm)"
  'At u t = (prototerm_node_2 label_S label_A u t).

(* Basic constructions *******************************************************)

lemma in_comp_oref_hd (k):
      (𝗱k◗𝐞) ϵ ⧣k.
// qed.

lemma in_comp_iref_hd (t) (q) (k):
      q ϵ t → 𝗱k◗𝗺◗q ϵ 𝛕k.t.
/2 width=3 by ex2_intro/ qed.

lemma in_comp_abst_hd (t) (q):
      q ϵ t → 𝗟◗q ϵ 𝛌.t.
/2 width=3 by ex2_intro/ qed.

lemma in_comp_appl_sd (u) (t) (q):
      q ϵ u → 𝗦◗q ϵ ＠u.t.
/3 width=3 by ex2_intro, or_introl/ qed.

lemma in_comp_appl_hd (u) (t) (q):
      q ϵ t → 𝗔◗q ϵ ＠u.t.
/3 width=3 by ex2_intro, or_intror/ qed.

(* Basic inversions *********************************************************)

lemma in_comp_inv_iref (t) (p) (k):
      p ϵ 𝛕k.t →
      ∃∃q. 𝗱k◗𝗺◗q = p & q ϵ t.
#t #p #k * #q #Hq #Hp
/2 width=3 by ex2_intro/
qed-.

lemma in_comp_inv_abst (t) (p):
      p ϵ 𝛌.t →
      ∃∃q. 𝗟◗q = p & q ϵ t.
#t #p * #q #Hq #Hp
/2 width=3 by ex2_intro/
qed-.

lemma in_comp_inv_appl (u) (t) (p):
      p ϵ ＠u.t →
      ∨∨ ∃∃q. 𝗦◗q = p & q ϵ u
       | ∃∃q. 𝗔◗q = p & q ϵ t.
#u #t #p * * #q #Hq #Hp
/3 width=3 by ex2_intro, or_introl, or_intror/
qed-.

(* Advanced inversions ******************************************************)

lemma in_comp_inv_abst_hd (t) (p):
      (𝗟◗p) ϵ 𝛌.t → p ϵ t.
#t #p #H0
elim (in_comp_inv_abst … H0) -H0 #q #H0 #Hq
elim (eq_inv_list_rcons_bi ????? H0) -H0 #H1 #H2 destruct //
qed-. 

lemma in_comp_inv_appl_sd (u) (t) (p):
      (𝗦◗p) ϵ ＠u.t → p ϵ u.
#u #t #p #H0
elim (in_comp_inv_appl … H0) -H0 * #q #H0 #Hq
elim (eq_inv_list_rcons_bi ????? H0) -H0 #H1 #H2 destruct //
qed-. 

lemma in_comp_inv_appl_hd (u) (t) (p):
      (𝗔◗p) ϵ ＠u.t → p ϵ t.
#u #t #p #H0
elim (in_comp_inv_appl … H0) -H0 * #q #H0 #Hq
elim (eq_inv_list_rcons_bi ????? H0) -H0 #H1 #H2 destruct //
qed-. 
