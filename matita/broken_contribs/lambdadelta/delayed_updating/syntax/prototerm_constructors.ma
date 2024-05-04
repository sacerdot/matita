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
include "delayed_updating/notation/functions/hash_1.ma".
include "delayed_updating/notation/functions/tau_2.ma".
include "delayed_updating/notation/functions/lamda_1.ma".
include "delayed_updating/notation/functions/at_2.ma".
include "ground/subsets/subset_or.ma".
include "ground/subsets/subset_listed.ma".

(* CONSTRUCTORS FOR PROTOTERM ***********************************************)

definition term_node_0 (l): 𝕋 ≝
           ❴l◗𝐞❵.

definition term_node_1 (l): 𝕋 → 𝕋 ≝
           λt. l◗t.

definition term_node_2 (l1) (l2): 𝕋 → 𝕋 → 𝕋 ≝
           λt1,t2.
           (term_node_1 l1 t1) ∪ (term_node_1 l2 t2).

interpretation
  "outer variable reference by depth (prototerm)"
  'Hash k = (term_node_0 (label_d k)).

interpretation
  "inner variable reference by depth (prototerm)"
  'Tau k t = (term_node_1 (label_d k) t).

interpretation
  "name-free functional abstraction (prototerm)"
  'Lamda t = (term_node_1 label_L t).

interpretation
  "application (prototerm)"
  'At u t = (term_node_2 label_S label_A u t).

(* Basic constructions *******************************************************)

lemma in_comp_oref_hd (k):
      (𝗱k◗𝐞) ϵ ⧣k.
// qed.

lemma in_comp_iref_hd (t) (q) (k):
      q ϵ t → 𝗱k◗q ϵ 𝛕k.t.
/2 width=1 by pt_append_in/ qed.

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
      ∃∃q. 𝗱k◗q = p & q ϵ t.
#t #p #k * #q #Hq #H0 destruct
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
