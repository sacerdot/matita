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

include "delayed_updating/syntax/preterm.ma".
include "delayed_updating/notation/functions/hash_1.ma".
include "delayed_updating/notation/functions/phi_2.ma".
include "delayed_updating/notation/functions/lamda_1.ma".
include "delayed_updating/notation/functions/at_2.ma".

(* CONSTRUCTORS FOR PRETERM *************************************************)

definition preterm_node_0 (l): preterm ≝
           λp. l◗𝐞 = p.

definition preterm_node_1 (l): preterm → preterm ≝
           λt,p. ∃∃q. q ϵ t & l◗q = p.

definition preterm_node_2 (l1) (l2): preterm → preterm → preterm ≝
           λt1,t2,p.
           ∨∨ ∃∃q. q ϵ t1 & l1◗q = p
            | ∃∃q. q ϵ t2 & l2◗q = p.

interpretation
  "outer variable reference by depth (preterm)"
  'Hash n = (preterm_node_0 (label_node_d n)).

interpretation
  "inner variable reference by depth (preterm)"
  'Phi n t = (preterm_node_1 (label_node_d n) t).

interpretation
  "name-free functional abstraction (preterm)"
  'Lamda t = (preterm_node_1 label_edge_L t).

interpretation
  "application (preterm)"
  'At u t = (preterm_node_2 label_edge_S label_edge_A u t).

(* Basic Inversions *********************************************************)

lemma preterm_in_root_inv_lcons_oref:
      ∀p,l,n. l◗p ϵ ▵#n →
      ∧∧ 𝗱n = l & 𝐞 = p.
#p #l #n * #q
<list_append_lcons_sn #H0 destruct -H0
elim (eq_inv_list_empty_append … e0) -e0 #H0 #_
/2 width=1 by conj/
qed-.

lemma preterm_in_root_inv_lcons_iref:
      ∀t,p,l,n. l◗p ϵ ▵𝛗n.t →
      ∧∧ 𝗱n = l & p ϵ ▵t.
#t #p #l #n * #q
<list_append_lcons_sn * #r #Hr #H0 destruct
/3 width=2 by ex_intro, conj/
qed-.

lemma preterm_in_root_inv_lcons_abst:
      ∀t,p,l. l◗p ϵ ▵𝛌.t →
      ∧∧ 𝗟 = l & p ϵ ▵t.
#t #p #l * #q
<list_append_lcons_sn * #r #Hr #H0 destruct
/3 width=2 by ex_intro, conj/
qed-.

lemma preterm_in_root_inv_lcons_appl:
      ∀u,t,p,l. l◗p ϵ ▵@u.t →
      ∨∨ ∧∧ 𝗦 = l & p ϵ ▵u
       | ∧∧ 𝗔 = l & p ϵ ▵t.
#u #t #p #l * #q
<list_append_lcons_sn * * #r #Hr #H0 destruct
/4 width=2 by ex_intro, or_introl, or_intror, conj/
qed-.
