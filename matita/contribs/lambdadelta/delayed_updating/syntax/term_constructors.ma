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

include "delayed_updating/syntax/term.ma".
include "delayed_updating/notation/functions/hash_1.ma".
include "delayed_updating/notation/functions/phi_2.ma".
include "delayed_updating/notation/functions/lamda_1.ma".
include "delayed_updating/notation/functions/at_2.ma".

(* CONSTRUCTORS FOR TERM ****************************************************)

definition term_node_0 (l): term ≝
           λp. l;𝐞 = p.

definition term_node_1 (l): term → term ≝
           λt,p. ∃∃q. q ϵ⬦ t & l;q = p.

definition term_node_2 (l1) (l2): term → term → term ≝
           λt1,t2,p.
           ∨∨ ∃∃q. q ϵ⬦ t1 & l1;q = p
            | ∃∃q. q ϵ⬦ t2 & l2;q = p.

interpretation
  "outer variable reference by depth (term)"
  'Hash n = (term_node_0 (label_node_d n)).

interpretation
  "inner variable reference by depth (term)"
  'Phi n t = (term_node_1 (label_node_d n) t).

interpretation
  "name-free functional abstraction (term)"
  'Lamda t = (term_node_1 label_edge_l t).

interpretation
  "application (term)"
  'At u t = (term_node_2 label_edge_s label_edge_a u t).

(* Basic Inversions *********************************************************)

lemma term_in_ini_inv_lcons_oref:
      ∀p,l,n. l;p ϵ▵ #n →
      ∧∧ 𝗱❨n❩ = l & 𝐞 = p.
#p #l #n * #q
<list_append_lcons_sn #H destruct -H
elim (eq_inv_list_empty_append … e0) -e0 #H1 #_
/2 width=1 by conj/
qed-.

lemma term_in_ini_inv_lcons_iref:
      ∀t,p,l,n. l;p ϵ▵ 𝛗n.t →
      ∧∧ 𝗱❨n❩ = l & p ϵ▵ t.
#t #p #l #n * #q
<list_append_lcons_sn * #r #Hr #H1 destruct
/3 width=2 by ex_intro, conj/
qed-.
