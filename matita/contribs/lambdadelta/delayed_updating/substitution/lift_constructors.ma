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
include "delayed_updating/syntax/prototerm_constructors.ma".

(* LIFT FOR PROTOTERM *******************************************************)

lemma lift_iref_after_sn (f) (t:prototerm) (n:pnat):
      ↑[f∘𝐮❨n❩]t ⊆ ↑[f](𝛗n.t).
#f #t #n #p * #q #Hq #H0 destruct
@(ex2_intro … (𝗱n◗𝗺◗q))
/2 width=1 by in_comp_iref/
qed-.

lemma lift_iref_after_dx (f) (t) (n:pnat):
      ↑[f](𝛗n.t) ⊆ ↑[f∘𝐮❨n❩]t.
#f #t #n #p * #q #Hq #H0 destruct
elim (in_comp_inv_iref … Hq) -Hq #p #Hp #Ht destruct
/2 width=1 by in_comp_lift_bi/
qed-.

lemma lift_iref_after (f) (t) (n:pnat):
      ↑[f∘𝐮❨n❩]t ⇔ ↑[f](𝛗n.t).
/3 width=1 by conj, lift_iref_after_sn, lift_iref_after_dx/
qed.

lemma lift_iref (f) (t) (n:pnat):
      ↑[f]↑[𝐮❨n❩]t ⇔ ↑[f](𝛗n.t).
/3 width=3 by lift_term_after, subset_eq_trans/
qed.