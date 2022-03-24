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

include "delayed_updating/unwind1/unwind_prototerm_eq.ma".
include "delayed_updating/syntax/prototerm_constructors.ma".

(* UNWIND FOR PROTOTERM *****************************************************)

lemma unwind_iref_sn (f) (t:prototerm) (n:pnat):
      ▼[𝐮❨f@❨n❩❩]t ⊆ ▼[f](𝛗n.t).
#f #t #n #p * #q #Hq #H0 destruct
@(ex2_intro … (𝗱n◗𝗺◗q))
/2 width=1 by in_comp_iref/
qed-.

lemma unwind_iref_dx (f) (t) (n:pnat):
      ▼[f](𝛗n.t) ⊆ ▼[𝐮❨f@❨n❩❩]t.
#f #t #n #p * #q #Hq #H0 destruct
elim (in_comp_inv_iref … Hq) -Hq #p #Hp #Ht destruct
/2 width=1 by in_comp_unwind_bi/
qed-.

lemma unwind_iref (f) (t) (n:pnat):
      ▼[𝐮❨f@❨n❩❩]t ⇔ ▼[f](𝛗n.t).
/3 width=1 by conj, unwind_iref_sn, unwind_iref_dx/
qed.
