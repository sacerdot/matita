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
include "ground/lib/subset_equivalence.ma".

(* EQUIVALENCE FOR PROTOTERM ************************************************)

(* Constructions with prototerm_root ****************************************)

lemma prototerm_root_incl_repl:
      ∀t1,t2. t1 ⊆ t2 → ▵t1 ⊆ ▵t2.
#t1 #t2 #Ht #p * #q #Hq
/3 width=2 by ex_intro/
qed.

lemma prototerm_root_eq_repl:
      ∀t1,t2. t1 ⇔ t2 → ▵t1 ⇔ ▵t2.
#t1 #t2 * #H1 #H2
/3 width=3 by conj, prototerm_root_incl_repl/
qed.
