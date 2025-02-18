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
include "delayed_updating/reduction/prototerm_immediate.ma".

(* BALANCED REDUCTION IMMEDIATE SUBREDUCT ***********************************)

(* Constructions with subset_eq *********************************************)

lemma bri_eq_repl_fwd (t1) (t2) (p) (b) (q) (n):
      t1 ⇔ t2 → 𝐈❨t1,p,b,q,n❩ ⇔ 𝐈❨t2,p,b,q,n❩.
#t1 #t2 #p #b #q #n
/4 width=1 by pt_append_eq_repl_bi, lift_term_eq_repl_dx, term_grafted_eq_repl/
qed.
