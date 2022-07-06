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

include "delayed_updating/syntax/prototerm_constructors.ma".
include "ground/lib/subset_ext_equivalence.ma".

(* CONSTRUCTORS FOR PROTOTERM ***********************************************)

(* Constructions with equivalence for prototerm *****************************)

lemma iref_eq_repl (t1) (t2) (k):
      t1 ⇔ t2 → 𝛕k.t1 ⇔ 𝛕k.t2.
/2 width=1 by subset_equivalence_ext_f1_bi/
qed.
