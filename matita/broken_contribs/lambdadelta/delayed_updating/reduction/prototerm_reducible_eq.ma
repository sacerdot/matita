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

include "ground/subsets/subset_eq.ma".
include "delayed_updating/reduction/prototerm_reducible_le.ma".

(* EXPLICIT REDEX POINTER ***************************************************)

(* Constructions with subset_eq *********************************************)

lemma xprc_eq_repl (t1) (t2) (p) (b) (q) (n):
      t1 ⇔ t2 → 𝐑❨t1,p,b,q,n❩ ⇔ 𝐑❨t2,p,b,q,n❩.
#t1 #t2 #p #b #q #n * #Ht12 #Ht21
/3 width=3 by conj, xprc_le_repl/
qed.
