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

include "delayed_updating/reduction/prototerm_reducible_le.ma".
include "delayed_updating/reduction/prototerm_reducibles.ma".

(* SUBSET OF REDEX POINTERS *************************************************)

(* Constructions with subset_le *********************************************)

lemma prc_mk_le (t) (p) (b) (q) (n):
      (𝐑❨t,p,b,q,n❩) ⊆ 𝐑❨t❩.
/2 width=5 by ex1_4_intro/
qed.

lemma prc_le_repl (t1) (t2):
      t1 ⊆ t2 → 𝐑❨t1❩ ⊆ 𝐑❨t2❩.
#t1 #t2 #Ht12 #r
* #p #b #q #n #Hr
/3 width=7 by prc_mk_le, xprc_le_repl/
qed.
