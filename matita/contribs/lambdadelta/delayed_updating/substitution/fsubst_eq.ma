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

include "delayed_updating/substitution/fsubst.ma".
include "delayed_updating/syntax/prototerm_eq.ma".

(* FOCALIZED SUBSTITUTION ***************************************************)

(* Constructions with subset_equivalence ************************************)

lemma fsubst_empty_rc (t) (u):
      u ā t[āšāu].
#t #u @conj #p
[ #Hp /3 width=3 by or_introl, ex2_intro/ ]
* *
[ #r #Hr #H0 destruct // ]
#H1p #H2p elim H2p -H2p //
qed.

lemma subset_inclusion_fsubst_bi (t1) (t2) (u1) (u2) (p):
      t1 ā t2 ā u1 ā u2 ā t1[āpāu1] ā t2[āpāu2].
#t1 #t2 #u1 #u2 #p #Ht #Hu #q * *
[ #r #Hr #H0 destruct
  /4 width=3 by ex2_intro, or_introl/
| /4 width=2 by or_intror, conj/
]
qed.

lemma fsubst_eq_repl (t1) (t2) (u1) (u2) (p1) (p2):
      t1 ā t2 ā p1 = p2 ā u1 ā u2 ā t1[āp1āu1] ā t2[āp2āu2].
#t1 #t2 #u1 #u2 #p1 #p2 * #H1t #H2t #Hp * #H1u #H2u
/3 width=5 by conj, subset_inclusion_fsubst_bi/
qed.
