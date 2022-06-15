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

(* Constructions with subset_equivalence ************************************)

lemma subset_inclusion_fsubst_bi (t1) (t2) (u1) (u2) (p):
      t1 ⊆ t2 → u1 ⊆ u2 → t1[⋔p←u1] ⊆ t2[⋔p←u2].
#t1 #t2 #u1 #u2 #p #Ht #Hu #q * *
[ #r #Hr #H0 destruct
  /4 width=3 by ex2_intro, or_introl/
| /4 width=2 by or_intror, conj/
]
qed.

lemma fsubst_eq_repl (t1) (t2) (u1) (u2) (p1) (p2):
      t1 ⇔ t2 → p1 = p2 → u1 ⇔ u2 → t1[⋔p1←u1] ⇔ t2[⋔p2←u2].
#t1 #t2 #u1 #u2 #p1 #p2 * #H1t #H2t #Hp * #H1u #H2u
/3 width=5 by conj, subset_inclusion_fsubst_bi/
qed.
