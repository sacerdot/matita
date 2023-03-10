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

include "delayed_updating/syntax/path.ma".
include "delayed_updating/notation/functions/class_p_0.ma".
include "ground/lib/subset.ma".
include "ground/xoa/ex_1_2.ma".

(* PROPER CONDITION FOR PATH ************************************************)

definition ppc: predicate path ā
           Ī»p. š = p ā ā„
.

interpretation
  "proper condition (path)"
  'ClassP = (ppc).

(* Basic constructions ******************************************************)

lemma ppc_rcons (p) (l):
      pāl Ļµ š.
#p #l #H0 destruct
qed.

lemma ppc_lcons (p) (l):
      lāp Ļµ š.
#p #l #H0
elim (eq_inv_list_empty_rcons ??? H0)
qed.

(* Basic inversions ********************************************************)

lemma ppc_inv_empty:
      (š) Ļµ š ā ā„.
#H0 @H0 -H0 //
qed-.

lemma ppc_inv_rcons (p):
      p Ļµ š ā āāq,l. qāl = p.
*
[ #H0 elim (ppc_inv_empty ā¦ H0)
| #l #q #_ /2 width=3 by ex1_2_intro/
]
qed-.

lemma ppc_inv_lcons (p):
      p Ļµ š ā āāq,l. lāq = p.
#p @(list_ind_rcons ā¦ p) -p
[ #H0 elim (ppc_inv_empty ā¦ H0)
| #q #l #_ #_ /2 width=3 by ex1_2_intro/
]
qed-.
