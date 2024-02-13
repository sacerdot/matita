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

include "delayed_updating/syntax/prototerm_eq.ma".
include "delayed_updating/syntax/preterm.ma".

(* PRETERM ******************************************************************)

(* Constructions with subset_eq *********************************************)

lemma term_eq_repl_back (t1) (t2):
      t2 ϵ 𝐓 → t1 ⇔ t2 → t1 ϵ 𝐓.
#t1 #t2 * #H1 #H2 #H3 #H4 #Ht
@mk_preterm_posts
[ /3 width=3 by subset_in_eq_repl_fwd/
| /3 width=5 by term_root_eq_repl_fwd/
| #p #Hp (**) (* full auto too slow *)
  @(term_root_eq_repl_back … Ht)
  /3 width=3 by term_root_eq_repl_fwd/
| /3 width=4 by subset_in_eq_repl_fwd/
]
qed-.

lemma term_eq_repl_fwd (t1) (t2):
      t1 ϵ 𝐓 → t1 ⇔ t2 → t2 ϵ 𝐓.
#t1 #t2 * #H1 #H2 #H3 #H4 #Ht
@mk_preterm_posts
[ /3 width=3 by subset_in_eq_repl_back/
| /3 width=5 by term_root_eq_repl_back/
| #p #Hp (**) (* full auto too slow *)
  @(term_root_eq_repl_fwd … Ht)
  /3 width=3 by term_root_eq_repl_back/
| /3 width=4 by subset_in_eq_repl_back/
]
qed-.
