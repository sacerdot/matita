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

lemma term_grafted_complete (t) (p):
      t ϵ 𝐓 → p ϵ t → ❴𝐞❵ ⇔ ⋔[p]t.
#t #p #Ht #Hp @conj #q #Hq
[ >(subset_in_inv_single ??? Hq) -q //
| lapply (term_complete_post … Ht … Hq Hp ?) -t [ // ] #H0
  <(eq_inv_list_append_dx_dx_refl … (sym_eq … H0)) -p -q //
]
qed.

lemma term_slice_complete (t) (p):
      t ϵ 𝐓 → p ϵ t → ❴p❵ ⇔ t∩↑p.
#t #p #Ht #Hp @conj #x
[ #H0
  >(subset_in_inv_single ??? H0) -x
  /2 width=1 by subset_and_in/
| * #Hx #H0
  elim (term_in_slice_inv_gen … H0) -H0 #y #H0 destruct
  <(term_complete_append … Ht Hp Hx) -y //
]
qed.

lemma term_eq_repl_back (t1) (t2):
      t2 ϵ 𝐓 → t1 ⇔ t2 → t1 ϵ 𝐓.
#t1 #t2 * #H1 #H2 #H3 #H4 #H5 #Ht
@mk_preterm_posts
[ /3 width=3 by subset_in_eq_repl_fwd/
| /3 width=5 by term_root_eq_repl_fwd/
| /3 width=5 by term_root_eq_repl_fwd/
| #p #Hp (**) (* full auto too slow *)
  @(term_root_eq_repl_back … Ht)
  /3 width=3 by term_root_eq_repl_fwd/
| /3 width=4 by subset_in_eq_repl_fwd/
]
qed-.

lemma term_eq_repl_fwd (t1) (t2):
      t1 ϵ 𝐓 → t1 ⇔ t2 → t2 ϵ 𝐓.
#t1 #t2 * #H1 #H2 #H3 #H4 #H5 #Ht
@mk_preterm_posts
[ /3 width=3 by subset_in_eq_repl_back/
| /3 width=5 by term_root_eq_repl_back/
| /3 width=5 by term_root_eq_repl_back/
| #p #Hp (**) (* full auto too slow *)
  @(term_root_eq_repl_fwd … Ht)
  /3 width=3 by term_root_eq_repl_back/
| /3 width=4 by subset_in_eq_repl_back/
]
qed-.
