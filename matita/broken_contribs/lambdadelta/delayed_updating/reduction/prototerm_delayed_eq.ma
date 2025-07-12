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

include "delayed_updating/syntax/prototerm_constructors_eq.ma".
include "delayed_updating/substitution/fsubst_eq.ma".
include "delayed_updating/reduction/prototerm_delayed.ma".

(* BALANCED REDUCTION DELAYED SUBREDUCT *************************************)

(* Constructions with subset_le *********************************************)

lemma term_le_root_bi_brd_slice (t) (p) (b) (q) (n):
      ▵𝐃❨t,p,b,q,n❩ ⊆ ▵↑(p●𝗔◗⓪b●𝗟◗q).
/3 width=3 by pt_append_slice, term_root_le_repl/
qed.

(* Constructions with subset_eq *********************************************)

lemma brd_grafted_eq_repl_fwd (t1) (t2) (p) (b) (q) (n):
      (⋔[p◖𝗦]t1 ⇔ ⋔[p◖𝗦]t2) → 𝐃❨t1,p,b,q,n❩ ⇔ 𝐃❨t2,p,b,q,n❩.
#t1 #t2 #p #b #q #n
/3 width=1 by pt_append_eq_repl_bi, iref_eq_repl_bi/
qed.

lemma brd_eq_repl_fwd (t1) (t2) (p) (b) (q) (n):
      t1 ⇔ t2 → 𝐃❨t1,p,b,q,n❩ ⇔ 𝐃❨t2,p,b,q,n❩.
#t1 #t2 #p #b #q #n
/3 width=1 by brd_grafted_eq_repl_fwd, term_grafted_eq_repl/
qed.

lemma brd_fsubst_grafted_eq_repl_fwd (t1) (t2) (u) (v) (p) (b) (q) (n):
      ⬕[⋔[p◖𝗦]u←⋔[p◖𝗦]v]⋔[p◖𝗦]t1 ⇔ ⋔[p◖𝗦]t2 →
      ⬕[𝐃❨u,p,b,q,n❩←𝐃❨v,p,b,q,n❩]𝐃❨t1,p,b,q,n❩ ⇔ 𝐃❨t2,p,b,q,n❩.
#t1 #t2 #u #v #p #b #q #n #H0
@(subset_eq_canc_sn … (fsubst_append …))
@pt_append_eq_repl_bi [ // ]
@(subset_eq_canc_sn … (fsubst_append …))
/2 width=1 by iref_eq_repl_bi/
qed.


lemma brd_fsubst_false_eq_repl_fwd (t1) (t2) (u) (v) (p) (b) (q) (n):
      (p◖𝗦) ⧸ϵ ▵u → (p◖𝗦) ⧸ϵ ▵v → ⬕[u←v]t1 ⇔ t2 →
      (𝐃❨t1,p,b,q,n❩ ⇔ 𝐃❨t2,p,b,q,n❩).
#t1 #t2 #u #v #p #b #q #n #H1np #H2np #H0
lapply (term_grafted_eq_repl … (p◖𝗦) H0) -H0 #H0
lapply (subset_eq_trans … (grafted_fsubst_false … H1np H2np) … H0) -H0 -H1np -H2np #H0
/2 width=1 by brd_grafted_eq_repl_fwd/
qed.

lemma brd_fsubst_true_eq_repl_fwd (t1) (t2) (u) (v) (p) (b) (q) (n):
      (⋔[p◖𝗦]t1) ≬ ⋔[p◖𝗦]u → ⬕[u←v]t1 ⇔ t2 →
      ⬕[𝐃❨u,p,b,q,n❩←𝐃❨v,p,b,q,n❩]𝐃❨t1,p,b,q,n❩ ⇔ 𝐃❨t2,p,b,q,n❩.
#t1 #t2 #u #v #p #b #q #n #Htu #H0
lapply (term_grafted_eq_repl … (p◖𝗦) H0) -H0 #H0
lapply (subset_eq_trans … (grafted_fsubst_true … Htu) … H0) -H0 -Htu #H0
/2 width=1 by brd_fsubst_grafted_eq_repl_fwd/
qed.
