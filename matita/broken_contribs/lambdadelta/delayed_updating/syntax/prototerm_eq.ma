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

include "delayed_updating/syntax/prototerm.ma".
include "ground/lib/subset_eq.ma".

(* EQUIVALENCE FOR PROTOTERM ************************************************)

(* Constructions with prototerm_grafted *************************************)

lemma term_grafted_empty_dx (t):
      t ⇔ ⋔[𝐞]t.
/2 width=1 by conj/
qed.

lemma term_grafted_le_repl (t1) (t2) (p):
      t1 ⊆ t2 → ⋔[p]t1 ⊆ ⋔[p]t2.
#t1 #t2 #p #Ht #q #Hq
/2 width=1 by/
qed.

lemma term_grafted_eq_repl (t1) (t2) (p):
      t1 ⇔ t2 → ⋔[p]t1 ⇔ ⋔[p]t2.
#t1 #t2 #p * #H1t #H2t
/3 width=1 by conj, term_grafted_le_repl/
qed.

(* Constructions with term_root *********************************************)

lemma term_root_le_repl:
      ∀t1,t2. t1 ⊆ t2 → ▵t1 ⊆ ▵t2.
#t1 #t2 #Ht #p * #q #Hq
/3 width=2 by ex_intro/
qed.

lemma term_root_eq_repl:
      ∀t1,t2. t1 ⇔ t2 → ▵t1 ⇔ ▵t2.
#t1 #t2 * #H1 #H2
/3 width=3 by conj, term_root_le_repl/
qed.

lemma term_root_eq_repl_back (t1) (t2) (p):
      p ϵ ▵t2 → t1 ⇔ t2 → p ϵ ▵t1.
#t1 #t2 #p * #q #Hq #Ht
/3 width=4 by term_in_root, subset_in_eq_repl_back/
qed-.

lemma term_root_eq_repl_fwd (t1) (t2) (p):
      p ϵ ▵t1 → t1 ⇔ t2 → p ϵ ▵t2.
#t1 #t2 #p * #q #Hq #Ht
/3 width=4 by term_in_root, subset_in_eq_repl_fwd/
qed-.

(* Constructions with pt_append *********************************************)

lemma pt_append_le_repl (t1) (t2) (p) :
      t1 ⊆ t2 → p●t1 ⊆ p●t2.
#t1 #t2 #p #Ht #r * #q #Hq #H0 destruct
/3 width=1 by pt_append_in/
qed.

lemma pt_append_eq_repl_bi (t1) (t2) (p1) (p2):
      p1 = p2 → t1 ⇔ t2 → p1●t1 ⇔ p2●t2.
#t1 #t2 #p1 #p2 #p * #H1 #H2
/3 width=3 by conj, pt_append_le_repl/
qed.

lemma pt_append_assoc_sn (p) (q) (t:𝕋):
      p●(q●t) ⊆ (p●q)●t.
#p #q #t #r * #s1 * #s2 #Hs2 #H2 #H1 destruct
/3 width=1 by pt_append_in/
qed.

lemma pt_append_assoc_dx (p) (q) (t:𝕋):
      (p●q)●t ⊆ p●(q●t).
#p #q #t #r * #s #Hs #H0 destruct
/3 width=1 by pt_append_in/
qed.

lemma pt_append_assoc (p) (q) (t:𝕋):
      p●(q●t) ⇔ (p●q)●t.
#p #q #t
/3 width=1 by conj, pt_append_assoc_sn, pt_append_assoc_dx/
qed.

(* Constructions with term_slice ********************************************)

lemma term_slice_append (p) (q):
      p●↑q ⇔ ↑(p●q).
#p #q @conj #r * #s
[ #Hs #H0 destruct
  cases Hs -Hs #r #H0 destruct //
| #H0 destruct /2 width=1 by pt_append_in/
]
qed.

lemma append_in_comp_slice_bi (p) (q) (s):
      s ϵ ↑q → p●s ϵ ↑(p●q).
/3 width=4 by subset_in_eq_repl_fwd, pt_append_in/
qed.

(* Inversions with term_slice ***********************************************)

lemma append_in_comp_slice_inv_bi (p) (q) (s):
      p●s ϵ ↑(p●q) → s ϵ ↑q.
/3 width=4 by subset_in_eq_repl_back, append_in_comp_inv_bi/
qed-.
