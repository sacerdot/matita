(**************************************************************************)
(*       ___	                                                            *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||       A.Asperti, C.Sacerdoti Coen,                          *)
(*      ||A||       E.Tassi, S.Zacchiroli                                 *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU Lesser General Public License Version 2.1         *)
(*                                                                        *)
(**************************************************************************)

include "nat/nat.ma".

let rec plus n m \def 
 match n with 
 [ O \Rightarrow m
 | (S p) \Rightarrow S (plus p m) ].

interpretation "natural plus" 'plus x y = (plus x y).

theorem plus_n_O: \forall n:nat. n = n+O.
intros.elim n.
simplify.reflexivity.
simplify.apply eq_f.assumption.
qed.

theorem plus_n_Sm : \forall n,m:nat. S (n+m) = n+(S m).
intros.elim n.
simplify.reflexivity.
simplify.apply eq_f.assumption.
qed.

theorem plus_n_SO : \forall n:nat. S n = n+(S O).
intro.rewrite > plus_n_O.
apply plus_n_Sm.
qed.

theorem sym_plus: \forall n,m:nat. n+m = m+n.
intros.elim n.
simplify.apply plus_n_O.
simplify.rewrite > H.apply plus_n_Sm.
qed.

theorem associative_plus : associative nat plus.
unfold associative.intros.elim x.
simplify.reflexivity.
simplify.apply eq_f.assumption.
qed.

theorem assoc_plus : \forall n,m,p:nat. (n+m)+p = n+(m+p)
\def associative_plus.

theorem injective_plus_r: \forall n:nat.injective nat nat (\lambda m.n+m).
intro.simplify.intros 2.elim n.
exact H.
apply H.apply inj_S.apply H1.
qed.

theorem inj_plus_r: \forall p,n,m:nat. p+n = p+m \to n=m
\def injective_plus_r.

theorem injective_plus_l: \forall m:nat.injective nat nat (\lambda n.n+m).
intro.simplify.intros.
apply (injective_plus_r m).
rewrite < sym_plus.
rewrite < (sym_plus y).
assumption.
qed.

theorem inj_plus_l: \forall p,n,m:nat. n+p = m+p \to n=m
\def injective_plus_l.
