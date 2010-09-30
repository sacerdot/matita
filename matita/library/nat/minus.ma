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


include "nat/le_arith.ma".
include "nat/compare.ma".

let rec minus n m \def 
 match n with 
 [ O \Rightarrow O
 | (S p) \Rightarrow 
	match m with
	[O \Rightarrow (S p)
        | (S q) \Rightarrow minus p q ]].
        
interpretation "natural minus" 'minus x y = (minus x y).

theorem minus_S_S: ∀n,m:nat.S n - S m = n -m.
intros;reflexivity.
qed.

theorem minus_n_O: \forall n:nat.n=n-O.
intros.elim n.simplify.reflexivity.
simplify.reflexivity.
qed.

theorem minus_n_n: \forall n:nat.O=n-n.
intros.elim n.simplify.
reflexivity.
simplify.apply H.
qed.

theorem minus_Sn_n: \forall n:nat. S O = (S n)-n.
intro.elim n.
simplify.reflexivity.
elim H.reflexivity.
qed.

theorem minus_Sn_m: \forall n,m:nat. m \leq n \to (S n)-m = S (n-m).
intros 2.
apply (nat_elim2
(\lambda n,m.m \leq n \to (S n)-m = S (n-m))).
intros.apply (le_n_O_elim n1 H).
simplify.reflexivity.
intros.simplify.reflexivity.
intros.rewrite < H.reflexivity.
apply le_S_S_to_le. assumption.
qed.

theorem eq_minus_S_pred: \forall n,m. n - (S m) = pred(n -m).
apply nat_elim2
  [intro.reflexivity
  |intro.simplify.autobatch
  |intros.simplify.assumption
  ]
qed.

theorem plus_minus:
\forall n,m,p:nat. m \leq n \to (n-m)+p = (n+p)-m.
intros 2.
apply (nat_elim2
(\lambda n,m.\forall p:nat.m \leq n \to (n-m)+p = (n+p)-m)).
intros.apply (le_n_O_elim ? H).
simplify.rewrite < minus_n_O.reflexivity.
intros.simplify.reflexivity.
intros.simplify.apply H.apply le_S_S_to_le.assumption.
qed.

theorem minus_plus_m_m: \forall n,m:nat.n = (n+m)-m.
intros 2 .elim m in n ⊢ %.
rewrite < minus_n_O.apply plus_n_O.
elim n1.simplify. apply minus_n_n.
autobatch by H.
(* rewrite < plus_n_Sm.
change with (S n2 = (S n2 + n)-n).
apply H. *)
qed.

theorem plus_minus_m_m: \forall n,m:nat.
m \leq n \to n = (n-m)+m.
intros 2.
apply (nat_elim2 (\lambda n,m.m \leq n \to n = (n-m)+m)).
intros.apply (le_n_O_elim n1 H).
reflexivity.
intros.simplify.rewrite < plus_n_O.reflexivity.
intros. 
rewrite < sym_plus.simplify. apply eq_f.
rewrite < sym_plus.apply H.
apply le_S_S_to_le.assumption.
qed.

theorem le_plus_minus_m_m: \forall n,m:nat. n \le (n-m)+m.
intro.elim n;
  [apply le_O_n
  |cases m; simplify[autobatch|autobatch by H, le_S_S]
  ]
qed.

theorem minus_to_plus :\forall n,m,p:nat.m \leq n \to n-m = p \to 
n = m+p.
intros.apply (trans_eq ? ? ((n-m)+m)).
apply plus_minus_m_m.
apply H.elim H1.
apply sym_plus.
qed.

theorem plus_to_minus :\forall n,m,p:nat.
n = m+p \to n-m = p.
intros.
(* autobatch by transitive_eq, eq_f2, H. *)
autobatch depth=4 by inj_plus_r, symmetric_eq, minus_to_plus, le_plus_n_r.
(* 
rewrite < H.
rewrite < sym_plus.
symmetry.
apply plus_minus_m_m.rewrite > H.
rewrite > sym_plus.
apply le_plus_n.*)
qed.

theorem minus_pred_pred : \forall n,m:nat. lt O n \to lt O m \to 
eq nat (minus (pred n) (pred m)) (minus n m).
intros.
apply (lt_O_n_elim n H).intro.
apply (lt_O_n_elim m H1).intro.
simplify.reflexivity.
qed.

theorem eq_minus_n_m_O: \forall n,m:nat.
n \leq m \to n-m = O.
intros 2.
apply (nat_elim2 (\lambda n,m.n \leq m \to n-m = O)).
intros.simplify.reflexivity.
intros.apply False_ind.
apply not_le_Sn_O;
[2: apply H | skip].
intros.
simplify.apply H.apply le_S_S_to_le. apply H1.
qed.

theorem le_SO_minus: \forall n,m:nat.S n \leq m \to S O \leq m-n.
intros.elim H.elim (minus_Sn_n n).apply le_n.
rewrite > minus_Sn_m.
apply le_S.assumption.
apply lt_to_le.assumption.
qed.

theorem minus_le_S_minus_S: \forall n,m:nat. m-n \leq S (m-(S n)).
intros.
apply (nat_elim2 (\lambda n,m.m-n \leq S (m-(S n)))).
intro.elim n1.simplify.apply le_n_Sn.
simplify.rewrite < minus_n_O.apply le_n.
intros.simplify.apply le_n_Sn.
intros.simplify.apply H.
qed.

theorem lt_minus_S_n_to_le_minus_n : \forall n,m,p:nat. m-(S n) < p \to m-n \leq p. 
intros 3.intro.
(* autobatch *)
(* end auto($Revision$) proof: TIME=1.33 SIZE=100 DEPTH=100 *)
apply (trans_le (m-n) (S (m-(S n))) p).
apply minus_le_S_minus_S.
assumption.
qed.

theorem le_minus_m: \forall n,m:nat. n-m \leq n.
intros.apply (nat_elim2 (\lambda m,n. n-m \leq n)).
intros.rewrite < minus_n_O.apply le_n.
intros.simplify.apply le_n.
intros.simplify.apply le_S.assumption.
qed.

theorem lt_minus_m: \forall n,m:nat. O < n \to O < m \to n-m \lt n.
intros.apply (lt_O_n_elim n H).intro.
apply (lt_O_n_elim m H1).intro.
simplify.unfold lt.apply le_S_S.apply le_minus_m.
qed.

theorem minus_le_O_to_le: \forall n,m:nat. n-m \leq O \to n \leq m.
intros 2.
apply (nat_elim2 (\lambda n,m:nat.n-m \leq O \to n \leq m)).
intros.apply le_O_n.
simplify.intros. assumption.
simplify.intros.apply le_S_S.apply H.assumption.
qed.

(* galois *)
theorem monotonic_le_minus_r: 
\forall p,q,n:nat. q \leq p \to n-p \le n-q.
intros 2.apply (nat_elim2 ???? p q); intros;
  [apply (le_n_O_elim n H).apply le_n.
  |applyS le_minus_m.
  |elim n1;intros;[apply le_n|simplify.apply H.apply le_S_S_to_le.assumption]
  ]
qed.

theorem monotonic_le_minus_l: 
∀p,q,n:nat. q \leq p \to q-n \le p-n.
intros 2.apply (nat_elim2 ???? p q); intros;
  [apply (le_n_O_elim n H).apply le_n.
  |apply le_O_n.
  |cases n1;[apply H1|simplify. apply H.apply le_S_S_to_le.assumption]
  ]
qed.

theorem le_minus_to_plus: \forall n,m,p. (le (n-m) p) \to (le n (p+m)).
intros.
(* autobatch by transitive_le, le_plus_minus_m_m, le_plus_l, H.*)
apply transitive_le
  [2:apply le_plus_minus_m_m.
  |3:apply le_plus_l.apply H.
  ]
  skip.
qed.

theorem le_plus_to_minus: \forall n,m,p. (le n (p+m)) \to (le (n-m) p).
intros.
autobatch by (monotonic_le_minus_l (p+m) n m), H.
(*
intros 2.apply (nat_elim2 (\lambda n,m.\forall p.(le n (p+m)) \to (le (n-m) p))).
intros.simplify.apply le_O_n.
intros 2.rewrite < plus_n_O.intro.simplify.assumption.
intros.simplify.apply H.
apply le_S_S_to_le.rewrite > plus_n_Sm.assumption. *)
qed.

(* the converse of le_plus_to_minus does not hold *)
theorem le_plus_to_minus_r: \forall n,m,p. (le (n+m) p) \to (le n (p-m)).
intros.
autobatch by trans_le, le_plus_to_le, H, le_plus_minus_m_m.
(*
apply (nat_elim2 (\lambda m,p.(le (n+m) p) \to (le n (p-m)))).
intro.rewrite < plus_n_O.rewrite < minus_n_O.intro.assumption.
intro.intro.cut (n=O).rewrite > Hcut.apply le_O_n.
apply sym_eq. apply le_n_O_to_eq.
apply (trans_le ? (n+(S n1))).
rewrite < sym_plus.
apply le_plus_n.assumption.
intros.simplify.
apply H.apply le_S_S_to_le.
rewrite > plus_n_Sm.assumption. *)
qed.

(* minus and lt - to be completed *)
theorem lt_minus_l: \forall m,l,n:nat. 
  l < m \to m \le n \to n - m < n - l.
apply nat_elim2
  [intros.apply False_ind.apply (not_le_Sn_O ? H)
  |intros.autobatch.
   (* rewrite < minus_n_O.
    change in H1 with (n<n1);
    apply lt_minus_m; autobatch depth=2; *)
  |intros.
   generalize in match H2.
   apply (nat_case n1)
    [intros.apply False_ind.apply (not_le_Sn_O ? H3)
    |intros.simplify.
     apply H
      [
       apply lt_S_S_to_lt.
       assumption
      |apply le_S_S_to_le.assumption
      ]
    ]
  ]
qed.

theorem lt_minus_r: \forall n,m,l:nat. 
  n \le l \to l < m \to l -n < m -n.
  unfold lt.
intro.elim n
  [applyS H1
  |(*
   letin x ≝ (lt_pred (l-n1) (m-n1)).
   clearbody x.
   unfold lt in x.
   autobatch depth=4 width=5 size=10 by 
    x, H, H1, H2, trans_le, le_n_Sn, le_n.
  ]*)
  rewrite > eq_minus_S_pred.
   rewrite > eq_minus_S_pred.
   apply lt_pred
    [unfold lt.apply le_plus_to_minus_r.applyS H1
    |apply H[autobatch depth=2|assumption]
    ]
  ]
qed.

lemma lt_to_lt_O_minus : \forall m,n.
  n < m \to O < m - n.
intros.  
unfold. apply le_plus_to_minus_r. unfold in H.
cut ((S n ≤ m) = (1 + n ≤ m)) as applyS;
  [ rewrite < applyS; assumption;
  | demodulate; reflexivity. ]
(*
rewrite > sym_plus. 
rewrite < plus_n_Sm. 
rewrite < plus_n_O. 
assumption.
*)
qed.  

theorem lt_minus_to_plus: \forall n,m,p. (lt n (p-m)) \to (lt (n+m) p).
intros 3.apply (nat_elim2 (\lambda m,p.(lt n (p-m)) \to (lt (n+m) p))).
intro.rewrite < plus_n_O.rewrite < minus_n_O.intro.assumption.
simplify.intros.apply False_ind.apply (not_le_Sn_O n H).
simplify.intros.unfold lt.
apply le_S_S.
rewrite < plus_n_Sm.
apply H.apply H1.
qed.

theorem lt_O_minus_to_lt: \forall a,b:nat.
O \lt b-a \to a \lt b.
intros. applyS (lt_minus_to_plus O  a b). assumption;
(*
rewrite > (plus_n_O a).
rewrite > (sym_plus a O).
apply (lt_minus_to_plus O  a b).
assumption.
*)
qed.

theorem lt_minus_to_lt_plus:
\forall n,m,p. n - m < p \to n < m + p.
intros 2.
apply (nat_elim2 ? ? ? ? n m)
  [simplify.intros.
   lapply depth=0 le_n; autobatch;
  |intros 2.rewrite < minus_n_O.
   intro.assumption
  |intros.
   simplify.
   cut (n1 < m1+p)
    [autobatch
    |apply H.
     apply H1
    ]
  ]
qed.

theorem lt_plus_to_lt_minus:
\forall n,m,p. m \le n \to n < m + p \to n - m < p.
intros 2.
apply (nat_elim2 ? ? ? ? n m)
  [simplify.intros 3.
   apply (le_n_O_elim ? H).
   simplify.intros.assumption
  |simplify.intros.assumption.
  |intros.
   simplify.
   apply H
    [apply le_S_S_to_le.assumption
    |apply le_S_S_to_le.apply H2
    ]
  ]
qed. 

theorem minus_m_minus_mn: \forall n,m. n\le m \to n=m-(m-n).
intros.
apply sym_eq.
apply plus_to_minus.
autobatch;
qed.

theorem distributive_times_minus: distributive nat times minus.
unfold distributive.
intros.
apply ((leb_elim z y)).
  intro.cut (x*(y-z)+x*z = (x*y-x*z)+x*z).
    apply (inj_plus_l (x*z)).assumption.
    apply (trans_eq nat ? (x*y)).
      rewrite < distr_times_plus.rewrite < (plus_minus_m_m ? ? H).reflexivity.
      rewrite < plus_minus_m_m.
        reflexivity.
        apply le_times_r.assumption.
  intro.rewrite > eq_minus_n_m_O.
    rewrite > (eq_minus_n_m_O (x*y)).
      rewrite < sym_times.simplify.reflexivity.
        apply le_times_r.apply lt_to_le.apply not_le_to_lt.assumption.
        apply lt_to_le.apply not_le_to_lt.assumption.
qed.

theorem distr_times_minus: \forall n,m,p:nat. n*(m-p) = n*m-n*p
\def distributive_times_minus.

theorem eq_minus_plus_plus_minus: \forall n,m,p:nat. p \le m \to (n+m)-p = n+(m-p).
intros.
apply plus_to_minus.
lapply (plus_minus_m_m ?? H); demodulate. reflexivity.
(*
rewrite > sym_plus in \vdash (? ? ? %).
rewrite > assoc_plus.
rewrite < plus_minus_m_m.
reflexivity.assumption.
*)
qed.

theorem eq_minus_minus_minus_plus: \forall n,m,p:nat. (n-m)-p = n-(m+p).
intros.
cut (m+p \le n \or m+p \nleq n).
  elim Hcut.
    symmetry.apply plus_to_minus.
    rewrite > assoc_plus.rewrite > (sym_plus p).rewrite < plus_minus_m_m.
      rewrite > sym_plus.rewrite < plus_minus_m_m.
        reflexivity.
        apply (trans_le ? (m+p)).
          rewrite < sym_plus.apply le_plus_n.
          assumption.
      apply le_plus_to_minus_r.rewrite > sym_plus.assumption.   
    rewrite > (eq_minus_n_m_O n (m+p)).
      rewrite > (eq_minus_n_m_O (n-m) p).
        reflexivity.
      apply le_plus_to_minus.apply lt_to_le. rewrite < sym_plus.
       apply not_le_to_lt. assumption.
    apply lt_to_le.apply not_le_to_lt.assumption.          
  apply (decidable_le (m+p) n).
qed.

theorem eq_plus_minus_minus_minus: \forall n,m,p:nat. p \le m \to m \le n \to
p+(n-m) = n-(m-p).
intros. 
apply sym_eq.
apply plus_to_minus.
rewrite < assoc_plus.
rewrite < plus_minus_m_m.
rewrite < sym_plus.
rewrite < plus_minus_m_m.reflexivity.
assumption.assumption.
qed.
