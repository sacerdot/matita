(**************************************************************************)
(*       ___	                                                          *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||       A.Asperti, C.Sacerdoti Coen,                          *)
(*      ||A||       E.Tassi, S.Zacchiroli                                 *)
(*      \   /                                                             *)
(*       \ /        Matita is distributed under the terms of the          *)
(*        v         GNU Lesser General Public License Version 2.1         *)
(*                                                                        *)
(**************************************************************************)

include "datatypes/constructors.ma".
include "nat/minus.ma".

let rec mod_aux p m n: nat \def
match (leb m n) with
[ true \Rightarrow m
| false \Rightarrow
  match p with
  [O \Rightarrow m
  |(S q) \Rightarrow mod_aux q (m-(S n)) n]].

definition mod : nat \to nat \to nat \def
\lambda n,m.
match m with 
[O \Rightarrow n
| (S p) \Rightarrow mod_aux n n p]. 

interpretation "natural remainder" 'module x y = (mod x y).

let rec div_aux p m n : nat \def
match (leb m n) with
[ true \Rightarrow O
| false \Rightarrow
  match p with
  [O \Rightarrow O
  |(S q) \Rightarrow S (div_aux q (m-(S n)) n)]].

definition div : nat \to nat \to nat \def
\lambda n,m.
match m with 
[O \Rightarrow S n
| (S p) \Rightarrow div_aux n n p]. 

interpretation "natural divide" 'divide x y = (div x y).

theorem le_mod_aux_m_m: 
\forall p,n,m. n \leq p \to (mod_aux p n m) \leq m.
intro.elim p.
apply (le_n_O_elim n H (\lambda n.(mod_aux O n m) \leq m)).
simplify.apply le_O_n.
simplify.
apply (leb_elim n1 m).
simplify.intro.assumption.
simplify.intro.apply H.
cut (n1 \leq (S n) \to n1-(S m) \leq n).
apply Hcut.assumption.
elim n1.
simplify.apply le_O_n.
simplify.apply (trans_le ? n2 n).
apply le_minus_m.apply le_S_S_to_le.assumption.
qed.

theorem lt_mod_m_m: \forall n,m. O < m \to (n \mod m) < m.
intros 2.elim m.apply False_ind.
apply (not_le_Sn_O O H).
simplify.unfold lt.apply le_S_S.apply le_mod_aux_m_m.
apply le_n.
qed.

theorem div_aux_mod_aux: \forall p,n,m:nat. 
(n=(div_aux p n m)*(S m) + (mod_aux p n m)).
intro.elim p.
simplify.elim (leb n m).
simplify.apply refl_eq.
simplify.apply refl_eq.
simplify.
apply (leb_elim n1 m).
simplify.intro.apply refl_eq.
simplify.intro.
rewrite > assoc_plus. 
elim (H (n1-(S m)) m).
change with (n1=(S m)+(n1-(S m))).
rewrite < sym_plus.
apply plus_minus_m_m.
change with (m < n1).
apply not_le_to_lt.exact H1.
qed.

theorem div_mod: \forall n,m:nat. O < m \to n=(n / m)*m+(n \mod m).
intros 2.elim m.elim (not_le_Sn_O O H).
simplify.
apply div_aux_mod_aux.
qed.

theorem eq_times_div_minus_mod:
\forall a,b:nat. O \lt b \to
(a /b)*b = a - (a \mod b).
intros.
rewrite > (div_mod a b) in \vdash (? ? ? (? % ?))
[ apply (minus_plus_m_m (times (div a b) b) (mod a b))
| assumption
]
qed.

inductive div_mod_spec (n,m,q,r:nat) : Prop \def
div_mod_spec_intro: r < m \to n=q*m+r \to (div_mod_spec n m q r).

(* 
definition div_mod_spec : nat \to nat \to nat \to nat \to Prop \def
\lambda n,m,q,r:nat.r < m \land n=q*m+r).
*)

theorem div_mod_spec_to_not_eq_O: \forall n,m,q,r.(div_mod_spec n m q r) \to m \neq O.
intros 4.unfold Not.intros.elim H.absurd (le (S r) O).
rewrite < H1.assumption.
exact (not_le_Sn_O r).
qed.

theorem div_mod_spec_div_mod: 
\forall n,m. O < m \to (div_mod_spec n m (n / m) (n \mod m)).
intros.
apply div_mod_spec_intro.
apply lt_mod_m_m.assumption.
apply div_mod.assumption.
qed. 

theorem div_mod_spec_to_eq :\forall a,b,q,r,q1,r1.
(div_mod_spec a b q r) \to (div_mod_spec a b q1 r1) \to 
(eq nat q q1).
intros.elim H.elim H1.
apply (nat_compare_elim q q1).intro.
apply False_ind.
cut (eq nat ((q1-q)*b+r1) r).
cut (b \leq (q1-q)*b+r1).
cut (b \leq r).
apply (lt_to_not_le r b H2 Hcut2).
elim Hcut.assumption.
apply (trans_le ? ((q1-q)*b)).
apply le_times_n.
apply le_SO_minus.exact H6.
rewrite < sym_plus.
apply le_plus_n.
rewrite < sym_times.
rewrite > distr_times_minus.
rewrite > plus_minus.
lapply(plus_to_minus ??? H3); demodulate all.
(*
rewrite > sym_times.
rewrite < H5.
rewrite < sym_times. 
apply plus_to_minus.
apply H3.
*)
apply le_times_r.
apply lt_to_le.
apply H6.
(* eq case *)
intros.assumption.
(* the following case is symmetric *)
intro.
apply False_ind.
cut (eq nat ((q-q1)*b+r) r1).
cut (b \leq (q-q1)*b+r).
cut (b \leq r1).
apply (lt_to_not_le r1 b H4 Hcut2).
elim Hcut.assumption.
apply (trans_le ? ((q-q1)*b)).
apply le_times_n.
apply le_SO_minus.exact H6.
rewrite < sym_plus.
apply le_plus_n.
rewrite < sym_times.
rewrite > distr_times_minus.
rewrite > plus_minus.
rewrite > sym_times.
rewrite < H3.
rewrite < sym_times.
apply plus_to_minus.
apply H5.
apply le_times_r.
apply lt_to_le.
apply H6.
qed.

theorem div_mod_spec_to_eq2 :\forall a,b,q,r,q1,r1.
(div_mod_spec a b q r) \to (div_mod_spec a b q1 r1) \to 
(eq nat r r1).
intros.elim H.elim H1.
apply (inj_plus_r (q*b)).
rewrite < H3.
rewrite > (div_mod_spec_to_eq a b q r q1 r1 H H1).
assumption.
qed.

theorem div_mod_spec_times : \forall n,m:nat.div_mod_spec ((S n)*m) (S n) m O.
intros.constructor 1.
unfold lt.apply le_S_S.apply le_O_n. demodulate. reflexivity.
(*rewrite < plus_n_O.rewrite < sym_times.reflexivity.*)
qed.

lemma div_plus_times: \forall m,q,r:nat. r < m \to  (q*m+r)/ m = q. 
intros.
apply (div_mod_spec_to_eq (q*m+r) m ? ((q*m+r) \mod m) ? r)
  [apply div_mod_spec_div_mod.
   apply (le_to_lt_to_lt ? r)
    [apply le_O_n|assumption]
  |apply div_mod_spec_intro[assumption|reflexivity]
  ]
qed.

lemma mod_plus_times: \forall m,q,r:nat. r < m \to  (q*m+r) \mod m = r. 
intros.
apply (div_mod_spec_to_eq2 (q*m+r) m ((q*m+r)/ m) ((q*m+r) \mod m) q r)
  [apply div_mod_spec_div_mod.
   apply (le_to_lt_to_lt ? r)
    [apply le_O_n|assumption]
  |apply div_mod_spec_intro[assumption|reflexivity]
  ]
qed.

(* some properties of div and mod *)
theorem div_times: \forall n,m:nat. ((S n)*m) / (S n) = m.
intros.
apply (div_mod_spec_to_eq ((S n)*m) (S n) ? ? ? O);
[2: apply div_mod_spec_div_mod.
    unfold lt.apply le_S_S.apply le_O_n.
|   skip
|   apply div_mod_spec_times
]
qed.

(*a simple variant of div_times theorem *)
theorem lt_O_to_div_times: \forall a,b:nat. O \lt b \to
a*b/b = a.
intros.
rewrite > sym_times.
rewrite > (S_pred b H).
apply div_times.
qed.

theorem div_n_n: \forall n:nat. O < n \to n / n = S O.
intros.
apply (div_mod_spec_to_eq n n (n / n) (n \mod n) (S O) O).
apply div_mod_spec_div_mod.assumption.
constructor 1.assumption. demodulate. reflexivity. (*
rewrite < plus_n_O.simplify.rewrite < plus_n_O.reflexivity.*)
qed.

theorem eq_div_O: \forall n,m. n < m \to n / m = O.
intros.
apply (div_mod_spec_to_eq n m (n/m) (n \mod m) O n).
apply div_mod_spec_div_mod.
apply (le_to_lt_to_lt O n m).
apply le_O_n.assumption.
constructor 1.assumption.reflexivity.
qed.

theorem mod_n_n: \forall n:nat. O < n \to n \mod n = O.
intros.
apply (div_mod_spec_to_eq2 n n (n / n) (n \mod n) (S O) O).
apply div_mod_spec_div_mod.assumption.
constructor 1.assumption. demodulate. reflexivity.(*
rewrite < plus_n_O.simplify.rewrite < plus_n_O.reflexivity.*)
qed.

theorem mod_S: \forall n,m:nat. O < m \to S (n \mod m) < m \to 
((S n) \mod m) = S (n \mod m).
intros.
apply (div_mod_spec_to_eq2 (S n) m ((S n) / m) ((S n) \mod m) (n / m) (S (n \mod m))).
apply div_mod_spec_div_mod.assumption.
constructor 1.assumption.rewrite < plus_n_Sm.
apply eq_f.
apply div_mod.
assumption.
qed.

theorem mod_O_n: \forall n:nat.O \mod n = O.
intro.elim n.simplify.reflexivity.
simplify.reflexivity.
qed.

theorem lt_to_eq_mod:\forall n,m:nat. n < m \to n \mod m = n.
intros.
apply (div_mod_spec_to_eq2 n m (n/m) (n \mod m) O n).
apply div_mod_spec_div_mod.
apply (le_to_lt_to_lt O n m).apply le_O_n.assumption.
constructor 1.
assumption.reflexivity.
qed.

theorem mod_SO: \forall n:nat. mod n (S O) = O.
intro.
apply sym_eq.
apply le_n_O_to_eq.
apply le_S_S_to_le.
apply lt_mod_m_m.
apply le_n.
qed.

theorem div_SO: \forall n:nat. div n (S O) = n.
intro.
rewrite > (div_mod ? (S O)) in \vdash (? ? ? %)
  [rewrite > mod_SO.
   rewrite < plus_n_O.
   apply times_n_SO
  |apply le_n
  ]
qed.

theorem or_div_mod: \forall n,q. O < q \to
((S (n \mod q)=q) \land S n = (S (div n q)) * q \lor
((S (n \mod q)<q) \land S n= (div n q) * q + S (n\mod q))).
intros.
elim (le_to_or_lt_eq ? ? (lt_mod_m_m n q H))
  [right.split
    [assumption
    |rewrite < plus_n_Sm.
     apply eq_f.
     apply div_mod.
     assumption
    ]
  |left.split
    [assumption
    |simplify.
     rewrite > sym_plus.
     rewrite < H1 in ⊢ (? ? ? (? ? %)).
     rewrite < plus_n_Sm.
     apply eq_f.
     apply div_mod.
     assumption
    ]
  ]
qed.

(* injectivity *)
theorem injective_times_r: \forall n:nat.injective nat nat (\lambda m:nat.(S n)*m).
change with (\forall n,p,q:nat.(S n)*p = (S n)*q \to p=q).
intros.
rewrite < (div_times n).
rewrite < (div_times n q).
apply eq_f2.assumption.
reflexivity.
qed.

variant inj_times_r : \forall n,p,q:nat.(S n)*p = (S n)*q \to p=q \def
injective_times_r.

theorem lt_O_to_injective_times_r: \forall n:nat. O < n \to injective nat nat (\lambda m:nat.n*m).
simplify.
intros 4.
apply (lt_O_n_elim n H).intros.
apply (inj_times_r m).assumption.
qed.

variant inj_times_r1:\forall n. O < n \to \forall p,q:nat.n*p = n*q \to p=q
\def lt_O_to_injective_times_r.

theorem injective_times_l: \forall n:nat.injective nat nat (\lambda m:nat.m*(S n)).
simplify.
intros.
apply (inj_times_r n x y).
rewrite < sym_times.
rewrite < (sym_times y).
assumption.
qed.

variant inj_times_l : \forall n,p,q:nat. p*(S n) = q*(S n) \to p=q \def
injective_times_l.

theorem lt_O_to_injective_times_l: \forall n:nat. O < n \to injective nat nat (\lambda m:nat.m*n).
simplify.
intros 4.
apply (lt_O_n_elim n H).intros.
apply (inj_times_l m).assumption.
qed.

variant inj_times_l1:\forall n. O < n \to \forall p,q:nat.p*n = q*n \to p=q
\def lt_O_to_injective_times_l.

      
(* n_divides computes the pair (div,mod) *)

(* p is just an upper bound, acc is an accumulator *)
let rec n_divides_aux p n m acc \def
  match n \mod m with
  [ O \Rightarrow 
    match p with
      [ O \Rightarrow pair nat nat acc n
      | (S p) \Rightarrow n_divides_aux p (n / m) m (S acc)]
  | (S a) \Rightarrow pair nat nat acc n].

(* n_divides n m = <q,r> if m divides n q times, with remainder r *)
definition n_divides \def \lambda n,m:nat.n_divides_aux n n m O.

