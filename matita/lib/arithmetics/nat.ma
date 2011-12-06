  (*
    ||M||  This file is part of HELM, an Hypertextual, Electronic        
    ||A||  Library of Mathematics, developed at the Computer Science     
    ||T||  Department of the University of Bologna, Italy.                     
    ||I||                                                                 
    ||T||  
    ||A||  This file is distributed under the terms of the 
    \   /  GNU General Public License Version 2        
     \ /      
      V_______________________________________________________________ *)

include "basics/relations.ma".

inductive nat : Type[0] ≝
  | O : nat
  | S : nat → nat.
  
interpretation "Natural numbers" 'N = nat.

alias num (instance 0) = "natural number".

definition pred ≝
 λn. match n with [ O ⇒ O | S p ⇒ p].

theorem pred_Sn : ∀n. n = pred (S n).
// qed.

theorem injective_S : injective nat nat S.
// qed.

(*
theorem inj_S : \forall n,m:nat.(S n)=(S m) \to n=m.
//. qed. *)

theorem not_eq_S: ∀n,m:nat. n ≠ m → S n ≠ S m.
/2/ qed.

definition not_zero: nat → Prop ≝
 λn: nat. match n with [ O ⇒ False | (S p) ⇒ True ].

theorem not_eq_O_S : ∀n:nat. O ≠ S n.
#n @nmk #eqOS (change with (not_zero O)) >eqOS // qed.

theorem not_eq_n_Sn: ∀n:nat. n ≠ S n.
#n (elim n) /2/ qed.

theorem nat_case:
 ∀n:nat.∀P:nat → Prop. 
  (n=O → P O) → (∀m:nat. n= S m → P (S m)) → P n.
#n #P (elim n) /2/ qed.

theorem nat_elim2 :
 ∀R:nat → nat → Prop.
  (∀n:nat. R O n) 
  → (∀n:nat. R (S n) O)
  → (∀n,m:nat. R n m → R (S n) (S m))
  → ∀n,m:nat. R n m.
#R #ROn #RSO #RSS #n (elim n) // #n0 #Rn0m #m (cases m) /2/ qed.

theorem decidable_eq_nat : ∀n,m:nat.decidable (n=m).
@nat_elim2 #n [ (cases n) /2/ | /3/ | #m #Hind (cases Hind) /3/]
qed. 

(*************************** plus ******************************)

let rec plus n m ≝ 
 match n with [ O ⇒ m | S p ⇒ S (plus p m) ].

interpretation "natural plus" 'plus x y = (plus x y).

theorem plus_O_n: ∀n:nat. n = O+n.
// qed.

(*
theorem plus_Sn_m: ∀n,m:nat. S (n + m) = S n + m.
// qed.
*)

theorem plus_n_O: ∀n:nat. n = n+O.
#n (elim n) normalize // qed.

theorem plus_n_Sm : ∀n,m:nat. S (n+m) = n + S m.
#n (elim n) normalize // qed.

(*
theorem plus_Sn_m1: ∀n,m:nat. S m + n = n + S m.
#n (elim n) normalize // qed.
*)

(* deleterio?
theorem plus_n_1 : ∀n:nat. S n = n+1.
// qed.
*)

theorem commutative_plus: commutative ? plus.
#n (elim n) normalize // qed. 

theorem associative_plus : associative nat plus.
#n (elim n) normalize // qed.

theorem assoc_plus1: ∀a,b,c. c + (b + a) = b + c + a.
// qed. 

theorem injective_plus_r: ∀n:nat.injective nat nat (λm.n+m).
#n (elim n) normalize /3/ qed.

(* theorem inj_plus_r: \forall p,n,m:nat. p+n = p+m \to n=m
\def injective_plus_r. 

theorem injective_plus_l: ∀m:nat.injective nat nat (λn.n+m).
/2/ qed. *)

(* theorem inj_plus_l: \forall p,n,m:nat. n+p = m+p \to n=m
\def injective_plus_l. *)

(*************************** times *****************************)

let rec times n m ≝ 
 match n with [ O ⇒ O | S p ⇒ m+(times p m) ].

interpretation "natural times" 'times x y = (times x y).

theorem times_Sn_m: ∀n,m:nat. m+n*m = S n*m.
// qed.

theorem times_O_n: ∀n:nat. O = O*n.
// qed.

theorem times_n_O: ∀n:nat. O = n*O.
#n (elim n) // qed.

theorem times_n_Sm : ∀n,m:nat. n+(n*m) = n*(S m).
#n (elim n) normalize // qed.

theorem commutative_times : commutative nat times. 
#n (elim n) normalize // qed. 

(* variant sym_times : \forall n,m:nat. n*m = m*n \def
symmetric_times. *)

theorem distributive_times_plus : distributive nat times plus.
#n (elim n) normalize // qed.

theorem distributive_times_plus_r :
  ∀a,b,c:nat. (b+c)*a = b*a + c*a.
// qed. 

theorem associative_times: associative nat times.
#n (elim n) normalize // qed.

lemma times_times: ∀x,y,z. x*(y*z) = y*(x*z).
// qed. 

theorem times_n_1 : ∀n:nat. n = n * 1.
#n // qed.

(* ci servono questi risultati? 
theorem times_O_to_O: ∀n,m:nat.n*m=O → n=O ∨ m=O.
napply nat_elim2 /2/ 
#n #m #H normalize #H1 napply False_ind napply not_eq_O_S
// qed.
  
theorem times_n_SO : ∀n:nat. n = n * S O.
#n // qed.

theorem times_SSO_n : ∀n:nat. n + n = (S(S O)) * n.
normalize // qed.

nlemma times_SSO: \forall n.(S(S O))*(S n) = S(S((S(S O))*n)).
// qed.

theorem or_eq_eq_S: \forall n.\exists m. 
n = (S(S O))*m \lor n = S ((S(S O))*m).
#n (elim n)
  ##[@ /2/
  ##|#a #H nelim H #b#ornelim or#aeq
    ##[@ b @ 2 //
    ##|@ (S b) @ 1 /2/
    ##]
qed.
*)

(******************** ordering relations ************************)

inductive le (n:nat) : nat → Prop ≝
  | le_n : le n n
  | le_S : ∀ m:nat. le n m → le n (S m).

interpretation "natural 'less or equal to'" 'leq x y = (le x y).

interpretation "natural 'neither less nor equal to'" 'nleq x y = (Not (le x y)).

definition lt: nat → nat → Prop ≝ λn,m. S n ≤ m.

interpretation "natural 'less than'" 'lt x y = (lt x y).
interpretation "natural 'not less than'" 'nless x y = (Not (lt x y)).

(* lemma eq_lt: ∀n,m. (n < m) = (S n ≤ m).
// qed. *)

definition ge: nat → nat → Prop ≝ λn,m.m ≤ n.

interpretation "natural 'greater or equal to'" 'geq x y = (ge x y).

definition gt: nat → nat → Prop ≝ λn,m.m<n.

interpretation "natural 'greater than'" 'gt x y = (gt x y).
interpretation "natural 'not greater than'" 'ngtr x y = (Not (gt x y)).

theorem transitive_le : transitive nat le.
#a #b #c #leab #lebc (elim lebc) /2/
qed.

(*
theorem trans_le: \forall n,m,p:nat. n \leq m \to m \leq p \to n \leq p
\def transitive_le. *)

theorem transitive_lt: transitive nat lt.
#a #b #c #ltab #ltbc (elim ltbc) /2/qed.

(*
theorem trans_lt: \forall n,m,p:nat. lt n m \to lt m p \to lt n p
\def transitive_lt. *)

theorem le_S_S: ∀n,m:nat. n ≤ m → S n ≤ S m.
#n #m #lenm (elim lenm) /2/ qed.

theorem le_O_n : ∀n:nat. O ≤ n.
#n (elim n) /2/ qed.

theorem le_n_Sn : ∀n:nat. n ≤ S n.
/2/ qed.

theorem le_pred_n : ∀n:nat. pred n ≤ n.
#n (elim n) // qed.

theorem monotonic_pred: monotonic ? le pred.
#n #m #lenm (elim lenm) /2/ qed.

theorem le_S_S_to_le: ∀n,m:nat. S n ≤ S m → n ≤ m.
(* demo *)
/2/ qed-.

(* this are instances of the le versions 
theorem lt_S_S_to_lt: ∀n,m. S n < S m → n < m.
/2/ qed. 

theorem lt_to_lt_S_S: ∀n,m. n < m → S n < S m.
/2/ qed. *)

theorem lt_to_not_zero : ∀n,m:nat. n < m → not_zero m.
#n #m #Hlt (elim Hlt) // qed.

(* lt vs. le *)
theorem not_le_Sn_O: ∀ n:nat. S n ≰ O.
#n @nmk #Hlen0 @(lt_to_not_zero ?? Hlen0) qed.

theorem not_le_to_not_le_S_S: ∀ n,m:nat. n ≰ m → S n ≰ S m.
/3/ qed.

theorem not_le_S_S_to_not_le: ∀ n,m:nat. S n ≰ S m → n ≰ m.
/3/ qed.

theorem decidable_le: ∀n,m. decidable (n≤m).
@nat_elim2 #n /2/ #m * /3/ qed.

theorem decidable_lt: ∀n,m. decidable (n < m).
#n #m @decidable_le  qed.

theorem not_le_Sn_n: ∀n:nat. S n ≰ n.
#n (elim n) /2/ qed.

(* this is le_S_S_to_le
theorem lt_S_to_le: ∀n,m:nat. n < S m → n ≤ m.
/2/ qed.
*)

lemma le_gen: ∀P:nat → Prop.∀n.(∀i. i ≤ n → P i) → P n.
/2/ qed.

theorem not_le_to_lt: ∀n,m. n ≰ m → m < n.
@nat_elim2 #n
 [#abs @False_ind /2/
 |/2/
 |#m #Hind #HnotleSS @le_S_S /3/
 ]
qed.

theorem lt_to_not_le: ∀n,m. n < m → m ≰ n.
#n #m #Hltnm (elim Hltnm) /3/ qed.

theorem not_lt_to_le: ∀n,m:nat. n ≮ m → m ≤ n.
/4/ qed.

theorem le_to_not_lt: ∀n,m:nat. n ≤ m → m ≮ n.
#n #m #H @lt_to_not_le /2/ (* /3/ *) qed.

(* lt and le trans *)

theorem lt_to_le_to_lt: ∀n,m,p:nat. n < m → m ≤ p → n < p.
#n #m #p #H #H1 (elim H1) /2/ qed.

theorem le_to_lt_to_lt: ∀n,m,p:nat. n ≤ m → m < p → n < p.
#n #m #p #H (elim H) /3/ qed.

theorem lt_S_to_lt: ∀n,m. S n < m → n < m.
/2/ qed.

theorem ltn_to_ltO: ∀n,m:nat. n < m → O < m.
/2/ qed.

(*
theorem lt_SO_n_to_lt_O_pred_n: \forall n:nat.
(S O) \lt n \to O \lt (pred n).
intros.
apply (ltn_to_ltO (pred (S O)) (pred n) ?).
 apply (lt_pred (S O) n)
 [ apply (lt_O_S O) 
 | assumption
 ]
qed. *)

theorem lt_O_n_elim: ∀n:nat. O < n → 
  ∀P:nat → Prop.(∀m:nat.P (S m)) → P n.
#n (elim n) // #abs @False_ind /2/
qed.

theorem S_pred: ∀n. 0 < n → S(pred n) = n.
#n #posn (cases posn) //
qed.

(*
theorem lt_pred: \forall n,m. 
  O < n \to n < m \to pred n < pred m. 
apply nat_elim2
  [intros.apply False_ind.apply (not_le_Sn_O ? H)
  |intros.apply False_ind.apply (not_le_Sn_O ? H1)
  |intros.simplify.unfold.apply le_S_S_to_le.assumption
  ]
qed.

theorem le_pred_to_le:
 ∀n,m. O < m → pred n ≤ pred m → n ≤ m.
intros 2
elim n
[ apply le_O_n
| simplify in H2
  rewrite > (S_pred m)
  [ apply le_S_S
    assumption
  | assumption
  ]
].
qed.

*)

(* le to lt or eq *)
theorem le_to_or_lt_eq: ∀n,m:nat. n ≤ m → n < m ∨ n = m.
#n #m #lenm (elim lenm) /3/ qed.

(* not eq *)
theorem lt_to_not_eq : ∀n,m:nat. n < m → n ≠ m.
#n #m #H @not_to_not /2/ qed.

(*not lt 
theorem eq_to_not_lt: ∀a,b:nat. a = b → a ≮ b.
intros.
unfold Not.
intros.
rewrite > H in H1.
apply (lt_to_not_eq b b)
[ assumption
| reflexivity
]
qed. 

theorem lt_n_m_to_not_lt_m_Sn: ∀n,m. n < m → m ≮ S n.
intros
unfold Not
intro
unfold lt in H
unfold lt in H1
generalize in match (le_S_S ? ? H)
intro
generalize in match (transitive_le ? ? ? H2 H1)
intro
apply (not_le_Sn_n ? H3).
qed. *)

theorem not_eq_to_le_to_lt: ∀n,m. n≠m → n≤m → n<m.
#n #m #Hneq #Hle cases (le_to_or_lt_eq ?? Hle) //
#Heq /3/ qed-.
(*
nelim (Hneq Heq) qed. *)

(* le elimination *)
theorem le_n_O_to_eq : ∀n:nat. n ≤ O → O=n.
#n (cases n) // #a  #abs @False_ind /2/ qed.

theorem le_n_O_elim: ∀n:nat. n ≤ O → ∀P: nat →Prop. P O → P n.
#n (cases n) // #a #abs @False_ind /2/ qed. 

theorem le_n_Sm_elim : ∀n,m:nat.n ≤ S m → 
∀P:Prop. (S n ≤ S m → P) → (n=S m → P) → P.
#n #m #Hle #P (elim Hle) /3/ qed.

(* le and eq *)

theorem le_to_le_to_eq: ∀n,m. n ≤ m → m ≤ n → n = m.
@nat_elim2 /4/
qed. 

theorem lt_O_S : ∀n:nat. O < S n.
/2/ qed.

(*
(* other abstract properties *)
theorem antisymmetric_le : antisymmetric nat le.
unfold antisymmetric.intros 2.
apply (nat_elim2 (\lambda n,m.(n \leq m \to m \leq n \to n=m))).
intros.apply le_n_O_to_eq.assumption.
intros.apply False_ind.apply (not_le_Sn_O ? H).
intros.apply eq_f.apply H.
apply le_S_S_to_le.assumption.
apply le_S_S_to_le.assumption.
qed.

theorem antisym_le: \forall n,m:nat. n \leq m \to m \leq n \to n=m
\def antisymmetric_le.

theorem le_n_m_to_lt_m_Sn_to_eq_n_m: ∀n,m. n ≤ m → m < S n → n=m.
intros
unfold lt in H1
generalize in match (le_S_S_to_le ? ? H1)
intro
apply antisym_le
assumption.
qed.
*)

(* well founded induction principles *)

theorem nat_elim1 : ∀n:nat.∀P:nat → Prop. 
(∀m.(∀p. p < m → P p) → P m) → P n.
#n #P #H 
cut (∀q:nat. q ≤ n → P q) /2/
(elim n) 
 [#q #HleO (* applica male *) 
    @(le_n_O_elim ? HleO)
    @H #p #ltpO @False_ind /2/ (* 3 *)
 |#p #Hind #q #HleS 
    @H #a #lta @Hind @le_S_S_to_le /2/
 ]
qed.

(* some properties of functions *)

definition increasing ≝ λf:nat → nat. ∀n:nat. f n < f (S n).

theorem increasing_to_monotonic: ∀f:nat → nat.
  increasing f → monotonic nat lt f.
#f #incr #n #m #ltnm (elim ltnm) /2/
qed.

theorem le_n_fn: ∀f:nat → nat. 
  increasing f → ∀n:nat. n ≤ f n.
#f #incr #n (elim n) /2/
qed-.

theorem increasing_to_le: ∀f:nat → nat. 
  increasing f → ∀m:nat.∃i.m ≤ f i.
#f #incr #m (elim m) /2/#n * #a #lenfa
@(ex_intro ?? (S a)) /2/
qed.

theorem increasing_to_le2: ∀f:nat → nat. increasing f → 
  ∀m:nat. f 0 ≤ m → ∃i. f i ≤ m ∧ m < f (S i).
#f #incr #m #lem (elim lem)
  [@(ex_intro ? ? O) /2/
  |#n #len * #a * #len #ltnr (cases(le_to_or_lt_eq … ltnr)) #H
    [@(ex_intro ? ? a) % /2/ 
    |@(ex_intro ? ? (S a)) % //
    ]
  ]
qed.

theorem increasing_to_injective: ∀f:nat → nat.
  increasing f → injective nat nat f.
#f #incr #n #m cases(decidable_le n m)
  [#lenm cases(le_to_or_lt_eq … lenm) //
   #lenm #eqf @False_ind @(absurd … eqf) @lt_to_not_eq 
   @increasing_to_monotonic //
  |#nlenm #eqf @False_ind @(absurd … eqf) @sym_not_eq 
   @lt_to_not_eq @increasing_to_monotonic /2/
  ]
qed.

(*********************** monotonicity ***************************)
theorem monotonic_le_plus_r: 
∀n:nat.monotonic nat le (λm.n + m).
#n #a #b (elim n) normalize //
#m #H #leab @le_S_S /2/ qed.

(*
theorem le_plus_r: ∀p,n,m:nat. n ≤ m → p + n ≤ p + m
≝ monotonic_le_plus_r. *)

theorem monotonic_le_plus_l: 
∀m:nat.monotonic nat le (λn.n + m).
/2/ qed.

(*
theorem le_plus_l: \forall p,n,m:nat. n \le m \to n + p \le m + p
\def monotonic_le_plus_l. *)

theorem le_plus: ∀n1,n2,m1,m2:nat. n1 ≤ n2  → m1 ≤ m2 
→ n1 + m1 ≤ n2 + m2.
#n1 #n2 #m1 #m2 #len #lem @(transitive_le ? (n1+m2))
/2/ qed-.

theorem le_plus_n :∀n,m:nat. m ≤ n + m.
/2/ qed. 

lemma le_plus_a: ∀a,n,m. n ≤ m → n ≤ a + m.
/2/ qed.

lemma le_plus_b: ∀b,n,m. n + b ≤ m → n ≤ m.
/2/ qed.

theorem le_plus_n_r :∀n,m:nat. m ≤ m + n.
/2/ qed.

theorem eq_plus_to_le: ∀n,m,p:nat.n=m+p → m ≤ n.
// qed-.

theorem le_plus_to_le: ∀a,n,m. a + n ≤ a + m → n ≤ m.
#a (elim a) normalize /3/ qed. 

theorem le_plus_to_le_r: ∀a,n,m. n + a ≤ m +a → n ≤ m.
/2/ qed-. 

(* plus & lt *)

theorem monotonic_lt_plus_r: 
∀n:nat.monotonic nat lt (λm.n+m).
/2/ qed.

(*
variant lt_plus_r: \forall n,p,q:nat. p < q \to n + p < n + q \def
monotonic_lt_plus_r. *)

theorem monotonic_lt_plus_l: 
∀n:nat.monotonic nat lt (λm.m+n).
/2/ qed.

(*
variant lt_plus_l: \forall n,p,q:nat. p < q \to p + n < q + n \def
monotonic_lt_plus_l. *)

theorem lt_plus: ∀n,m,p,q:nat. n < m → p < q → n + p < m + q.
#n #m #p #q #ltnm #ltpq
@(transitive_lt ? (n+q))/2/ qed.

theorem lt_plus_to_lt_l :∀n,p,q:nat. p+n < q+n → p<q.
/2/ qed.

theorem lt_plus_to_lt_r :∀n,p,q:nat. n+p < n+q → p<q.
/2/ qed-.

(*
theorem le_to_lt_to_lt_plus: ∀a,b,c,d:nat.
a ≤ c → b < d → a + b < c+d.
(* bello /2/ un po' lento *)
#a #b #c #d #leac #lebd 
normalize napplyS le_plus // qed.
*)

(* times *)
theorem monotonic_le_times_r: 
∀n:nat.monotonic nat le (λm. n * m).
#n #x #y #lexy (elim n) normalize//(* lento /2/*)
#a #lea @le_plus //
qed.

(*
theorem le_times_r: \forall p,n,m:nat. n \le m \to p*n \le p*m
\def monotonic_le_times_r. *)

(*
theorem monotonic_le_times_l: 
∀m:nat.monotonic nat le (λn.n*m).
/2/ qed.
*)

(*
theorem le_times_l: \forall p,n,m:nat. n \le m \to n*p \le m*p
\def monotonic_le_times_l. *)

theorem le_times: ∀n1,n2,m1,m2:nat. 
n1 ≤ n2  → m1 ≤ m2 → n1*m1 ≤ n2*m2.
#n1 #n2 #m1 #m2 #len #lem @(transitive_le ? (n1*m2)) /2/
qed.

(* interessante *)
theorem lt_times_n: ∀n,m:nat. O < n → m ≤ n*m.
#n #m #H /2/ qed.

theorem le_times_to_le: 
∀a,n,m. O < a → a * n ≤ a * m → n ≤ m.
#a @nat_elim2 normalize
  [//
  |#n #H1 #H2 
     @(transitive_le ? (a*S n)) /2/
  |#n #m #H #lta #le
     @le_S_S @H /2/
  ]
qed-.

(*
theorem le_S_times_2: ∀n,m.O < m → n ≤ m → S n ≤ 2*m.
#n #m #posm #lenm  (* interessante *)
applyS (le_plus n m) // qed. *)

(* times & lt *)
(*
theorem lt_O_times_S_S: ∀n,m:nat.O < (S n)*(S m).
intros.simplify.unfold lt.apply le_S_S.apply le_O_n.
qed. *)

(*
theorem lt_times_eq_O: \forall a,b:nat.
O < a → a * b = O → b = O.
intros.
apply (nat_case1 b)
[ intros.
  reflexivity
| intros.
  rewrite > H2 in H1.
  rewrite > (S_pred a) in H1
  [ apply False_ind.
    apply (eq_to_not_lt O ((S (pred a))*(S m)))
    [ apply sym_eq.
      assumption
    | apply lt_O_times_S_S
    ]
  | assumption
  ]
]
qed. 

theorem O_lt_times_to_O_lt: \forall a,c:nat.
O \lt (a * c) \to O \lt a.
intros.
apply (nat_case1 a)
[ intros.
  rewrite > H1 in H.
  simplify in H.
  assumption
| intros.
  apply lt_O_S
]
qed.

lemma lt_times_to_lt_O: \forall i,n,m:nat. i < n*m \to O < m.
intros.
elim (le_to_or_lt_eq O ? (le_O_n m))
  [assumption
  |apply False_ind.
   rewrite < H1 in H.
   rewrite < times_n_O in H.
   apply (not_le_Sn_O ? H)
  ]
qed. *)

(*
theorem monotonic_lt_times_r: 
∀n:nat.monotonic nat lt (λm.(S n)*m).
/2/ 
simplify.
intros.elim n.
simplify.rewrite < plus_n_O.rewrite < plus_n_O.assumption.
apply lt_plus.assumption.assumption.
qed. *)

theorem monotonic_lt_times_r: 
  ∀c:nat. O < c → monotonic nat lt (λt.(c*t)).
#c #posc #n #m #ltnm
(elim ltnm) normalize
  [/2/ 
  |#a #_ #lt1 @(transitive_le … lt1) //
  ]
qed.

theorem monotonic_lt_times_l: 
  ∀c:nat. O < c → monotonic nat lt (λt.(t*c)).
/2/
qed.

theorem lt_to_le_to_lt_times: 
∀n,m,p,q:nat. n < m → p ≤ q → O < q → n*p < m*q.
#n #m #p #q #ltnm #lepq #posq
@(le_to_lt_to_lt ? (n*q))
  [@monotonic_le_times_r //
  |@monotonic_lt_times_l //
  ]
qed.

theorem lt_times:∀n,m,p,q:nat. n<m → p<q → n*p < m*q.
#n #m #p #q #ltnm #ltpq @lt_to_le_to_lt_times/2/
qed.

theorem lt_times_n_to_lt_l: 
∀n,p,q:nat. p*n < q*n → p < q.
#n #p #q #Hlt (elim (decidable_lt p q)) //
#nltpq @False_ind @(absurd ? ? (lt_to_not_le ? ? Hlt))
applyS monotonic_le_times_r /2/
qed.

theorem lt_times_n_to_lt_r: 
∀n,p,q:nat. n*p < n*q → p < q.
/2/ qed-.

(*
theorem nat_compare_times_l : \forall n,p,q:nat. 
nat_compare p q = nat_compare ((S n) * p) ((S n) * q).
intros.apply nat_compare_elim.intro.
apply nat_compare_elim.
intro.reflexivity.
intro.absurd (p=q).
apply (inj_times_r n).assumption.
apply lt_to_not_eq. assumption.
intro.absurd (q<p).
apply (lt_times_to_lt_r n).assumption.
apply le_to_not_lt.apply lt_to_le.assumption.
intro.rewrite < H.rewrite > nat_compare_n_n.reflexivity.
intro.apply nat_compare_elim.intro.
absurd (p<q).
apply (lt_times_to_lt_r n).assumption.
apply le_to_not_lt.apply lt_to_le.assumption.
intro.absurd (q=p).
symmetry.
apply (inj_times_r n).assumption.
apply lt_to_not_eq.assumption.
intro.reflexivity.
qed. *)

(* times and plus 
theorem lt_times_plus_times: \forall a,b,n,m:nat. 
a < n \to b < m \to a*m + b < n*m.
intros 3.
apply (nat_case n)
  [intros.apply False_ind.apply (not_le_Sn_O ? H)
  |intros.simplify.
   rewrite < sym_plus.
   unfold.
   change with (S b+a*m1 \leq m1+m*m1).
   apply le_plus
    [assumption
    |apply le_times
      [apply le_S_S_to_le.assumption
      |apply le_n
      ]
    ]
  ]
qed. *)

(************************** minus ******************************)

let rec minus n m ≝ 
 match n with 
 [ O ⇒ O
 | S p ⇒ 
	match m with
	  [ O ⇒ S p
    | S q ⇒ minus p q ]].
        
interpretation "natural minus" 'minus x y = (minus x y).

theorem minus_S_S: ∀n,m:nat.S n - S m = n -m.
// qed.

theorem minus_O_n: ∀n:nat.O=O-n.
#n (cases n) // qed.

theorem minus_n_O: ∀n:nat.n=n-O.
#n (cases n) // qed.

theorem minus_n_n: ∀n:nat.O=n-n.
#n (elim n) // qed.

theorem minus_Sn_n: ∀n:nat. S O = (S n)-n.
#n (elim n) normalize // qed.

theorem minus_Sn_m: ∀m,n:nat. m ≤ n → S n -m = S (n-m).
(* qualcosa da capire qui 
#n #m #lenm nelim lenm napplyS refl_eq. *)
@nat_elim2 
  [//
  |#n #abs @False_ind /2/ 
  |#n #m #Hind #c applyS Hind /2/
  ]
qed.

(*
theorem not_eq_to_le_to_le_minus: 
  ∀n,m.n ≠ m → n ≤ m → n ≤ m - 1.
#n * #m (cases m// #m normalize
#H #H1 napply le_S_S_to_le
napplyS (not_eq_to_le_to_lt n (S m) H H1)
qed. *)

theorem eq_minus_S_pred: ∀n,m. n - (S m) = pred(n -m).
@nat_elim2 normalize // qed.

theorem plus_minus:
∀m,n,p:nat. m ≤ n → (n-m)+p = (n+p)-m.
@nat_elim2 
  [//
  |#n #p #abs @False_ind /2/
  |normalize/3/
  ]
qed.

theorem minus_plus_m_m: ∀n,m:nat.n = (n+m)-m.
/2/ qed.

theorem plus_minus_m_m: ∀n,m:nat.
  m ≤ n → n = (n-m)+m.
#n #m #lemn @sym_eq /2/ qed.

theorem le_plus_minus_m_m: ∀n,m:nat. n ≤ (n-m)+m.
#n (elim n) // #a #Hind #m (cases m) // normalize #n/2/  
qed.

theorem minus_to_plus :∀n,m,p:nat.
  m ≤ n → n-m = p → n = m+p.
#n #m #p #lemn #eqp (applyS plus_minus_m_m) //
qed.

theorem plus_to_minus :∀n,m,p:nat.n = m+p → n-m = p.
#n #m #p #eqp @sym_eq (applyS (minus_plus_m_m p m))
qed.

theorem minus_pred_pred : ∀n,m:nat. O < n → O < m → 
pred n - pred m = n - m.
#n #m #posn #posm @(lt_O_n_elim n posn) @(lt_O_n_elim m posm) //.
qed.


(*

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
(* end auto($Revision: 9739 $) proof: TIME=1.33 SIZE=100 DEPTH=100 *)
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
*)

(* monotonicity and galois *)

theorem monotonic_le_minus_l: 
∀p,q,n:nat. q ≤ p → q-n ≤ p-n.
@nat_elim2 #p #q
  [#lePO @(le_n_O_elim ? lePO) //
  |//
  |#Hind #n (cases n) // #a #leSS @Hind /2/
  ]
qed.

theorem le_minus_to_plus: ∀n,m,p. n-m ≤ p → n≤ p+m.
#n #m #p #lep @transitive_le
  [|@le_plus_minus_m_m | @monotonic_le_plus_l // ]
qed.

theorem le_minus_to_plus_r: ∀a,b,c. c ≤ b → a ≤ b - c → a + c ≤ b.
#a #b #c #Hlecb #H >(plus_minus_m_m … Hlecb) /2/
qed.

theorem le_plus_to_minus: ∀n,m,p. n ≤ p+m → n-m ≤ p.
#n #m #p #lep /2/ qed.

theorem le_plus_to_minus_r: ∀a,b,c. a + b ≤ c → a ≤ c -b.
#a #b #c #H @(le_plus_to_le_r … b) /2/
qed.

theorem lt_minus_to_plus: ∀a,b,c. a - b < c → a < c + b.
#a #b #c #H @not_le_to_lt 
@(not_to_not … (lt_to_not_le …H)) /2/
qed.

theorem lt_minus_to_plus_r: ∀a,b,c. a < b - c → a + c < b.
#a #b #c #H @not_le_to_lt @(not_to_not … (le_plus_to_minus …))
@lt_to_not_le //
qed.

theorem lt_plus_to_minus: ∀n,m,p. m ≤ n → n < p+m → n-m < p.
#n #m #p #lenm #H normalize <minus_Sn_m // @le_plus_to_minus //
qed.

theorem lt_plus_to_minus_r: ∀a,b,c. a + b < c → a < c - b.
#a #b #c #H @le_plus_to_minus_r //
qed. 

theorem monotonic_le_minus_r: 
∀p,q,n:nat. q ≤ p → n-p ≤ n-q.
#p #q #n #lepq @le_plus_to_minus
@(transitive_le … (le_plus_minus_m_m ? q)) /2/
qed.

theorem monotonic_lt_minus_l: ∀p,q,n. n ≤ q → q < p → q - n < p - n.
#p #q #n #H1 #H2
@lt_plus_to_minus_r <plus_minus_m_m //
qed.

theorem eq_minus_O: ∀n,m:nat.
  n ≤ m → n-m = O.
#n #m #lenm @(le_n_O_elim (n-m)) /2/
qed.

theorem distributive_times_minus: distributive ? times minus.
#a #b #c
(cases (decidable_lt b c)) #Hbc
 [> eq_minus_O /2/ >eq_minus_O // 
  @monotonic_le_times_r /2/
 |@sym_eq (applyS plus_to_minus) <distributive_times_plus 
  @eq_f (applyS plus_minus_m_m) /2/
qed.

theorem minus_plus: ∀n,m,p. n-m-p = n -(m+p).
#n #m #p 
cases (decidable_le (m+p) n) #Hlt
  [@plus_to_minus @plus_to_minus <associative_plus
   @minus_to_plus //
  |cut (n ≤ m+p) [@(transitive_le … (le_n_Sn …)) @not_le_to_lt //]
   #H >eq_minus_O /2/ (* >eq_minus_O // *) 
  ]
qed.

(*
theorem plus_minus: ∀n,m,p. p ≤ m → (n+m)-p = n +(m-p).
#n #m #p #lepm @plus_to_minus >(commutative_plus p)
>associative_plus <plus_minus_m_m //
qed.  *)

theorem minus_minus: ∀n,m,p:nat. p ≤ m → m ≤ n →
  p+(n-m) = n-(m-p).
#n #m #p #lepm #lemn
@sym_eq @plus_to_minus <associative_plus <plus_minus_m_m //
<commutative_plus <plus_minus_m_m //
qed.

(*********************** boolean arithmetics ********************) 
include "basics/bool.ma".

let rec eqb n m ≝ 
match n with 
  [ O ⇒ match m with [ O ⇒ true | S q ⇒ false] 
  | S p ⇒ match m with [ O ⇒ false | S q ⇒ eqb p q]
  ].

theorem eqb_elim : ∀ n,m:nat.∀ P:bool → Prop.
(n=m → (P true)) → (n ≠ m → (P false)) → (P (eqb n m)). 
@nat_elim2 
  [#n (cases n) normalize /3/ 
  |normalize /3/
  |normalize /4/ 
  ] 
qed.

theorem eqb_n_n: ∀n. eqb n n = true.
#n (elim n) normalize // qed. 

theorem eqb_true_to_eq: ∀n,m:nat. eqb n m = true → n = m.
#n #m @(eqb_elim n m) // #_ #abs @False_ind /2/ qed.

theorem eqb_false_to_not_eq: ∀n,m:nat. eqb n m = false → n ≠ m.
#n #m @(eqb_elim n m) /2/ qed.

theorem eq_to_eqb_true: ∀n,m:nat.n = m → eqb n m = true.
// qed.

theorem not_eq_to_eqb_false: ∀n,m:nat.
  n ≠  m → eqb n m = false.
#n #m #noteq @eqb_elim// #Heq @False_ind /2/ qed.

let rec leb n m ≝ 
match n with 
    [ O ⇒ true
    | (S p) ⇒
	match m with 
        [ O ⇒ false
	      | (S q) ⇒ leb p q]].

theorem leb_elim: ∀n,m:nat. ∀P:bool → Prop. 
(n ≤ m → P true) → (n ≰ m → P false) → P (leb n m).
@nat_elim2 normalize
  [/2/
  |/3/
  |#n #m #Hind #P #Pt #Pf @Hind
    [#lenm @Pt @le_S_S // |#nlenm @Pf /2/ ]
  ]
qed.

theorem leb_true_to_le:∀n,m.leb n m = true → n ≤ m.
#n #m @leb_elim // #_ #abs @False_ind /2/ qed.

theorem leb_false_to_not_le:∀n,m.
  leb n m = false → n ≰ m.
#n #m @leb_elim // #_ #abs @False_ind /2/ qed.

theorem le_to_leb_true: ∀n,m. n ≤ m → leb n m = true.
#n #m @leb_elim // #H #H1 @False_ind /2/ qed.

theorem not_le_to_leb_false: ∀n,m. n ≰ m → leb n m = false.
#n #m @leb_elim // #H #H1 @False_ind /2/ qed.

theorem lt_to_leb_false: ∀n,m. m < n → leb n m = false.
/3/ qed.

(* serve anche ltb? 
ndefinition ltb ≝λn,m. leb (S n) m.

theorem ltb_elim: ∀n,m:nat. ∀P:bool → Prop. 
(n < m → P true) → (n ≮ m → P false) → P (ltb n m).
#n #m #P #Hlt #Hnlt
napply leb_elim /3/ qed.

theorem ltb_true_to_lt:∀n,m.ltb n m = true → n < m.
#n #m #Hltb napply leb_true_to_le nassumption
qed.

theorem ltb_false_to_not_lt:∀n,m.
  ltb n m = false → n ≮ m.
#n #m #Hltb napply leb_false_to_not_le nassumption
qed.

theorem lt_to_ltb_true: ∀n,m. n < m → ltb n m = true.
#n #m #Hltb napply le_to_leb_true nassumption
qed.

theorem le_to_ltb_false: ∀n,m. m \le n → ltb n m = false.
#n #m #Hltb napply lt_to_leb_false /2/
qed. *)

(* min e max *)
definition min: nat →nat →nat ≝
λn.λm. if_then_else ? (leb n m) n m.

definition max: nat →nat →nat ≝
λn.λm. if_then_else ? (leb n m) m n.

lemma commutative_min: commutative ? min.
#n #m normalize @leb_elim 
  [@leb_elim normalize /2/
  |#notle >(le_to_leb_true …) // @(transitive_le ? (S m)) /2/
  ] qed.

lemma le_minr: ∀i,n,m. i ≤ min n m → i ≤ m.
#i #n #m normalize @leb_elim normalize /2/ qed. 

lemma le_minl: ∀i,n,m. i ≤ min n m → i ≤ n.
/2/ qed-.

lemma to_min: ∀i,n,m. i ≤ n → i ≤ m → i ≤ min n m.
#i #n #m #lein #leim normalize (cases (leb n m)) 
normalize // qed.

lemma commutative_max: commutative ? max.
#n #m normalize @leb_elim 
  [@leb_elim normalize /2/
  |#notle >(le_to_leb_true …) // @(transitive_le ? (S m)) /2/
  ] qed.

lemma le_maxl: ∀i,n,m. max n m ≤ i → n ≤ i.
#i #n #m normalize @leb_elim normalize /2/ qed. 

lemma le_maxr: ∀i,n,m. max n m ≤ i → m ≤ i.
/2/ qed-.

lemma to_max: ∀i,n,m. n ≤ i → m ≤ i → max n m ≤ i.
#i #n #m #leni #lemi normalize (cases (leb n m)) 
normalize // qed.

