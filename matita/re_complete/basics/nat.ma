include "basics/relations.ma".
include "basics/bool.ma".

(* natural numbers *)

inductive nat : Type[0] ≝
  | O : nat
  | S : nat → nat.
  
interpretation "Natural numbers" 'N = nat.

alias num (instance 0) = "natural number".

definition pred ≝
 λn. match n with [ O ⇒ O | S p ⇒ p].

definition not_zero: nat → Prop ≝
 λn: nat. match n with [ O ⇒ False | (S p) ⇒ True ].

(* order relations *)

inductive le (n:nat) : nat → Prop ≝
  | le_n : le n n
  | le_S : ∀ m:nat. le n m → le n (S m).

interpretation "natural 'less or equal to'" 'leq x y = (le x y).

interpretation "natural 'neither less nor equal to'" 'nleq x y = (Not (le x y)).

definition lt: nat → nat → Prop ≝ λn,m. S n ≤ m.

interpretation "natural 'less than'" 'lt x y = (lt x y).

interpretation "natural 'not less than'" 'nless x y = (Not (lt x y)).

(* abstract properties *)

definition increasing ≝ λf:nat → nat. ∀n:nat. f n < f (S n).

(* arithmetic operations *)

let rec plus n m ≝ 
 match n with [ O ⇒ m | S p ⇒ S (plus p m) ].

interpretation "natural plus" 'plus x y = (plus x y).

(* Generic conclusion ******************************************************)

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

lemma le_gen: ∀P:nat → Prop.∀n.(∀i. i ≤ n → P i) → P n.
/2/ qed.

(* Equalities ***************************************************************)

theorem pred_Sn : ∀n. n = pred (S n).
// qed.

theorem injective_S : injective nat nat S.
#a #b #H >(pred_Sn a) >(pred_Sn b) @eq_f // qed.

theorem S_pred: ∀n. O < n → S(pred n) = n.
#n #posn (cases posn) //
qed.

theorem plus_O_n: ∀n:nat. n = O + n.
// qed.

theorem plus_n_O: ∀n:nat. n = n + O.
#n (elim n) normalize // qed.

theorem plus_n_Sm : ∀n,m:nat. S (n+m) = n + S m.
#n (elim n) normalize // qed.

theorem commutative_plus: commutative ? plus.
#n (elim n) normalize // qed. 

theorem associative_plus : associative nat plus.
#n (elim n) normalize // qed.

theorem assoc_plus1: ∀a,b,c. c + (b + a) = b + c + a.
// qed. 

theorem injective_plus_r: ∀n:nat.injective nat nat (λm.n+m).
#n (elim n) normalize /3/ qed.

theorem not_eq_S: ∀n,m:nat. n ≠ m → S n ≠ S m.
/2/ qed.

(* not_zero *)

theorem lt_to_not_zero : ∀n,m:nat. n < m → not_zero m.
#n #m #Hlt (elim Hlt) // qed.

(* le *)

theorem le_S_S: ∀n,m:nat. n ≤ m → S n ≤ S m.
#n #m #lenm (elim lenm) /2/ qed.

theorem le_O_n : ∀n:nat. O ≤ n.
#n (elim n) /2/ qed.

theorem le_n_Sn : ∀n:nat. n ≤ S n.
/2/ qed.

theorem transitive_le : transitive nat le.
#a #b #c #leab #lebc (elim lebc) /2/
qed.

theorem le_pred_n : ∀n:nat. pred n ≤ n.
#n (elim n) // qed.

theorem monotonic_pred: monotonic ? le pred.
#n #m #lenm (elim lenm) /2/ qed.

theorem le_S_S_to_le: ∀n,m:nat. S n ≤ S m → n ≤ m.
(* demo *)
/2/ qed-.

theorem monotonic_le_plus_r: 
∀n:nat.monotonic nat le (λm.n + m).
#n #a #b (elim n) normalize //
#m #H #leab @le_S_S /2/ qed.

theorem monotonic_le_plus_l: 
∀m:nat.monotonic nat le (λn.n + m).
/2/ qed.

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

(* lt *)

theorem transitive_lt: transitive nat lt.
#a #b #c #ltab #ltbc (elim ltbc) /2/
qed.

theorem lt_to_le_to_lt: ∀n,m,p:nat. n < m → m ≤ p → n < p.
#n #m #p #H #H1 (elim H1) /2/ qed.

theorem le_to_lt_to_lt: ∀n,m,p:nat. n ≤ m → m < p → n < p.
#n #m #p #H (elim H) /3/ qed.

theorem lt_S_to_lt: ∀n,m. S n < m → n < m.
/2/ qed.

theorem ltn_to_ltO: ∀n,m:nat. n < m → O < m.
/2/ qed.

theorem lt_O_S : ∀n:nat. O < S n.
/2/ qed.

theorem monotonic_lt_plus_r: 
∀n:nat.monotonic nat lt (λm.n+m).
/2/ qed.

theorem monotonic_lt_plus_l: 
∀n:nat.monotonic nat lt (λm.m+n).
/2/ qed.

theorem lt_plus: ∀n,m,p,q:nat. n < m → p < q → n + p < m + q.
#n #m #p #q #ltnm #ltpq
@(transitive_lt ? (n+q))/2/ qed.

theorem lt_plus_to_lt_l :∀n,p,q:nat. p+n < q+n → p<q.
/2/ qed.

theorem lt_plus_to_lt_r :∀n,p,q:nat. n+p < n+q → p<q.
/2/ qed-.

theorem increasing_to_monotonic: ∀f:nat → nat.
  increasing f → monotonic nat lt f.
#f #incr #n #m #ltnm (elim ltnm) /2/
qed.

(* not le, lt *)

theorem not_le_Sn_O: ∀ n:nat. S n ≰ O.
#n @nmk #Hlen0 @(lt_to_not_zero ?? Hlen0) qed.

theorem not_le_to_not_le_S_S: ∀ n,m:nat. n ≰ m → S n ≰ S m.
/3/ qed.

theorem not_le_S_S_to_not_le: ∀ n,m:nat. S n ≰ S m → n ≰ m.
/3/ qed.

theorem not_le_Sn_n: ∀n:nat. S n ≰ n.
#n (elim n) /2/ qed.

theorem lt_to_not_le: ∀n,m. n < m → m ≰ n.
#n #m #Hltnm (elim Hltnm) /3/ qed.

theorem not_le_to_lt: ∀n,m. n ≰ m → m < n.
@nat_elim2 #n
 [#abs @False_ind /2/
 |/2/
 |#m #Hind #HnotleSS @le_S_S /3/
 ]
qed.

(* not lt, le *)

theorem not_lt_to_le: ∀n,m:nat. n ≮ m → m ≤ n.
/4/ qed.

theorem le_to_not_lt: ∀n,m:nat. n ≤ m → m ≮ n.
#n #m #H @lt_to_not_le /2/ (* /3/ *) qed.

(*********************** boolean arithmetics ********************) 


let rec eqbnat n m ≝ 
match n with 
  [ O ⇒ match m with [ O ⇒ true | S q ⇒ false] 
  | S p ⇒ match m with [ O ⇒ false | S q ⇒ eqbnat p q]
  ].

theorem eqbnat_elim : ∀ n,m:nat.∀ P:bool → Prop.
(n=m → (P true)) → (n ≠ m → (P false)) → (P (eqbnat n m)). 
@nat_elim2 
  [#n (cases n) normalize /3/ 
  |normalize /3/
  |normalize /4/ 
  ] 
qed.

theorem eqbnat_n_n: ∀n. eqbnat n n = true.
#n (elim n) normalize // qed. 

theorem eqbnat_true_to_eq: ∀n,m:nat. eqbnat n m = true → n = m.
#n #m @(eqbnat_elim n m) // #_ #abs @False_ind /2/ qed.

(* theorem eqb_false_to_not_eq: ∀n,m:nat. eqbnat n m = false → n ≠ m.
#n #m @(eqbnat_elim n m) /2/ qed. *)

theorem eq_to_eqbnat_true: ∀n,m:nat.n = m → eqbnat n m = true.
// qed.