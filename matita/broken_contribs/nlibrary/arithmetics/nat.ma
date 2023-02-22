(**************************************************************************)
(*       ___	                                                          *)
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

include "hints_declaration.ma".
include "basics/functions.ma".
include "basics/eq.ma".

ninductive nat : Type ≝
  | O : nat
  | S : nat → nat.
  
interpretation "Natural numbers" 'N = nat.

alias num (instance 0) = "nnatural number".

(*
nrecord pos : Type ≝
 {n:>nat; is_pos: n ≠ 0}.

ncoercion nat_to_pos: ∀n:nat. n ≠0 →pos ≝ mk_pos on 
*)

(* default "natural numbers" cic:/matita/ng/arithmetics/nat/nat.ind.
*)

ndefinition pred ≝
 λn. match n with [ O ⇒ O | S p ⇒ p].

ntheorem pred_Sn : ∀n. n = pred (S n).
//; nqed.

ntheorem injective_S : injective nat nat S.
//; nqed.

(*
ntheorem inj_S : \forall n,m:nat.(S n)=(S m) \to n=m.
//. nqed. *)

ntheorem not_eq_S: ∀n,m:nat. n ≠ m → S n ≠ S m.
/3/; nqed.

ndefinition not_zero: nat → Prop ≝
 λn: nat. match n with
  [ O ⇒ False | (S p) ⇒ True ].

ntheorem not_eq_O_S : ∀n:nat. O ≠ S n.
#n; napply nmk; #eqOS; nchange with (not_zero O); nrewrite > eqOS; //.
nqed.

ntheorem not_eq_n_Sn: ∀n:nat. n ≠ S n.
#n; nelim n;/2/; nqed.

ntheorem nat_case:
 ∀n:nat.∀P:nat → Prop. 
  (n=O → P O) → (∀m:nat. (n=(S m) → P (S m))) → P n.
#n; #P; nelim n; /2/; nqed.

ntheorem nat_elim2 :
 ∀R:nat → nat → Prop.
  (∀n:nat. R O n) 
  → (∀n:nat. R (S n) O)
  → (∀n,m:nat. R n m → R (S n) (S m))
  → ∀n,m:nat. R n m.
#R; #ROn; #RSO; #RSS; #n; nelim n;//;
#n0; #Rn0m; #m; ncases m;/2/; nqed.

ntheorem decidable_eq_nat : ∀n,m:nat.decidable (n=m).
napply nat_elim2; #n;
 ##[ ncases n; /2/;
 ##| /3/;
 ##| #m; #Hind; ncases Hind;/3/;
 ##]
nqed. 

(*************************** plus ******************************)

nlet rec plus n m ≝ 
 match n with 
 [ O ⇒ m
 | S p ⇒ S (plus p m) ].

interpretation "natural plus" 'plus x y = (plus x y).

ntheorem plus_O_n: ∀n:nat. n = 0+n.
//; nqed.

(*
ntheorem plus_Sn_m: ∀n,m:nat. S (n + m) = S n + m.
//; nqed.
*)

ntheorem plus_n_O: ∀n:nat. n = n+0.
#n; nelim n; nnormalize; //; nqed.

ntheorem plus_n_Sm : ∀n,m:nat. S (n+m) = n + S m.
#n; nelim n; nnormalize; //; nqed.

(*
ntheorem plus_Sn_m1: ∀n,m:nat. S m + n = n + S m.
#n; nelim n; nnormalize; //; nqed.
*)

(* deleterio?
ntheorem plus_n_1 : ∀n:nat. S n = n+1.
//; nqed.
*)

ntheorem symmetric_plus: symmetric ? plus.
#n; nelim n; nnormalize; //; nqed. 

ntheorem associative_plus : associative nat plus.
#n; nelim n; nnormalize; //; nqed.

ntheorem assoc_plus1: ∀a,b,c. c + (b + a) = b + c + a.
//; nqed. 

ntheorem injective_plus_r: ∀n:nat.injective nat nat (λm.n+m).
#n; nelim n; nnormalize; /3/; nqed.

(* ntheorem inj_plus_r: \forall p,n,m:nat. p+n = p+m \to n=m
\def injective_plus_r. 

ntheorem injective_plus_l: ∀m:nat.injective nat nat (λn.n+m).
/2/; nqed. *)

(* ntheorem inj_plus_l: \forall p,n,m:nat. n+p = m+p \to n=m
\def injective_plus_l. *)

(*************************** times *****************************)

nlet rec times n m ≝ 
 match n with 
 [ O ⇒ O
 | S p ⇒ m+(times p m) ].

interpretation "natural times" 'times x y = (times x y).

ntheorem times_Sn_m: ∀n,m:nat. m+n*m = S n*m.
//; nqed.

ntheorem times_O_n: ∀n:nat. O = O*n.
//; nqed.

ntheorem times_n_O: ∀n:nat. O = n*O.
#n; nelim n; //; nqed.

ntheorem times_n_Sm : ∀n,m:nat. n+(n*m) = n*(S m).
#n; nelim n; nnormalize; //; nqed.

ntheorem symmetric_times : symmetric nat times. 
#n; nelim n; nnormalize; //; nqed. 

(* variant sym_times : \forall n,m:nat. n*m = m*n \def
symmetric_times. *)

ntheorem distributive_times_plus : distributive nat times plus.
#n; nelim n; nnormalize; //; nqed.

ntheorem distributive_times_plus_r :
  ∀a,b,c:nat. (b+c)*a = b*a + c*a.
//; nqed. 

ntheorem associative_times: associative nat times.
#n; nelim n; nnormalize; //; nqed.

nlemma times_times: ∀x,y,z. x*(y*z) = y*(x*z).
//; nqed. 

(* ci servono questi risultati? 
ntheorem times_O_to_O: ∀n,m:nat.n*m=O → n=O ∨ m=O.
napply nat_elim2; /2/; 
#n; #m; #H; nnormalize; #H1; napply False_ind;napply not_eq_O_S;
//; nqed.
  
ntheorem times_n_SO : ∀n:nat. n = n * S O.
#n; //; nqed.

ntheorem times_SSO_n : ∀n:nat. n + n = (S(S O)) * n.
nnormalize; //; nqed.

nlemma times_SSO: \forall n.(S(S O))*(S n) = S(S((S(S O))*n)).
//; nqed.

ntheorem or_eq_eq_S: \forall n.\exists m. 
n = (S(S O))*m \lor n = S ((S(S O))*m).
#n; nelim n;
  ##[@; /2/;
  ##|#a; #H; nelim H; #b;#or;nelim or;#aeq;
    ##[@ b; @ 2; //;
    ##|@ (S b); @ 1; /2/;
    ##]
nqed.
*)

(******************** ordering relations ************************)

ninductive le (n:nat) : nat → Prop ≝
  | le_n : le n n
  | le_S : ∀ m:nat. le n m → le n (S m).

interpretation "natural 'less or equal to'" 'leq x y = (le x y).

interpretation "natural 'neither less nor equal to'" 'nleq x y = (Not (le x y)).

ndefinition lt: nat → nat → Prop ≝
λn,m:nat. S n ≤ m.

interpretation "natural 'less than'" 'lt x y = (lt x y).

interpretation "natural 'not less than'" 'nless x y = (Not (lt x y)).

(* nlemma eq_lt: ∀n,m. (n < m) = (S n ≤ m).
//; nqed. *)

ndefinition ge: nat → nat → Prop ≝
λn,m:nat.m ≤ n.

interpretation "natural 'greater or equal to'" 'geq x y = (ge x y).

ndefinition gt: nat → nat → Prop ≝
λn,m:nat.m<n.

interpretation "natural 'greater than'" 'gt x y = (gt x y).

interpretation "natural 'not greater than'" 'ngtr x y = (Not (gt x y)).

ntheorem transitive_le : transitive nat le.
#a; #b; #c; #leab; #lebc;nelim lebc;/2/;
nqed.

(*
ntheorem trans_le: \forall n,m,p:nat. n \leq m \to m \leq p \to n \leq p
\def transitive_le. *)


ntheorem transitive_lt: transitive nat lt.
#a; #b; #c; #ltab; #ltbc;nelim ltbc;/2/;nqed.

(*
theorem trans_lt: \forall n,m,p:nat. lt n m \to lt m p \to lt n p
\def transitive_lt. *)

ntheorem le_S_S: ∀n,m:nat. n ≤ m → S n ≤ S m.
#n; #m; #lenm; nelim lenm; /2/; nqed.

ntheorem le_O_n : ∀n:nat. O ≤ n.
#n; nelim n; /2/; nqed.

ntheorem le_n_Sn : ∀n:nat. n ≤ S n.
/2/; nqed.

ntheorem le_pred_n : ∀n:nat. pred n ≤ n.
#n; nelim n; //; nqed.

(* XXX global problem 
nlemma my_trans_le : ∀x,y,z:nat.x ≤ y → y ≤ z → x ≤ z. 
napply transitive_le.
nqed. *)

ntheorem monotonic_pred: monotonic ? le pred.
#n; #m; #lenm; nelim lenm; /2/;nqed.

ntheorem le_S_S_to_le: ∀n,m:nat. S n ≤ S m → n ≤ m.
/2/; nqed.

(* this are instances of the le versions 
ntheorem lt_S_S_to_lt: ∀n,m. S n < S m → n < m.
/2/; nqed. 

ntheorem lt_to_lt_S_S: ∀n,m. n < m → S n < S m.
/2/; nqed. *)

ntheorem lt_to_not_zero : ∀n,m:nat. n < m → not_zero m.
#n; #m; #Hlt; nelim Hlt;//; nqed.

(* lt vs. le *)
ntheorem not_le_Sn_O: ∀ n:nat. S n ≰ O.
#n; napply nmk; #Hlen0; napply (lt_to_not_zero ?? Hlen0); nqed.

ntheorem not_le_to_not_le_S_S: ∀ n,m:nat. n ≰ m → S n ≰ S m.
/3/; nqed.

ntheorem not_le_S_S_to_not_le: ∀ n,m:nat. S n ≰ S m → n ≰ m.
/3/; nqed.

ntheorem decidable_le: ∀n,m. decidable (n≤m).
napply nat_elim2; #n; /2/;
#m; *; /3/; nqed.

ntheorem decidable_lt: ∀n,m. decidable (n < m).
#n; #m; napply decidable_le ; nqed.

ntheorem not_le_Sn_n: ∀n:nat. S n ≰ n.
#n; nelim n; /2/; nqed.

(* this is le_S_S_to_le
ntheorem lt_S_to_le: ∀n,m:nat. n < S m → n ≤ m.
/2/; nqed.
*)

ntheorem not_le_to_lt: ∀n,m. n ≰ m → m < n.
napply nat_elim2; #n;
 ##[#abs; napply False_ind;/2/;
 ##|/2/;
 ##|#m;#Hind;#HnotleSS; napply le_S_S;/3/;
 ##]
nqed.

ntheorem lt_to_not_le: ∀n,m. n < m → m ≰ n.
#n; #m; #Hltnm; nelim Hltnm;/3/; nqed.

ntheorem not_lt_to_le: ∀n,m:nat. n ≮ m → m ≤ n.
/4/; nqed.

(*
#n; #m; #Hnlt; napply le_S_S_to_le;/2/;
(* something strange here: /2/ fails *)
napply not_le_to_lt; napply Hnlt; nqed. *)

ntheorem le_to_not_lt: ∀n,m:nat. n ≤ m → m ≮ n.
#n; #m; #H;napply lt_to_not_le; /2/; (* /3/ *) nqed.

(* lt and le trans *)

ntheorem lt_to_le_to_lt: ∀n,m,p:nat. n < m → m ≤ p → n < p.
#n; #m; #p; #H; #H1; nelim H1; /2/; nqed.

ntheorem le_to_lt_to_lt: ∀n,m,p:nat. n ≤ m → m < p → n < p.
#n; #m; #p; #H; nelim H; /3/; nqed.

ntheorem lt_S_to_lt: ∀n,m. S n < m → n < m.
/2/; nqed.

ntheorem ltn_to_ltO: ∀n,m:nat. n < m → O < m.
/2/; nqed.

(*
theorem lt_SO_n_to_lt_O_pred_n: \forall n:nat.
(S O) \lt n \to O \lt (pred n).
intros.
apply (ltn_to_ltO (pred (S O)) (pred n) ?).
 apply (lt_pred (S O) n);
 [ apply (lt_O_S O) 
 | assumption
 ]
qed. *)

ntheorem lt_O_n_elim: ∀n:nat. O < n → 
  ∀P:nat → Prop.(∀m:nat.P (S m)) → P n.
#n; nelim n; //; #abs; napply False_ind;/2/;
nqed.

(*
theorem lt_pred: \forall n,m. 
  O < n \to n < m \to pred n < pred m. 
apply nat_elim2
  [intros.apply False_ind.apply (not_le_Sn_O ? H)
  |intros.apply False_ind.apply (not_le_Sn_O ? H1)
  |intros.simplify.unfold.apply le_S_S_to_le.assumption
  ]
qed.

theorem S_pred: \forall n:nat.lt O n \to eq nat n (S (pred n)).
intro.elim n.apply False_ind.exact (not_le_Sn_O O H).
apply eq_f.apply pred_Sn.
qed.

theorem le_pred_to_le:
 ∀n,m. O < m → pred n ≤ pred m → n ≤ m.
intros 2;
elim n;
[ apply le_O_n
| simplify in H2;
  rewrite > (S_pred m);
  [ apply le_S_S;
    assumption
  | assumption
  ]
].
qed.

*)

(* le to lt or eq *)
ntheorem le_to_or_lt_eq: ∀n,m:nat. n ≤ m → n < m ∨ n = m.
#n; #m; #lenm; nelim lenm; /3/; nqed.

(* not eq *)
ntheorem lt_to_not_eq : ∀n,m:nat. n < m → n ≠ m.
#n; #m; #H; napply not_to_not;/2/; nqed.

(*not lt 
ntheorem eq_to_not_lt: ∀a,b:nat. a = b → a ≮ b.
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
intros;
unfold Not;
intro;
unfold lt in H;
unfold lt in H1;
generalize in match (le_S_S ? ? H);
intro;
generalize in match (transitive_le ? ? ? H2 H1);
intro;
apply (not_le_Sn_n ? H3).
qed. *)

ntheorem not_eq_to_le_to_lt: ∀n,m. n≠m → n≤m → n<m.
#n; #m; #Hneq; #Hle; ncases (le_to_or_lt_eq ?? Hle); //;
#Heq; /3/; nqed.
(*
nelim (Hneq Heq); nqed. *)

(* le elimination *)
ntheorem le_n_O_to_eq : ∀n:nat. n ≤ O → O=n.
#n; ncases n; //; #a ; #abs;
napply False_ind; /2/;nqed.

ntheorem le_n_O_elim: ∀n:nat. n ≤ O → ∀P: nat →Prop. P O → P n.
#n; ncases n; //; #a; #abs; 
napply False_ind; /2/; nqed. 

ntheorem le_n_Sm_elim : ∀n,m:nat.n ≤ S m → 
∀P:Prop. (S n ≤ S m → P) → (n=S m → P) → P.
#n; #m; #Hle; #P; nelim Hle; /3/; nqed.

(* le and eq *)

ntheorem le_to_le_to_eq: ∀n,m. n ≤ m → m ≤ n → n = m.
napply nat_elim2; /4/;
nqed. 

ntheorem lt_O_S : ∀n:nat. O < S n.
/2/; nqed.

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
intros;
unfold lt in H1;
generalize in match (le_S_S_to_le ? ? H1);
intro;
apply antisym_le;
assumption.
qed.
*)

(* well founded induction principles *)

ntheorem nat_elim1 : ∀n:nat.∀P:nat → Prop. 
(∀m.(∀p. p < m → P p) → P m) → P n.
#n; #P; #H; 
ncut (∀q:nat. q ≤ n → P q);/2/;
nelim n; 
 ##[#q; #HleO; (* applica male *) 
    napply (le_n_O_elim ? HleO);
    napply H; #p; #ltpO;
    napply False_ind; /2/; (* 3 *)
 ##|#p; #Hind; #q; #HleS; 
    napply H; #a; #lta; napply Hind;
    napply le_S_S_to_le;/2/;
 ##]
nqed.

(* some properties of functions *)
(*
definition increasing \def \lambda f:nat \to nat. 
\forall n:nat. f n < f (S n).

theorem increasing_to_monotonic: \forall f:nat \to nat.
increasing f \to monotonic nat lt f.
unfold monotonic.unfold lt.unfold increasing.unfold lt.intros.elim H1.apply H.
apply (trans_le ? (f n1)).
assumption.apply (trans_le ? (S (f n1))).
apply le_n_Sn.
apply H.
qed.

theorem le_n_fn: \forall f:nat \to nat. (increasing f) 
\to \forall n:nat. n \le (f n).
intros.elim n.
apply le_O_n.
apply (trans_le ? (S (f n1))).
apply le_S_S.apply H1.
simplify in H. unfold increasing in H.unfold lt in H.apply H.
qed.

theorem increasing_to_le: \forall f:nat \to nat. (increasing f) 
\to \forall m:nat. \exists i. m \le (f i).
intros.elim m.
apply (ex_intro ? ? O).apply le_O_n.
elim H1.
apply (ex_intro ? ? (S a)).
apply (trans_le ? (S (f a))).
apply le_S_S.assumption.
simplify in H.unfold increasing in H.unfold lt in H.
apply H.
qed.

theorem increasing_to_le2: \forall f:nat \to nat. (increasing f) 
\to \forall m:nat. (f O) \le m \to 
\exists i. (f i) \le m \land m <(f (S i)).
intros.elim H1.
apply (ex_intro ? ? O).
split.apply le_n.apply H.
elim H3.elim H4.
cut ((S n1) < (f (S a)) \lor (S n1) = (f (S a))).
elim Hcut.
apply (ex_intro ? ? a).
split.apply le_S. assumption.assumption.
apply (ex_intro ? ? (S a)).
split.rewrite < H7.apply le_n.
rewrite > H7.
apply H.
apply le_to_or_lt_eq.apply H6.
qed.
*)

(*********************** monotonicity ***************************)
ntheorem monotonic_le_plus_r: 
∀n:nat.monotonic nat le (λm.n + m).
#n; #a; #b; nelim n; nnormalize; //;
#m; #H; #leab;napply le_S_S; /2/; nqed.

(*
ntheorem le_plus_r: ∀p,n,m:nat. n ≤ m → p + n ≤ p + m
≝ monotonic_le_plus_r. *)

ntheorem monotonic_le_plus_l: 
∀m:nat.monotonic nat le (λn.n + m).
/2/; nqed.

(*
ntheorem le_plus_l: \forall p,n,m:nat. n \le m \to n + p \le m + p
\def monotonic_le_plus_l. *)

ntheorem le_plus: ∀n1,n2,m1,m2:nat. n1 ≤ n2  → m1 ≤ m2 
→ n1 + m1 ≤ n2 + m2.
#n1; #n2; #m1; #m2; #len; #lem; napply (transitive_le ? (n1+m2));
/2/; nqed.

ntheorem le_plus_n :∀n,m:nat. m ≤ n + m.
/2/; nqed. 

nlemma le_plus_a: ∀a,n,m. n ≤ m → n ≤ a + m.
/2/; nqed.

nlemma le_plus_b: ∀b,n,m. n + b ≤ m → n ≤ m.
/2/; nqed.

ntheorem le_plus_n_r :∀n,m:nat. m ≤ m + n.
/2/; nqed.

ntheorem eq_plus_to_le: ∀n,m,p:nat.n=m+p → m ≤ n.
//; nqed.

ntheorem le_plus_to_le: ∀a,n,m. a + n ≤ a + m → n ≤ m.
#a; nelim a; nnormalize; /3/; nqed. 

ntheorem le_plus_to_le_r: ∀a,n,m. n + a ≤ m +a → n ≤ m.
/2/; nqed. 

(* plus & lt *)

ntheorem monotonic_lt_plus_r: 
∀n:nat.monotonic nat lt (λm.n+m).
/2/; nqed.

(*
variant lt_plus_r: \forall n,p,q:nat. p < q \to n + p < n + q \def
monotonic_lt_plus_r. *)

ntheorem monotonic_lt_plus_l: 
∀n:nat.monotonic nat lt (λm.m+n).
/2/; nqed.

(*
variant lt_plus_l: \forall n,p,q:nat. p < q \to p + n < q + n \def
monotonic_lt_plus_l. *)

ntheorem lt_plus: ∀n,m,p,q:nat. n < m → p < q → n + p < m + q.
#n; #m; #p; #q; #ltnm; #ltpq;
napply (transitive_lt ? (n+q));/2/; nqed.

ntheorem lt_plus_to_lt_l :∀n,p,q:nat. p+n < q+n → p<q.
/2/; nqed.

ntheorem lt_plus_to_lt_r :∀n,p,q:nat. n+p < n+q → p<q.
/2/; nqed.

(*
ntheorem le_to_lt_to_lt_plus: ∀a,b,c,d:nat.
a ≤ c → b < d → a + b < c+d.
(* bello /2/ un po' lento *)
#a; #b; #c; #d; #leac; #lebd; 
nnormalize; napplyS le_plus; //; nqed.
*)

(* times *)
ntheorem monotonic_le_times_r: 
∀n:nat.monotonic nat le (λm. n * m).
#n; #x; #y; #lexy; nelim n; nnormalize;//;(* lento /2/;*)
#a; #lea; napply le_plus; //;
nqed.

(*
ntheorem le_times_r: \forall p,n,m:nat. n \le m \to p*n \le p*m
\def monotonic_le_times_r. *)

(*
ntheorem monotonic_le_times_l: 
∀m:nat.monotonic nat le (λn.n*m).
/2/; nqed.
*)

(*
theorem le_times_l: \forall p,n,m:nat. n \le m \to n*p \le m*p
\def monotonic_le_times_l. *)

ntheorem le_times: ∀n1,n2,m1,m2:nat. 
n1 ≤ n2  → m1 ≤ m2 → n1*m1 ≤ n2*m2.
#n1; #n2; #m1; #m2; #len; #lem; 
napply (transitive_le ? (n1*m2)); (* /2/ slow *)
 ##[ napply monotonic_le_times_r;//; 
 ##| napplyS monotonic_le_times_r;//;
 ##]
nqed.

(* interesssante *)
ntheorem lt_times_n: ∀n,m:nat. O < n → m ≤ n*m.
#n; #m; #H; /2/; nqed.

ntheorem le_times_to_le: 
∀a,n,m. O < a → a * n ≤ a * m → n ≤ m.
#a; napply nat_elim2; nnormalize;
  ##[//;
  ##|#n; #H1; #H2; 
     napply (transitive_le ? (a*S n));/2/;
  ##|#n; #m; #H; #lta; #le;
     napply le_S_S; napply H; /2/;
  ##]
nqed.

ntheorem le_S_times_2: ∀n,m.O < m → n ≤ m → S n ≤ 2*m.
#n; #m; #posm; #lenm;  (* interessante *)
napplyS (le_plus n m); //; nqed.

(* times & lt *)
(*
ntheorem lt_O_times_S_S: ∀n,m:nat.O < (S n)*(S m).
intros.simplify.unfold lt.apply le_S_S.apply le_O_n.
qed. *)

(*
ntheorem lt_times_eq_O: \forall a,b:nat.
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
ntheorem monotonic_lt_times_r: 
∀n:nat.monotonic nat lt (λm.(S n)*m).
/2/; 
simplify.
intros.elim n.
simplify.rewrite < plus_n_O.rewrite < plus_n_O.assumption.
apply lt_plus.assumption.assumption.
qed. *)

ntheorem monotonic_lt_times_l: 
  ∀c:nat. O < c → monotonic nat lt (λt.(t*c)).
#c; #posc; #n; #m; #ltnm;
nelim ltnm; nnormalize;
  ##[/2/; 
  ##|#a; #_; #lt1; napply (transitive_le ??? lt1);//;
  ##]
nqed.

ntheorem monotonic_lt_times_r: 
  ∀c:nat. O < c → monotonic nat lt (λt.(c*t)).
/2/; nqed.

ntheorem lt_to_le_to_lt_times: 
∀n,m,p,q:nat. n < m → p ≤ q → O < q → n*p < m*q.
#n; #m; #p; #q; #ltnm; #lepq; #posq;
napply (le_to_lt_to_lt ? (n*q));
  ##[napply monotonic_le_times_r;//;
  ##|napply monotonic_lt_times_l;//;
  ##]
nqed.

ntheorem lt_times:∀n,m,p,q:nat. n<m → p<q → n*p < m*q.
#n; #m; #p; #q; #ltnm; #ltpq;
napply lt_to_le_to_lt_times;/2/;
nqed.

ntheorem lt_times_n_to_lt_l: 
∀n,p,q:nat. p*n < q*n → p < q.
#n; #p; #q; #Hlt;
nelim (decidable_lt p q);//;
#nltpq; napply False_ind; 
napply (absurd ? ? (lt_to_not_le ? ? Hlt));
napplyS monotonic_le_times_r;/2/;
nqed.

ntheorem lt_times_n_to_lt_r: 
∀n,p,q:nat. n*p < n*q → p < q.
/2/; nqed.

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

nlet rec minus n m ≝ 
 match n with 
 [ O ⇒ O
 | S p ⇒ 
	match m with
	  [ O ⇒ S p
    | S q ⇒ minus p q ]].
        
interpretation "natural minus" 'minus x y = (minus x y).

ntheorem minus_S_S: ∀n,m:nat.S n - S m = n -m.
//; nqed.

ntheorem minus_O_n: ∀n:nat.O=O-n.
#n; ncases n; //; nqed.

ntheorem minus_n_O: ∀n:nat.n=n-O.
#n; ncases n; //; nqed.

ntheorem minus_n_n: ∀n:nat.O=n-n.
#n; nelim n; //; nqed.

ntheorem minus_Sn_n: ∀n:nat. S O = (S n)-n.
#n; nelim n; nnormalize; //; nqed.

ntheorem minus_Sn_m: ∀m,n:nat. m ≤ n → S n -m = S (n-m).
(* qualcosa da capire qui 
#n; #m; #lenm; nelim lenm; napplyS refl_eq. *)
napply nat_elim2; 
  ##[//
  ##|#n; #abs; napply False_ind; /2/ 
  ##|#n; #m; #Hind; #c; napplyS Hind; /2/;
  ##]
nqed.

ntheorem not_eq_to_le_to_le_minus: 
  ∀n,m.n ≠ m → n ≤ m → n ≤ m - 1.
#n; #m; ncases m;//; #m; nnormalize;
#H; #H1; napply le_S_S_to_le;
napplyS (not_eq_to_le_to_lt n (S m) H H1);
nqed.

ntheorem eq_minus_S_pred: ∀n,m. n - (S m) = pred(n -m).
napply nat_elim2; nnormalize; //; nqed.

ntheorem plus_minus:
∀m,n,p:nat. m ≤ n → (n-m)+p = (n+p)-m.
napply nat_elim2; 
  ##[//
  ##|#n; #p; #abs; napply False_ind; /2/;
  ##|nnormalize;/3/;
  ##]
nqed.

ntheorem minus_plus_m_m: ∀n,m:nat.n = (n+m)-m.
#n; #m; napplyS (plus_minus m m n); //; nqed.

ntheorem plus_minus_m_m: ∀n,m:nat.
  m ≤ n → n = (n-m)+m.
#n; #m; #lemn; napplyS sym_eq; 
napplyS (plus_minus m n m); //; nqed.

ntheorem le_plus_minus_m_m: ∀n,m:nat. n ≤ (n-m)+m.
#n; nelim n;
  ##[//
  ##|#a; #Hind; #m; ncases m;//;  
     nnormalize; #n;/2/;  
  ##]
nqed.

ntheorem minus_to_plus :∀n,m,p:nat.
  m ≤ n → n-m = p → n = m+p.
#n; #m; #p; #lemn; #eqp; napplyS plus_minus_m_m; //;
nqed.

ntheorem plus_to_minus :∀n,m,p:nat.n = m+p → n-m = p.
(* /4/ done in 43.5 *)
#n; #m; #p; #eqp; 
napply sym_eq;
napplyS (minus_plus_m_m p m);
nqed.

ntheorem minus_pred_pred : ∀n,m:nat. O < n → O < m → 
pred n - pred m = n - m.
#n; #m; #posn; #posm;
napply (lt_O_n_elim n posn); 
napply (lt_O_n_elim m posm);//.
nqed.

(*
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

ntheorem monotonic_le_minus_l: 
∀p,q,n:nat. q ≤ p → q-n ≤ p-n.
napply nat_elim2; #p; #q;
  ##[#lePO; napply (le_n_O_elim ? lePO);//;
  ##|//;
  ##|#Hind; #n; ncases n;
    ##[//;
    ##|#a; #leSS; napply Hind; /2/;
    ##]
  ##]
nqed.

ntheorem le_minus_to_plus: ∀n,m,p. n-m ≤ p → n≤ p+m.
#n; #m; #p; #lep;
napply transitive_le;
  ##[##|napply le_plus_minus_m_m
  ##|napply monotonic_le_plus_l;//;
  ##]
nqed.

ntheorem le_plus_to_minus: ∀n,m,p. n ≤ p+m → n-m ≤ p.
#n; #m; #p; #lep;
(* bello *)
napplyS monotonic_le_minus_l;//;
(* /2/; *)
nqed.

ntheorem monotonic_le_minus_r: 
∀p,q,n:nat. q ≤ p → n-p ≤ n-q.
#p; #q; #n; #lepq;
napply le_plus_to_minus;
napply (transitive_le ??? (le_plus_minus_m_m ? q));/2/;
nqed.

(*********************** boolean arithmetics ********************) 
include "basics/bool.ma".

nlet rec eqb n m ≝ 
match n with 
  [ O ⇒ match m with [ O ⇒ true | S q ⇒ false] 
  | S p ⇒ match m with [ O ⇒ false | S q ⇒ eqb p q]
  ].
	   
(*
ntheorem eqb_to_Prop: ∀n,m:nat. 
match (eqb n m) with
[ true  \Rightarrow n = m 
| false \Rightarrow n \neq m].
intros.
apply (nat_elim2
(\lambda n,m:nat.match (eqb n m) with
[ true  \Rightarrow n = m 
| false \Rightarrow n \neq m])).
intro.elim n1.
simplify.reflexivity.
simplify.apply not_eq_O_S.
intro.
simplify.unfold Not.
intro. apply (not_eq_O_S n1).apply sym_eq.assumption.
intros.simplify.
generalize in match H.
elim ((eqb n1 m1)).
simplify.apply eq_f.apply H1.
simplify.unfold Not.intro.apply H1.apply inj_S.assumption.
qed.
*)

ntheorem eqb_elim : ∀ n,m:nat.∀ P:bool → Prop.
(n=m → (P true)) → (n ≠ m → (P false)) → (P (eqb n m)). 
napply nat_elim2; 
  ##[#n; ncases n; nnormalize; /3/; 
  ##|nnormalize; /3/;
  ##|nnormalize; /4/; 
  ##] 
nqed.

ntheorem eqb_n_n: ∀n. eqb n n = true.
#n; nelim n; nnormalize; //.
nqed. 

ntheorem eqb_true_to_eq: ∀n,m:nat. eqb n m = true → n = m.
#n; #m; napply (eqb_elim n m);//;
#_; #abs; napply False_ind; /2/;
nqed.

ntheorem eqb_false_to_not_eq: ∀n,m:nat. eqb n m = false → n ≠ m.
#n; #m; napply (eqb_elim n m);/2/;
nqed.

ntheorem eq_to_eqb_true: ∀n,m:nat.
  n = m → eqb n m = true.
//; nqed.

ntheorem not_eq_to_eqb_false: ∀n,m:nat.
  n ≠  m → eqb n m = false.
#n; #m; #noteq; 
napply eqb_elim;//;
#Heq; napply False_ind; /2/; 
nqed.

nlet rec leb n m ≝ 
match n with 
    [ O ⇒ true
    | (S p) ⇒
	match m with 
        [ O ⇒ false
	      | (S q) ⇒ leb p q]].

ntheorem leb_elim: ∀n,m:nat. ∀P:bool → Prop. 
(n ≤ m → P true) → (n ≰ m → P false) → P (leb n m).
napply nat_elim2; nnormalize;
  ##[/2/
  ##|/3/;
  ##|#n; #m; #Hind; #P; #Pt; #Pf; napply Hind;
    ##[#lenm; napply Pt; napply le_S_S;//;
    ##|#nlenm; napply Pf; /2/; 
    ##]
  ##]
nqed.

ntheorem leb_true_to_le:∀n,m.leb n m = true → n ≤ m.
#n; #m; napply leb_elim;
  ##[//;
  ##|#_; #abs; napply False_ind; /2/;
  ##]
nqed.

ntheorem leb_false_to_not_le:∀n,m.
  leb n m = false → n ≰ m.
#n; #m; napply leb_elim;
  ##[#_; #abs; napply False_ind; /2/;
  ##|//;
  ##]
nqed.

ntheorem le_to_leb_true: ∀n,m. n ≤ m → leb n m = true.
#n; #m; napply leb_elim; //;
#H; #H1; napply False_ind; /2/;
nqed.

ntheorem not_le_to_leb_false: ∀n,m. n ≰ m → leb n m = false.
#n; #m; napply leb_elim; //;
#H; #H1; napply False_ind; /2/;
nqed.

ntheorem lt_to_leb_false: ∀n,m. m < n → leb n m = false.
/3/; nqed.

(* serve anche ltb? 
ndefinition ltb ≝λn,m. leb (S n) m.

ntheorem ltb_elim: ∀n,m:nat. ∀P:bool → Prop. 
(n < m → P true) → (n ≮ m → P false) → P (ltb n m).
#n; #m; #P; #Hlt; #Hnlt;
napply leb_elim; /3/; nqed.

ntheorem ltb_true_to_lt:∀n,m.ltb n m = true → n < m.
#n; #m; #Hltb; napply leb_true_to_le; nassumption;
nqed.

ntheorem ltb_false_to_not_lt:∀n,m.
  ltb n m = false → n ≮ m.
#n; #m; #Hltb; napply leb_false_to_not_le; nassumption;
nqed.

ntheorem lt_to_ltb_true: ∀n,m. n < m → ltb n m = true.
#n; #m; #Hltb; napply le_to_leb_true; nassumption;
nqed.

ntheorem le_to_ltb_false: ∀n,m. m \le n → ltb n m = false.
#n; #m; #Hltb; napply lt_to_leb_false; /2/;
nqed. *)

