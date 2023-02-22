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

include "arithmetics/nat.ma".

ninductive compare : Type[0] ≝
| LT : compare
| EQ : compare
| GT : compare.

ndefinition compare_invert: compare → compare ≝
  λc.match c with
      [ LT ⇒ GT
      | EQ ⇒ EQ
      | GT ⇒ LT ].

nlet rec nat_compare n m: compare ≝
match n with
[ O ⇒ match m with 
      [ O ⇒ EQ
      | (S q) ⇒ LT ]
| S p ⇒ match m with 
      [ O ⇒ GT
      | S q ⇒ nat_compare p q]].

ntheorem nat_compare_n_n: ∀n. nat_compare n n = EQ.
#n;nelim n
##[//
##|#m;#IH;nnormalize;//]
nqed.

ntheorem nat_compare_S_S: ∀n,m:nat.nat_compare n m = nat_compare (S n) (S m).
//;
nqed.

ntheorem nat_compare_pred_pred: 
  ∀n,m.O < n → O < m → nat_compare n m = nat_compare (pred n) (pred m).
#n;#m;#Hn;#Hm;
napply (lt_O_n_elim n Hn);
napply (lt_O_n_elim m Hm);
#p;#q;//;
nqed.

ntheorem nat_compare_to_Prop: 
  ∀n,m.match (nat_compare n m) with
    [ LT ⇒ n < m
    | EQ ⇒ n = m
    | GT ⇒ m < n ].
#n;#m;
napply (nat_elim2 (λn,m.match (nat_compare n m) with
  [ LT ⇒ n < m
  | EQ ⇒ n = m
  | GT ⇒ m < n ]) ?????) (* FIXME: don't want to put all these ?, especially when … does not work! *)
##[##1,2:#n1;ncases n1;//;
##|#n1;#m1;nnormalize;ncases (nat_compare n1 m1);
   ##[##1,3:nnormalize;#IH;napply le_S_S;//;
   ##|nnormalize;#IH;nrewrite > IH;//]
nqed.

ntheorem nat_compare_n_m_m_n: 
  ∀n,m:nat.nat_compare n m = compare_invert (nat_compare m n).
#n;#m;
napply (nat_elim2 (λn,m. nat_compare n m = compare_invert (nat_compare m n)))
##[##1,2:#n1;ncases n1;//;
##|#n1;#m1;#IH;nnormalize;napply IH]
nqed.
     
ntheorem nat_compare_elim : 
  ∀n,m. ∀P:compare → Prop.
    (n < m → P LT) → (n=m → P EQ) → (m < n → P GT) → P (nat_compare n m).
#n;#m;#P;#Hlt;#Heq;#Hgt;
ncut (match (nat_compare n m) with
    [ LT ⇒ n < m
    | EQ ⇒ n=m
    | GT ⇒ m < n] →
  P (nat_compare n m))
##[ncases (nat_compare n m);
   ##[napply Hlt
   ##|napply Heq
   ##|napply Hgt]
##|#Hcut;napply Hcut;//;
nqed.

ninductive cmp_cases (n,m:nat) : CProp[0] ≝
  | cmp_le : n ≤ m → cmp_cases n m
  | cmp_gt : m < n → cmp_cases n m.

ntheorem lt_to_le : ∀n,m:nat. n < m → n ≤ m.
(* sic 
#n;#m;#H;nelim H
##[//
##|/2/] *)
/2/; nqed.

nlemma cmp_nat: ∀n,m.cmp_cases n m.
#n;#m; nlapply (nat_compare_to_Prop n m);
ncases (nat_compare n m);nnormalize; /3/; 
nqed.
