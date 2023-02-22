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

include "logic/equality.ma".

include "nat/nat.ma".
include "list/list.ma".

inductive list_x : Type ≝
| nil_x  : list_x
| cons_x : ∀T:Type.∀x:T.list_x → list_x.

let rec mk_prod (l:list_x) ≝
  match l with
  [ nil_x ⇒ Type
  | cons_x T x tl ⇒ ∀y0:T.∀p0:x = y0. mk_prod tl ].
  
let rec appl (l:list_x) : mk_prod l →  Type ≝ 
 match l return λl:list_x.mk_prod l →Type
 with
 [ nil_x ⇒ λT:mk_prod nil_x.T
 | cons_x Ty hd tl ⇒ λT:mk_prod (cons_x Ty hd tl).appl tl (T hd (refl_eq Ty hd)) ].
  
inductive list_xyp : list_x → Type ≝
| nil_xyp  : ∀l.list_xyp l
| cons_xyp : ∀l.∀T:mk_prod l.∀x:appl l T.list_xyp (cons_x ? x l) → list_xyp l.

(* let rec tau (l:list_x) (w:list_xyp l) on w: Type ≝ 
 match w with
 [ nil_xyp _ ⇒ Type
 | cons_xyp l' T' x' w' ⇒ 
     ∀y:appl l' T'.∀p:x' = y.
     tau (cons_x ? y l') w' ].

eval normalize on (
  ∀T0:Type.
  ∀a0:T0.
  ∀T1:∀x0:T0. a0=x0 → Type.
  ∀a1:T1 a0 (refl_eq ? a0).
tau ? (cons_xyp nil_x T0 a0 (cons_xyp (cons_x T0 a0 nil_x) T1 a1 (nil_xyp ?))) Type).

inductive index_list (T: nat → Type): ∀m,n:nat.Type ≝
| il_s : ∀n.T n → index_list T n n
| il_c : ∀m,n. T m → index_list T (S m) n → index_list T m n.

lemma down_il : ∀T:nat → Type.∀m,n.∀l: index_list T m n.∀f:(∀p. T (S p) → T p).
                ∀m',n'.S m' = m → S n' = n → index_list T m' n'.
intros 5;elim i
[destruct;apply il_s;apply f;assumption
|apply il_c
 [apply f;rewrite > H;assumption
 |apply f1
  [rewrite > H;reflexivity
  |assumption]]]
qed. *)

definition R1 ≝ eq_rect'.

definition R2 :
  ∀T0:Type.
  ∀a0:T0.
  ∀T1:∀x0:T0. a0=x0 → Type.
  ∀a1:T1 a0 (refl_eq ? a0).
  ∀T2:∀x0:T0. ∀p0:a0=x0. ∀x1:T1 x0 p0. R1 ??? a1 ? p0 = x1 → Type.
  ∀a2:T2 a0 (refl_eq ? a0) a1 (refl_eq ? a1).  
  ∀b0:T0.
  ∀e0:a0 = b0.
  ∀b1: T1 b0 e0.
  ∀e1:R1 ??? a1 ? e0 = b1.
  T2 b0 e0 b1 e1.
intros (T0 a0 T1 a1 T2 a2);
apply (eq_rect' ????? e1);
apply (R1 ?? ? ?? e0);
simplify;assumption;
qed.

definition R3 :
  ∀T0:Type.
  ∀a0:T0.
  ∀T1:∀x0:T0. a0=x0 → Type.
  ∀a1:T1 a0 (refl_eq ? a0).
  ∀T2:∀x0:T0. ∀p0:a0=x0. ∀x1:T1 x0 p0. R1 ??? a1 ? p0 = x1 → Type.
  ∀a2:T2 a0 (refl_eq ? a0) a1 (refl_eq ? a1).
  ∀T3:∀x0:T0. ∀p0:a0=x0. ∀x1:T1 x0 p0.∀p1:R1 ??? a1 ? p0 = x1.
      ∀x2:T2 x0 p0 x1 p1.R2 T0 a0 T1 a1 T2 a2 ? p0 ? p1 = x2→ Type.
  ∀a3:T3 a0 (refl_eq ? a0) a1 (refl_eq ? a1) a2 (refl_eq ? a2).
  ∀b0:T0.
  ∀e0:a0 = b0.
  ∀b1: T1 b0 e0.
  ∀e1:R1 ??? a1 ? e0 = b1.
  ∀b2: T2 b0 e0 b1 e1.
  ∀e2:R2 T0 a0 T1 a1 T2 a2 ? e0 ? e1 = b2.
  T3 b0 e0 b1 e1 b2 e2.       
intros (T0 a0 T1 a1 T2 a2 T3 a3);
apply (eq_rect' ????? e2);
apply (R2 ?? ? ???? e0 ? e1);
simplify;assumption;
qed.

(*let rec iter_type n (l1 : lista dei nomi fin qui creati) (l2: lista dei tipi dipendenti da applicare) ≝
  match n with
  [ O ⇒ Type
  | S p ⇒ match l2 with
    [ nil ⇒ Type (* dummy *)
    | cons T tl ⇒ ∀t:app_type_list l1 T.iter_type p (l1@[t]) tl ]].
  
lemma app_type_list : ∀l:list Type.∀T:iter_type l.Type.
intro;
elim l
[apply i
|simplify in i;apply F;apply i;apply a]
qed.

definition type_list_cons : ∀l:list Type.iter_type l → list Type ≝
  λl,T.app_type_list l T :: l.

let rec build_dep_type n T acc ≝
  match n with
  [ O ⇒ acc
  | S p ⇒ 
Type → list Type → Type.
  λta,l.match l *)

inductive II : nat → Type ≝
| k1 : ∀n.II n
| k2 : ∀n.II n
| k3 : ∀n,m. II n → II m → II O.

inductive JJ : nat → Type ≝
| h1 : JJ O
| h2 : JJ (S O)
| h3 : ∀n,m. JJ n → JJ m → JJ O.

(*

lemma test: h3 ?? h1 h2 = h3 ?? h2 h1 → True.
intro;
letin f ≝ (λx.S (S x));
cut (∃a,b.S a = f b);
[decompose;cut (S (S a) = S (f a1))
 [|clear H;destruct;
cut (∀→ True)
[elim Hcut;
qed.
*)

definition IId : ∀n,m.II m → II n → Type ≝
 λa,b,x,y.match x with
 [ k1 n ⇒ match y with
   [ k1 n' ⇒ ∀P:Type.(n = n' → P) → P
   | k2 n' ⇒ ∀P:Type.P
   | k3 m n p' q' ⇒ ∀P:Type.P ] 
 | k2 n ⇒ match y with
   [ k1 n' ⇒ ∀P:Type.P
   | k2 n' ⇒ ∀P:Type.(n = n' → P) → P
   | k3 m' n' p' q' ⇒ ∀P:Type.P ]
 | k3 m n p q ⇒ match y with
   [ k1 n' ⇒ ∀P:Type.P
   | k2 n' ⇒ ∀P:Type.P
   | k3 m' n' p' q' ⇒ ∀P:Type.(∀e1:m = m'.∀e2:n = n'. (eq_rect ??? p ? e1) = p' 
     → (eq_rect ??? q ? e2) = q' → P) → P ]].

lemma IInc : ∀n,x,y.x = y → IId n n x y.
intros;rewrite > H;elim y;simplify;intros;
[apply f;reflexivity
|apply f;reflexivity
|apply f;reflexivity]
qed.

axiom daemon:False.

lemma IIconflict: ∀c,d.
  k3 c d (k1 c) (k2 d) = k3 d c (k2 d) (k1 c) → False.
intros;apply (IInc ??? H);clear H;intro;
apply (eq_rect' ?? (λx.λp.∀e2:x=c.eq_rect ℕ c II (k1 c) x p=k2 x→eq_rect nat x II (k2 x) c e2 = k1 c → False) ?? e1);
simplify;intros;apply (IInc ??? H);

inductive I1 : nat → Type ≝
| kI1 : ∀n.I1 n.

inductive I2 : ∀n:nat.I1 n → Type ≝
| kI2 : ∀n,i.I2 n i.

inductive I3 : Type ≝
| kI3 : ∀x1:nat.∀x2:I1 x1.∀x3:I2 x1 x2.I3.

(* lemma idfof : (∀t1,t2,t3,u1,u2,u3.((λy1:ℕ.λp1:t1=y1.λy2:I1 y1.λp2:R1 ℕ t1 (λy1:ℕ.λp1:t1=y1.I1 y1) t2 y1 p1 =y2.
       λy3:I2 y1 y2.λp3:R2 ℕ t1 (λy1:ℕ.λp1:t1=y1.I1 y1) t2 (λy1:ℕ.λp1:t1=y1.λy2:I1 y1.λp2:R1 ℕ t1 (λy1:ℕ.λp1:t1 =y1.I1 y1) t2 y1 p1 =y2.I2 y1 y2) t3 y1 p1 y2 p2 =y3.
                    kI3 y1 y2 y3 =kI3 u1 u2 u3)
t1 (refl_eq ℕ t1) t2 (refl_eq ((λy1:ℕ.λp1:t1=y1.I1 y1) t1 (refl_eq ℕ t1)) t2)
   t3 (refl_eq ((λy1:ℕ.λp1:t1=y1.λy2:I1 y1.λp2:R1 ℕ t1 (λy1:ℕ.λp1:t1=y1.I1 y1) t2 y1 p1 =y2.I2 y1 y2) t1 (refl_eq ℕ t1) t2 (refl_eq ((λy1:ℕ.λp1:t1=y1.I1 y1) t1 (refl_eq ℕ t1)) t2)) t3)
   )
    → True).
simplify; *)

definition I3d : ∀x,y:I3.x = y → Type ≝
λx,y.match x return (λx:I3.x = y → Type) with
[ kI3 x1 x2 x3 ⇒ match y return (λy:I3.kI3 x1 x2 x3 = y → Type) with
  [ kI3 y1 y2 y3 ⇒ 
    λe:kI3 x1 x2 x3 = kI3 y1 y2 y3.
       ∀P:Prop.(∀e1: x1 = y1.
                ∀e2: R1 ?? (λz1,p1.I1 z1) ?? e1 = y2.
                ∀e3: R2 ???? (λz1,p1,z2,p2.I2 z1 z2) x3 ? e1 ? e2 = y3. 
                R3 ?????? 
                (λz1,p1,z2,p2,z3,p3.
                  eq ? (kI3 z1 z2 z3) (kI3 y1 y2 y3)) e y1 e1 y2 e2 y3 e3
                = refl_eq ? (kI3 y1 y2 y3)
                → P) → P]].

definition I3d : ∀x,y:I3.x=y → Type.
intros 2;cases x;cases y;intro;
apply (∀P:Prop.(∀e1: x1 = x3.
                ∀e2: R1 ?? (λy1,p1.I1 y1) ?? e1 = x4.
                ∀e3: R2 ???? (λy1,p1,y2,p2.I2 y1 y2) i ? e1 ? e2 = i1. 
                R3 ?????? 
                (λy1,p1,y2,p2,y3,p3.
                  eq ? (kI3 y1 y2 y3) (kI3 x3 x4 i1)) H x3 e1 x4 e2 i1 e3
                = refl_eq ? (kI3 x3 x4 i1)
                → P) → P);
qed.

(* definition I3d : ∀x,y:nat. x = y → Type ≝
λx,y.
match x 
 return (λx.x = y → Type)
 with
[ O ⇒ match y return (λy.O = y → Type) with
  [ O ⇒ λe:O = O.∀P.P → P
  | S q ⇒ λe: O = S q. ∀P.P]
| S p ⇒ match y return (λy.S p = y → Type) with
  [ O ⇒ λe:S p = O.∀P.P
  | S q ⇒ λe: S p = S q. ∀P.(p = q → P) → P]]. 

definition I3d: 
  ∀x,y:I3. x = y → Type 
  ≝ 
λx,y. 
match x with
[ kI3 t1 t2 (t3:I2 t1 t2) ⇒ match y with
  [ kI3 u1 u2 u3 ⇒ λe:kI3 t1 t2 t3 = kI3 u1 u2 u3.∀P:Type.
    (∀e1: t1 = u1.
     ∀e2: R1 nat t1 (λy1:nat.λp1:y1 = u1.I1 y1) t2 ? e1 = u2.
     ∀e3: R2 nat t1 (λy1,p1.I1 y1) t2 (λy1,p1,y2,p2.I2 y1 y2) t3 ? e1 ? e2 = u3. 
     (* ∀e:  kI3 t1 t2 t3 = kI3 u1 u2 u3.*)
     R3 nat t1 (λy1,p1.I1 y1) t2 (λy1,p1,y2,p2.I2 y1 y2) t3 
        (λy1,p1,y2,p2,y3,p3.eq I3 (kI3 y1 y2 y3) (kI3 u1 u2 u3)) e u1 e1 u2 e2 u3 e3 = refl_eq I3 (kI3 u1 u2 u3)
     → P)
    → P]].

definition I3d: 
  ∀x,y:I3.
    (∀x,y.match x with [ kI3 t1 t2 t3 ⇒
      match y with [ kI3 u1 u2 u3 ⇒ kI3 t1 t2 t3 = kI3 u1 u2 u3]]) → Type 
  ≝ 
λx,y.λe:
   (∀x,y.match x with [ kI3 t1 t2 t3 ⇒
      match y with [ kI3 u1 u2 u3 ⇒ kI3 t1 t2 t3 = kI3 u1 u2 u3]]). 
match x with
[ kI3 t1 t2 (t3:I2 t1 t2) ⇒ match y with
  [ kI3 u1 u2 u3 ⇒ ∀P:Type.
    (∀e1: t1 = u1.
     ∀e2: R1 ?? (λy1,p1.I1 y1) ?? e1 = u2.
     ∀e3: R2 ???? (λy1,p1,y2,p2.I2 y1 y2) t3 ? e1 ? e2 = u3. 
     (* ∀e:  kI3 t1 t2 t3 = kI3 u1 u2 u3.*)
     R3 nat t1 (λy1,p1.I1 y1) t2 (λy1,p1,y2,p2.I2 y1 y2) t3 
        (λy1,p1,y2,p2,y3,p3.eq I3 (kI3 y1 y2 y3) (kI3 u1 u2 u3)) (e (kI3 t1 t2 t3) (kI3 u1 u2 u3)) u1 e1 u2 e2 u3 e3 = refl_eq ? (kI3 u1 u2 u3)
     → P)
    → P]].*)
     
lemma I3nc : ∀a,b.∀e:a = b. I3d a b e.
intros;apply (R1 ????? e);elim a;whd;intros;apply H;reflexivity;
qed.

(*lemma R1_r : ΠA:Type.Πx:A.ΠP:Πy:A.y=x→Type.P x (refl_eq A x)→Πy:A.Πp:y=x.P y p.
intros;lapply (eq_rect' A x P p y (sym_eq A y x p1));
generalize in match Hletin;
cut (∀p1:y = x.sym_eq ??? (sym_eq ??? p1) = p1)
[rewrite > Hcut;intro;assumption
|intro;apply (eq_rect' ????? p2);simplify;reflexivity]
qed.

definition R2_r :
  ∀T0:Type.
  ∀a0:T0.
  ∀T1:∀x0:T0. x0=a0 → Type.
  ∀a1:T1 a0 (refl_eq ? a0).
  ∀T2:∀x0:T0. ∀p0:x0=a0. ∀x1:T1 x0 p0. x1 = R1_r ??? a1 ? p0 → Type.
  ∀b0:T0.
  ∀e0:b0 = a0.
  ∀b1: T1 b0 e0.
  ∀e1:b1 = R1_r ??? a1 ? e0.
  ∀so:T2 a0 (refl_eq ? a0) a1 (refl_eq ? a1).T2 b0 e0 b1 e1.
intros 8;intros 2 (e1 H);
apply (R1_r ????? e1);
apply (R1_r ?? ? ?? e0);
simplify;assumption;
qed.*)

definition I3prova : ∀a,b,c,d,e,f.∀Heq:kI3 a b c = kI3 d e f.
  ∀P:? → ? → ? → ? → Prop.
  P d e f Heq → 
  P a b c (refl_eq ??).
intros;apply (I3nc ?? Heq);
simplify;intro;
generalize in match H as H;generalize in match Heq as Heq;
generalize in match f as f;generalize in match e as e;
clear H Heq f e;
apply (R1 ????? e1);intros 5;simplify in e2;
generalize in match H as H;generalize in match Heq as Heq;
generalize in match f as f;
clear H Heq f;
apply (R1 ????? e2);intros 4;simplify in e3;
generalize in match H as H;generalize in match Heq as Heq;
clear H Heq;
apply (R1 ????? e3);intros;simplify in H1;
apply (R1 ????? H1);
assumption;
qed.


definition KKd : ∀m,n,p,q.KK m n → KK p q → Type ≝
 λa,b,c,d,x,y.match x with
 [ c1 n ⇒ match y with
   [ c1 n' ⇒ ∀P:Type.(n = n' → P) → P
   | c2 n' ⇒ ∀P:Type.P
   | c3 m' n' p' q' h' i' ⇒ ∀P:Type.P ] 
 | c2 n ⇒ match y with
   [ c1 n' ⇒ ∀P:Type.P
   | c2 n' ⇒ ∀P:Type.(n = n' → P) → P
   | c3 m' n' p' q' h' i' ⇒ ∀P:Type.P ]
 | c3 m n p q h i ⇒ match y with
   [ c1 n' ⇒ ∀P:Type.P
   | c2 n' ⇒ ∀P:Type.P
   | c3 m' n' p' q' h' i' ⇒ 
     ∀P:Type.(∀e1:m = m'.∀e2:n = n'. ∀e3:p = p'. ∀e4:q = q'. 
     (eq_rect ?? (λm.KK m n') (eq_rect ?? (λn.KK m n) h n' e2) m' e1) = h' 
     → (eq_rect ?? (λp.KK p q') (eq_rect ?? (λq.KK p q) i ? e4) ? e3) = i' → P) → P ]].
     
lemma KKnc : ∀a,b,e,f.e = f → KKd a b a b e f.
intros;rewrite > H;elim f;simplify;intros;apply f1;reflexivity;
qed.

