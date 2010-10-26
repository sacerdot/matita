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

include "logic/connectives.ma".
include "properties/relations.ma".

inductive eq (A: Type[0]) (a: A) : A → CProp[0] ≝
 refl: eq A a a.

lemma eq_rect_Type0_r':
 ∀A.∀a,x.∀p:eq ? x a.∀P: ∀x:A. eq ? x a → Type[0]. P a (refl A a) → P x p.
 #A; #a; #x; #p; cases p; #P; #H; assumption.
qed.

lemma eq_rect_Type0_r:
 ∀A.∀a.∀P: ∀x:A. eq ? x a → Type[0]. P a (refl A a) → ∀x.∀p:eq ? x a.P x p.
 #A; #a; #P; #p; #x0; #p0; apply (eq_rect_Type0_r' ??? p0); assumption.
qed.

lemma eq_rect_CProp0_r':
 ∀A.∀a,x.∀p:eq ? x a.∀P: ∀x:A. eq ? x a → CProp[0]. P a (refl A a) → P x p.
 #A; #a; #x; #p; cases p; #P; #H; assumption.
qed.

lemma eq_rect_CProp0_r:
 ∀A.∀a.∀P: ∀x:A. eq ? x a → CProp[0]. P a (refl A a) → ∀x.∀p:eq ? x a.P x p.
 #A; #a; #P; #p; #x0; #p0; apply (eq_rect_CProp0_r' ??? p0); assumption.
qed.

lemma eq_ind_r :
 ∀A.∀a.∀P: ∀x:A. eq ? x a → Prop. P a (refl A a) → ∀x.∀p:eq ? x a.P x p.
 #A; #a; #P; #p; #x0; #p0; apply (eq_rect_CProp0_r' ??? p0); assumption.
qed.

interpretation "leibnitz's equality" 'eq t x y = (eq t x y).

interpretation "leibnitz's on-equality" 'neq t x y = (Not (eq t x y)).

definition R0 ≝ λT:Type[0].λt:T.t.
  
definition R1 ≝ eq_rect_Type0.

definition R2 :
  ∀T0:Type[0].
  ∀a0:T0.
  ∀T1:∀x0:T0. a0=x0 → Type[0].
  ∀a1:T1 a0 (refl ? a0).
  ∀T2:∀x0:T0. ∀p0:a0=x0. ∀x1:T1 x0 p0. R1 ?? T1 a1 ? p0 = x1 → Type[0].
  ∀a2:T2 a0 (refl ? a0) a1 (refl ? a1).
  ∀b0:T0.
  ∀e0:a0 = b0.
  ∀b1: T1 b0 e0.
  ∀e1:R1 ?? T1 a1 ? e0 = b1.
  T2 b0 e0 b1 e1.
#T0;#a0;#T1;#a1;#T2;#a2;#b0;#e0;#b1;#e1;
apply (eq_rect_Type0 ????? e1);
apply (R1 ?? ? ?? e0);
apply a2;
qed.

definition R3 :
  ∀T0:Type[0].
  ∀a0:T0.
  ∀T1:∀x0:T0. a0=x0 → Type[0].
  ∀a1:T1 a0 (refl ? a0).
  ∀T2:∀x0:T0. ∀p0:a0=x0. ∀x1:T1 x0 p0. R1 ?? T1 a1 ? p0 = x1 → Type[0].
  ∀a2:T2 a0 (refl ? a0) a1 (refl ? a1).
  ∀T3:∀x0:T0. ∀p0:a0=x0. ∀x1:T1 x0 p0.∀p1:R1 ?? T1 a1 ? p0 = x1.
      ∀x2:T2 x0 p0 x1 p1.R2 ???? T2 a2 x0 p0 ? p1 = x2 → Type[0].
  ∀a3:T3 a0 (refl ? a0) a1 (refl ? a1) a2 (refl ? a2).
  ∀b0:T0.
  ∀e0:a0 = b0.
  ∀b1: T1 b0 e0.
  ∀e1:R1 ?? T1 a1 ? e0 = b1.
  ∀b2: T2 b0 e0 b1 e1.
  ∀e2:R2 ???? T2 a2 b0 e0 ? e1 = b2.
  T3 b0 e0 b1 e1 b2 e2.
#T0;#a0;#T1;#a1;#T2;#a2;#T3;#a3;#b0;#e0;#b1;#e1;#b2;#e2;
apply (eq_rect_Type0 ????? e2);
apply (R2 ?? ? ???? e0 ? e1);
apply a3;
qed.

definition R4 :
  ∀T0:Type[0].
  ∀a0:T0.
  ∀T1:∀x0:T0. eq T0 a0 x0 → Type[0].
  ∀a1:T1 a0 (refl T0 a0).
  ∀T2:∀x0:T0. ∀p0:eq (T0 …) a0 x0. ∀x1:T1 x0 p0.eq (T1 …) (R1 T0 a0 T1 a1 x0 p0) x1 → Type[0].
  ∀a2:T2 a0 (refl T0 a0) a1 (refl (T1 a0 (refl T0 a0)) a1).
  ∀T3:∀x0:T0. ∀p0:eq (T0 …) a0 x0. ∀x1:T1 x0 p0.∀p1:eq (T1 …) (R1 T0 a0 T1 a1 x0 p0) x1.
      ∀x2:T2 x0 p0 x1 p1.eq (T2 …) (R2 T0 a0 T1 a1 T2 a2 x0 p0 x1 p1) x2 → Type[0].
  ∀a3:T3 a0 (refl T0 a0) a1 (refl (T1 a0 (refl T0 a0)) a1) 
      a2 (refl (T2 a0 (refl T0 a0) a1 (refl (T1 a0 (refl T0 a0)) a1)) a2). 
  ∀T4:∀x0:T0. ∀p0:eq (T0 …) a0 x0. ∀x1:T1 x0 p0.∀p1:eq (T1 …) (R1 T0 a0 T1 a1 x0 p0) x1.
      ∀x2:T2 x0 p0 x1 p1.∀p2:eq (T2 …) (R2 T0 a0 T1 a1 T2 a2 x0 p0 x1 p1) x2.
      ∀x3:T3 x0 p0 x1 p1 x2 p2.∀p3:eq (T3 …) (R3 T0 a0 T1 a1 T2 a2 T3 a3 x0 p0 x1 p1 x2 p2) x3. 
      Type[0].
  ∀a4:T4 a0 (refl T0 a0) a1 (refl (T1 a0 (refl T0 a0)) a1) 
      a2 (refl (T2 a0 (refl T0 a0) a1 (refl (T1 a0 (refl T0 a0)) a1)) a2) 
      a3 (refl (T3 a0 (refl T0 a0) a1 (refl (T1 a0 (refl T0 a0)) a1) 
                   a2 (refl (T2 a0 (refl T0 a0) a1 (refl (T1 a0 (refl T0 a0)) a1)) a2))
                   a3).
  ∀b0:T0.
  ∀e0:eq (T0 …) a0 b0.
  ∀b1: T1 b0 e0.
  ∀e1:eq (T1 …) (R1 T0 a0 T1 a1 b0 e0) b1.
  ∀b2: T2 b0 e0 b1 e1.
  ∀e2:eq (T2 …) (R2 T0 a0 T1 a1 T2 a2 b0 e0 b1 e1) b2.
  ∀b3: T3 b0 e0 b1 e1 b2 e2.
  ∀e3:eq (T3 …) (R3 T0 a0 T1 a1 T2 a2 T3 a3 b0 e0 b1 e1 b2 e2) b3.
  T4 b0 e0 b1 e1 b2 e2 b3 e3.
#T0;#a0;#T1;#a1;#T2;#a2;#T3;#a3;#T4;#a4;#b0;#e0;#b1;#e1;#b2;#e2;#b3;#e3;
apply (eq_rect_Type0 ????? e3);
apply (R3 ????????? e0 ? e1 ? e2);
apply a4;
qed.

axiom streicherK : ∀T:Type[0].∀t:T.∀P:t = t → Type[2].P (refl ? t) → ∀p.P p. 

definition EQ: ∀A:Type[0]. equivalence_relation A.
 #A; apply mk_equivalence_relation
  [ apply eq
  | apply refl
  | #x; #y; #H; rewrite < H; apply refl
  | #x; #y; #z; #Hyx; #Hxz; rewrite < Hxz; assumption]
qed.

axiom T1 : Type[0].
axiom T2 : T1 → Type[0].
axiom t1 : T1.
axiom t2 : ∀x:T1. T2 x.

inductive I2 : ∀r1:T1.T2 r1 → Type[0] ≝ 
| i2c1 : ∀x1:T1.∀x2:T2 x1. I2 x1 x2
| i2c2 : I2 t1 (t2 t1).

(* lemma i2d : ∀a,b.∀x,y:I2 a b.
             ∀e1:a = a.∀e2:R1 T1 a (λz,p.T2 z) b a e1 = b.
             ∀e: R2 T1 a (λz,p.T2 z) b (λz1,p1,z2,p2.I2 z1 z2) x a e1 b e2 = y.
             Type[2].
#a;#b;#x;#y;
apply (
match x return (λr1,r2,r.
                 ∀e1:r1 = a. ∀e2:R1 T1 r1 (λz,p. T2 z) r2 a e1 = b.
                 ∀e :R2 T1 r1 (λz,p. T2 z) r2 (λz1,p1,z2,p2. I2 z1 z2) r a e1 b e2 = y. Type[2]) with 
  [ i2c1 x1 x2 ⇒ ?
  | i2c2 ⇒ ?] 
)
[napply (match y return (λr1,r2,r.
                     ∀e1: x1 = r1. ∀e2: R1 T1 x1 (λz,p. T2 z) x2 r1 e1 = r2.
                     ∀e : R2 T1 x1 (λz,p.T2 z) x2 (λz1,p1,z2,p2. I2 z1 z2) (i2c1 x1 x2) r1 e1 r2 e2 = r. Type[2]) with
    [ i2c1 y1 y2 ⇒ ?
    | i2c2 ⇒ ? ])
 [#e1; #e2; #e;
  apply (∀P:Type[1].
                     (∀f1:x1 = y1. ∀f2: R1 T1 x1 (λz,p.T2 z) x2 y1 f1 = y2.
                      ∀f: R2 T1 x1 (λz,p.T2 z) x2
                          (λz1,p1,z2,p2.eq ? 
                              (i2c1 (R1 ??? z1 ? (R1 ?? (λm,n.m = y1) f1 ? p1)) ?)
                               (*       (R2 ???? (λm1,n1,m2,n2.R1 ?? (λm,n.T2 m) ? ? f1 = y2) f2 ? 
                                       p1 ? p2)))*)
(*                            (R2 ???? (λw1,q1,w2,q2.I2 w1 w2) (i2c1 z1 z2) 
                                ? (R1 ?? (λw,q.w = y1) e1 z1 p1) 
                                ? (R2 ????
                                      (λw1,q1,w2,q2.R1 ?? (λm,n.T2 m) w2 ? q1 = y2) 
                                      e2 z1 p1 (R1 T1 x1 (λw,q.w = y1) e1 z1 p1) p2))
  *)                          (i2c1 y1 y2)) 
                          ? y1 f1 y2 f2 = refl (I2 y1 y2) (i2c1 y1 y2).P) 
                   → P);
  apply (∀P:Type[1].
                     (∀f1:x1 = y1. ∀f2: R1 T1 x1 (λz,p.T2 z) x2 y1 f1 = y2. 
                      ∀f: R2 T1 x1 (λz,p.T2 z) x2
                          (λz1,p1,z2,p2.eq (I2 y1 y2) 
                            (R2 T1 z1 (λw,q.T2 w) z2 (λw1,q1,w2,q2.I2 w1 w2) (i2c1 z1 z2) 
                                y1 (R1 T1 x1 (λw,q.w = y1) e1 z1 p1) 
                                y2 (R2 T1 x1 (λw,q.w = y1) e1 
                                             (λw1,q1,w2,q2.R1 ??? w2 w1 q1 = y2) e2 z1 p1 (R1 T1 x1 (λw,q.w = y1) e1 z1 p1) p2))
                            (i2c1 y1 y2)) 
                          e y1 f1 y2 f2 = refl (I2 y1 y2) (i2c1 y1 y2).P) 
                   → P);



definition i2d : ∀a,b.∀x,y:I2 a b.
                  ∀e1:a = a.∀e2:R1 T1 a (λz,p.T2 z) b a e1 = b.
                  ∀e: R2 T1 a (λz,p.T2 z) b (λz1,p1,z2,p2.I2 z1 z2) x a e1 b e2 = y.Type[2] ≝
λa,b,x,y. 
match x return (λr1,r2,r.
                 ∀e1:r1 = a. ∀e2:R1 T1 r1 (λz,p. T2 z) r2 a e1 = b.
                 ∀e :R2 T1 r1 (λz,p. T2 z) r2 (λz1,p1,z2,p2. I2 z1 z2) r a e1 b e2 = y. Type[2]) with 
  [ i2c1 x1 x2 ⇒ 
    match y return (λr1,r2,r.
                     ∀e1: x1 = r1. ∀e2: R1 T1 x1 (λz,p. T2 z) x2 r1 e1 = r2.
                     ∀e : R2 T1 x1 (λz,p.T2 z) x2 (λz1,p1,z2,p2. I2 z1 z2) (i2c1 x1 x2) r1 e1 r2 e2 = r. Type[2]) with
    [ i2c1 y1 y2 ⇒ λe1,e2,e.∀P:Type[1].
                     (∀f1:x1 = y1. ∀f2: R1 T1 x1 (λz,p.T2 z) x2 y1 f1 = y2. 
                      ∀f: R2 T1 x1 (λz,p.T2 z) x2
                          (λz1,p1,z2,p2.eq (I2 y1 y2) 
                            (R2 T1 z1 (λw,q.T2 w) z2 (λw1,q1,w2,q2.I2 w1 w2) (i2c1 z1 z2) 
                                y1 (R1 T1 x1 (λw,q.w = y1) e1 z1 p1) 
                                y2 (R2 T1 x1 (λw,q.w = y1) e1 
                                             (λw1,q1,w2,q2.R1 ??? w2 w1 q1 = y2) e2 z1 p1 (R1 T1 x1 (λw,q.w = y1) e1 z1 p1) p2))
                            (i2c1 y1 y2)) 
                          e y1 f1 y2 f2 = refl (I2 y1 y2) (i2c1 y1 y2).P) 
                   → P
    | i2c2 ⇒ λe1,e2,e.∀P:Type[1].P ]
  | i2c2 ⇒ 
    match y return (λr1,r2,r.
                     ∀e1: x1 = r1. ∀e2: R1 ?? (λz,p. T2 z) x2 ? e1 = r2.
                     ∀e : R2 ???? (λz1,p1,z2,p2. I2 z1 z2) i2c2 ? e1 ? e2 = r. Type[2]) with
    [ i2c1 _ _ ⇒ λe1,e2,e.∀P:Type[1].P
    | i2c2 ⇒ λe1,e2,e.∀P:Type[1].
               (∀f: R2 ???? 
                    (λz1,p1,z2,p2.eq ? i2c2 i2c2) 
                    e ? e1 ? e2 = refl ? i2c2.P) → P ] ].

*)
