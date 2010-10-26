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

include "logic/pts.ma".

ninductive eq (A:Type[2]) (x:A) : A → Prop ≝
    refl: eq A x x.
    
interpretation "leibnitz's equality" 'eq t x y = (eq t x y).

nlemma eq_rect_r:
 ∀A.∀a,x.∀p:eq ? x a.∀P: ∀x:A. eq ? x a → Type. P a (refl A a) → P x p.
 #A; #a; #x; #p; ncases p; #P; #H; nassumption.
nqed.

nlemma eq_ind_r :
 ∀A.∀a.∀P: ∀x:A. x = a → Prop. P a (refl A a) → ∀x.∀p:eq ? x a.P x p.
 #A; #a; #P; #p; #x0; #p0; napply (eq_rect_r ? ? ? p0); nassumption.
nqed.

nlemma eq_rect_Type2_r :
  ∀A:Type.∀a.∀P: ∀x:A. eq ? x a → Type[2]. P a (refl A a) → ∀x.∀p:eq ? x a.P x p.
  #A;#a;#P;#H;#x;#p;ngeneralize in match H;ngeneralize in match P;
  ncases p;//;
nqed.

(*
nlemma eq_ind_r :
 ∀A.∀a.∀P: ∀x:A. x = a → Prop. P a (refl_eq A a) → ∀x.∀p:eq ? x a.P x p.
 #A; #a; #P; #p; #x0; #p0; ngeneralize in match p; 
ncases p0; #Heq; nassumption.
nqed.
*)

ntheorem rewrite_l: ∀A:Type[2].∀x.∀P:A → Prop. P x → ∀y. x = y → P y.
#A; #x; #P; #Hx; #y; #Heq;ncases Heq;nassumption.
nqed. 

ntheorem sym_eq: ∀A:Type[2].∀x,y:A. x = y → y = x.
#A; #x; #y; #Heq; napply (rewrite_l A x (λz.z=x)); 
##[ @; ##| nassumption; ##]
nqed.

ntheorem rewrite_r: ∀A:Type[2].∀x.∀P:A → Prop. P x → ∀y. y = x → P y.
#A; #x; #P; #Hx; #y; #Heq;ncases (sym_eq ? ? ?Heq);nassumption.
nqed.

ntheorem eq_coerc: ∀A,B:Type[1].A→(A=B)→B.
#A; #B; #Ha; #Heq;nelim Heq; nassumption.
nqed.

ndefinition R0 ≝ λT:Type[0].λt:T.t.
  
ndefinition R1 ≝ eq_rect_Type0.

ndefinition R2 :
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
napply (eq_rect_Type0 ????? e1);
napply (R1 ?? ? ?? e0);
napply a2;
nqed.

ndefinition R3 :
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
napply (eq_rect_Type0 ????? e2);
napply (R2 ?? ? ???? e0 ? e1);
napply a3;
nqed.

ndefinition R4 :
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
napply (eq_rect_Type0 ????? e3);
napply (R3 ????????? e0 ? e1 ? e2);
napply a4;
nqed.

naxiom streicherK : ∀T:Type[2].∀t:T.∀P:t = t → Type[2].P (refl ? t) → ∀p.P p.