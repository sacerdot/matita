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

(* This file was automatically generated: do not edit *********************)

include "Basic-1/arity/props.ma".

include "Basic-1/arity/cimp.ma".

include "Basic-1/aprem/props.ma".

theorem arity_aprem:
 \forall (g: G).(\forall (c: C).(\forall (t: T).(\forall (a: A).((arity g c t 
a) \to (\forall (i: nat).(\forall (b: A).((aprem i a b) \to (ex2_3 C T nat 
(\lambda (d: C).(\lambda (_: T).(\lambda (j: nat).(drop (plus i j) O d c)))) 
(\lambda (d: C).(\lambda (u: T).(\lambda (_: nat).(arity g d u (asucc g 
b)))))))))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (t: T).(\lambda (a: A).(\lambda (H: 
(arity g c t a)).(arity_ind g (\lambda (c0: C).(\lambda (_: T).(\lambda (a0: 
A).(\forall (i: nat).(\forall (b: A).((aprem i a0 b) \to (ex2_3 C T nat 
(\lambda (d: C).(\lambda (_: T).(\lambda (j: nat).(drop (plus i j) O d c0)))) 
(\lambda (d: C).(\lambda (u: T).(\lambda (_: nat).(arity g d u (asucc g 
b)))))))))))) (\lambda (c0: C).(\lambda (n: nat).(\lambda (i: nat).(\lambda 
(b: A).(\lambda (H0: (aprem i (ASort O n) b)).(let H_x \def (aprem_gen_sort b 
i O n H0) in (let H1 \def H_x in (False_ind (ex2_3 C T nat (\lambda (d: 
C).(\lambda (_: T).(\lambda (j: nat).(drop (plus i j) O d c0)))) (\lambda (d: 
C).(\lambda (u: T).(\lambda (_: nat).(arity g d u (asucc g b)))))) H1)))))))) 
(\lambda (c0: C).(\lambda (d: C).(\lambda (u: T).(\lambda (i: nat).(\lambda 
(H0: (getl i c0 (CHead d (Bind Abbr) u))).(\lambda (a0: A).(\lambda (_: 
(arity g d u a0)).(\lambda (H2: ((\forall (i0: nat).(\forall (b: A).((aprem 
i0 a0 b) \to (ex2_3 C T nat (\lambda (d0: C).(\lambda (_: T).(\lambda (j: 
nat).(drop (plus i0 j) O d0 d)))) (\lambda (d0: C).(\lambda (u0: T).(\lambda 
(_: nat).(arity g d0 u0 (asucc g b))))))))))).(\lambda (i0: nat).(\lambda (b: 
A).(\lambda (H3: (aprem i0 a0 b)).(let H_x \def (H2 i0 b H3) in (let H4 \def 
H_x in (ex2_3_ind C T nat (\lambda (d0: C).(\lambda (_: T).(\lambda (j: 
nat).(drop (plus i0 j) O d0 d)))) (\lambda (d0: C).(\lambda (u0: T).(\lambda 
(_: nat).(arity g d0 u0 (asucc g b))))) (ex2_3 C T nat (\lambda (d0: 
C).(\lambda (_: T).(\lambda (j: nat).(drop (plus i0 j) O d0 c0)))) (\lambda 
(d0: C).(\lambda (u0: T).(\lambda (_: nat).(arity g d0 u0 (asucc g b)))))) 
(\lambda (x0: C).(\lambda (x1: T).(\lambda (x2: nat).(\lambda (H5: (drop 
(plus i0 x2) O x0 d)).(\lambda (H6: (arity g x0 x1 (asucc g b))).(let H_x0 
\def (getl_drop_conf_rev (plus i0 x2) x0 d H5 Abbr c0 u i H0) in (let H7 \def 
H_x0 in (ex2_ind C (\lambda (c1: C).(drop (plus i0 x2) O c1 c0)) (\lambda 
(c1: C).(drop (S i) (plus i0 x2) c1 x0)) (ex2_3 C T nat (\lambda (d0: 
C).(\lambda (_: T).(\lambda (j: nat).(drop (plus i0 j) O d0 c0)))) (\lambda 
(d0: C).(\lambda (u0: T).(\lambda (_: nat).(arity g d0 u0 (asucc g b)))))) 
(\lambda (x: C).(\lambda (H8: (drop (plus i0 x2) O x c0)).(\lambda (H9: (drop 
(S i) (plus i0 x2) x x0)).(ex2_3_intro C T nat (\lambda (d0: C).(\lambda (_: 
T).(\lambda (j: nat).(drop (plus i0 j) O d0 c0)))) (\lambda (d0: C).(\lambda 
(u0: T).(\lambda (_: nat).(arity g d0 u0 (asucc g b))))) x (lift (S i) (plus 
i0 x2) x1) x2 H8 (arity_lift g x0 x1 (asucc g b) H6 x (S i) (plus i0 x2) 
H9))))) H7)))))))) H4)))))))))))))) (\lambda (c0: C).(\lambda (d: C).(\lambda 
(u: T).(\lambda (i: nat).(\lambda (H0: (getl i c0 (CHead d (Bind Abst) 
u))).(\lambda (a0: A).(\lambda (_: (arity g d u (asucc g a0))).(\lambda (H2: 
((\forall (i0: nat).(\forall (b: A).((aprem i0 (asucc g a0) b) \to (ex2_3 C T 
nat (\lambda (d0: C).(\lambda (_: T).(\lambda (j: nat).(drop (plus i0 j) O d0 
d)))) (\lambda (d0: C).(\lambda (u0: T).(\lambda (_: nat).(arity g d0 u0 
(asucc g b))))))))))).(\lambda (i0: nat).(\lambda (b: A).(\lambda (H3: (aprem 
i0 a0 b)).(let H4 \def (H2 i0 b (aprem_asucc g a0 b i0 H3)) in (ex2_3_ind C T 
nat (\lambda (d0: C).(\lambda (_: T).(\lambda (j: nat).(drop (plus i0 j) O d0 
d)))) (\lambda (d0: C).(\lambda (u0: T).(\lambda (_: nat).(arity g d0 u0 
(asucc g b))))) (ex2_3 C T nat (\lambda (d0: C).(\lambda (_: T).(\lambda (j: 
nat).(drop (plus i0 j) O d0 c0)))) (\lambda (d0: C).(\lambda (u0: T).(\lambda 
(_: nat).(arity g d0 u0 (asucc g b)))))) (\lambda (x0: C).(\lambda (x1: 
T).(\lambda (x2: nat).(\lambda (H5: (drop (plus i0 x2) O x0 d)).(\lambda (H6: 
(arity g x0 x1 (asucc g b))).(let H_x \def (getl_drop_conf_rev (plus i0 x2) 
x0 d H5 Abst c0 u i H0) in (let H7 \def H_x in (ex2_ind C (\lambda (c1: 
C).(drop (plus i0 x2) O c1 c0)) (\lambda (c1: C).(drop (S i) (plus i0 x2) c1 
x0)) (ex2_3 C T nat (\lambda (d0: C).(\lambda (_: T).(\lambda (j: nat).(drop 
(plus i0 j) O d0 c0)))) (\lambda (d0: C).(\lambda (u0: T).(\lambda (_: 
nat).(arity g d0 u0 (asucc g b)))))) (\lambda (x: C).(\lambda (H8: (drop 
(plus i0 x2) O x c0)).(\lambda (H9: (drop (S i) (plus i0 x2) x 
x0)).(ex2_3_intro C T nat (\lambda (d0: C).(\lambda (_: T).(\lambda (j: 
nat).(drop (plus i0 j) O d0 c0)))) (\lambda (d0: C).(\lambda (u0: T).(\lambda 
(_: nat).(arity g d0 u0 (asucc g b))))) x (lift (S i) (plus i0 x2) x1) x2 H8 
(arity_lift g x0 x1 (asucc g b) H6 x (S i) (plus i0 x2) H9))))) H7)))))))) 
H4))))))))))))) (\lambda (b: B).(\lambda (_: (not (eq B b Abst))).(\lambda 
(c0: C).(\lambda (u: T).(\lambda (a1: A).(\lambda (_: (arity g c0 u 
a1)).(\lambda (_: ((\forall (i: nat).(\forall (b0: A).((aprem i a1 b0) \to 
(ex2_3 C T nat (\lambda (d: C).(\lambda (_: T).(\lambda (j: nat).(drop (plus 
i j) O d c0)))) (\lambda (d: C).(\lambda (u0: T).(\lambda (_: nat).(arity g d 
u0 (asucc g b0))))))))))).(\lambda (t0: T).(\lambda (a2: A).(\lambda (_: 
(arity g (CHead c0 (Bind b) u) t0 a2)).(\lambda (H4: ((\forall (i: 
nat).(\forall (b0: A).((aprem i a2 b0) \to (ex2_3 C T nat (\lambda (d: 
C).(\lambda (_: T).(\lambda (j: nat).(drop (plus i j) O d (CHead c0 (Bind b) 
u))))) (\lambda (d: C).(\lambda (u0: T).(\lambda (_: nat).(arity g d u0 
(asucc g b0))))))))))).(\lambda (i: nat).(\lambda (b0: A).(\lambda (H5: 
(aprem i a2 b0)).(let H_x \def (H4 i b0 H5) in (let H6 \def H_x in (ex2_3_ind 
C T nat (\lambda (d: C).(\lambda (_: T).(\lambda (j: nat).(drop (plus i j) O 
d (CHead c0 (Bind b) u))))) (\lambda (d: C).(\lambda (u0: T).(\lambda (_: 
nat).(arity g d u0 (asucc g b0))))) (ex2_3 C T nat (\lambda (d: C).(\lambda 
(_: T).(\lambda (j: nat).(drop (plus i j) O d c0)))) (\lambda (d: C).(\lambda 
(u0: T).(\lambda (_: nat).(arity g d u0 (asucc g b0)))))) (\lambda (x0: 
C).(\lambda (x1: T).(\lambda (x2: nat).(\lambda (H7: (drop (plus i x2) O x0 
(CHead c0 (Bind b) u))).(\lambda (H8: (arity g x0 x1 (asucc g b0))).(let H9 
\def (eq_ind nat (S (plus i x2)) (\lambda (n: nat).(drop n O x0 c0)) (drop_S 
b x0 c0 u (plus i x2) H7) (plus i (S x2)) (plus_n_Sm i x2)) in (ex2_3_intro C 
T nat (\lambda (d: C).(\lambda (_: T).(\lambda (j: nat).(drop (plus i j) O d 
c0)))) (\lambda (d: C).(\lambda (u0: T).(\lambda (_: nat).(arity g d u0 
(asucc g b0))))) x0 x1 (S x2) H9 H8))))))) H6))))))))))))))))) (\lambda (c0: 
C).(\lambda (u: T).(\lambda (a1: A).(\lambda (H0: (arity g c0 u (asucc g 
a1))).(\lambda (_: ((\forall (i: nat).(\forall (b: A).((aprem i (asucc g a1) 
b) \to (ex2_3 C T nat (\lambda (d: C).(\lambda (_: T).(\lambda (j: nat).(drop 
(plus i j) O d c0)))) (\lambda (d: C).(\lambda (u0: T).(\lambda (_: 
nat).(arity g d u0 (asucc g b))))))))))).(\lambda (t0: T).(\lambda (a2: 
A).(\lambda (_: (arity g (CHead c0 (Bind Abst) u) t0 a2)).(\lambda (H3: 
((\forall (i: nat).(\forall (b: A).((aprem i a2 b) \to (ex2_3 C T nat 
(\lambda (d: C).(\lambda (_: T).(\lambda (j: nat).(drop (plus i j) O d (CHead 
c0 (Bind Abst) u))))) (\lambda (d: C).(\lambda (u0: T).(\lambda (_: 
nat).(arity g d u0 (asucc g b))))))))))).(\lambda (i: nat).(\lambda (b: 
A).(\lambda (H4: (aprem i (AHead a1 a2) b)).(nat_ind (\lambda (n: 
nat).((aprem n (AHead a1 a2) b) \to (ex2_3 C T nat (\lambda (d: C).(\lambda 
(_: T).(\lambda (j: nat).(drop (plus n j) O d c0)))) (\lambda (d: C).(\lambda 
(u0: T).(\lambda (_: nat).(arity g d u0 (asucc g b)))))))) (\lambda (H5: 
(aprem O (AHead a1 a2) b)).(let H_y \def (aprem_gen_head_O a1 a2 b H5) in 
(eq_ind_r A a1 (\lambda (a0: A).(ex2_3 C T nat (\lambda (d: C).(\lambda (_: 
T).(\lambda (j: nat).(drop (plus O j) O d c0)))) (\lambda (d: C).(\lambda 
(u0: T).(\lambda (_: nat).(arity g d u0 (asucc g a0))))))) (ex2_3_intro C T 
nat (\lambda (d: C).(\lambda (_: T).(\lambda (j: nat).(drop (plus O j) O d 
c0)))) (\lambda (d: C).(\lambda (u0: T).(\lambda (_: nat).(arity g d u0 
(asucc g a1))))) c0 u O (drop_refl c0) H0) b H_y))) (\lambda (i0: 
nat).(\lambda (_: (((aprem i0 (AHead a1 a2) b) \to (ex2_3 C T nat (\lambda 
(d: C).(\lambda (_: T).(\lambda (j: nat).(drop (plus i0 j) O d c0)))) 
(\lambda (d: C).(\lambda (u0: T).(\lambda (_: nat).(arity g d u0 (asucc g 
b))))))))).(\lambda (H5: (aprem (S i0) (AHead a1 a2) b)).(let H_y \def 
(aprem_gen_head_S a1 a2 b i0 H5) in (let H_x \def (H3 i0 b H_y) in (let H6 
\def H_x in (ex2_3_ind C T nat (\lambda (d: C).(\lambda (_: T).(\lambda (j: 
nat).(drop (plus i0 j) O d (CHead c0 (Bind Abst) u))))) (\lambda (d: 
C).(\lambda (u0: T).(\lambda (_: nat).(arity g d u0 (asucc g b))))) (ex2_3 C 
T nat (\lambda (d: C).(\lambda (_: T).(\lambda (j: nat).(drop (plus (S i0) j) 
O d c0)))) (\lambda (d: C).(\lambda (u0: T).(\lambda (_: nat).(arity g d u0 
(asucc g b)))))) (\lambda (x0: C).(\lambda (x1: T).(\lambda (x2: 
nat).(\lambda (H7: (drop (plus i0 x2) O x0 (CHead c0 (Bind Abst) 
u))).(\lambda (H8: (arity g x0 x1 (asucc g b))).(ex2_3_intro C T nat (\lambda 
(d: C).(\lambda (_: T).(\lambda (j: nat).(drop (plus (S i0) j) O d c0)))) 
(\lambda (d: C).(\lambda (u0: T).(\lambda (_: nat).(arity g d u0 (asucc g 
b))))) x0 x1 x2 (drop_S Abst x0 c0 u (plus i0 x2) H7) H8)))))) H6))))))) i 
H4))))))))))))) (\lambda (c0: C).(\lambda (u: T).(\lambda (a1: A).(\lambda 
(_: (arity g c0 u a1)).(\lambda (_: ((\forall (i: nat).(\forall (b: 
A).((aprem i a1 b) \to (ex2_3 C T nat (\lambda (d: C).(\lambda (_: 
T).(\lambda (j: nat).(drop (plus i j) O d c0)))) (\lambda (d: C).(\lambda 
(u0: T).(\lambda (_: nat).(arity g d u0 (asucc g b))))))))))).(\lambda (t0: 
T).(\lambda (a2: A).(\lambda (_: (arity g c0 t0 (AHead a1 a2))).(\lambda (H3: 
((\forall (i: nat).(\forall (b: A).((aprem i (AHead a1 a2) b) \to (ex2_3 C T 
nat (\lambda (d: C).(\lambda (_: T).(\lambda (j: nat).(drop (plus i j) O d 
c0)))) (\lambda (d: C).(\lambda (u0: T).(\lambda (_: nat).(arity g d u0 
(asucc g b))))))))))).(\lambda (i: nat).(\lambda (b: A).(\lambda (H4: (aprem 
i a2 b)).(let H5 \def (H3 (S i) b (aprem_succ a2 b i H4 a1)) in (ex2_3_ind C 
T nat (\lambda (d: C).(\lambda (_: T).(\lambda (j: nat).(drop (S (plus i j)) 
O d c0)))) (\lambda (d: C).(\lambda (u0: T).(\lambda (_: nat).(arity g d u0 
(asucc g b))))) (ex2_3 C T nat (\lambda (d: C).(\lambda (_: T).(\lambda (j: 
nat).(drop (plus i j) O d c0)))) (\lambda (d: C).(\lambda (u0: T).(\lambda 
(_: nat).(arity g d u0 (asucc g b)))))) (\lambda (x0: C).(\lambda (x1: 
T).(\lambda (x2: nat).(\lambda (H6: (drop (S (plus i x2)) O x0 c0)).(\lambda 
(H7: (arity g x0 x1 (asucc g b))).(C_ind (\lambda (c1: C).((drop (S (plus i 
x2)) O c1 c0) \to ((arity g c1 x1 (asucc g b)) \to (ex2_3 C T nat (\lambda 
(d: C).(\lambda (_: T).(\lambda (j: nat).(drop (plus i j) O d c0)))) (\lambda 
(d: C).(\lambda (u0: T).(\lambda (_: nat).(arity g d u0 (asucc g b))))))))) 
(\lambda (n: nat).(\lambda (H8: (drop (S (plus i x2)) O (CSort n) 
c0)).(\lambda (_: (arity g (CSort n) x1 (asucc g b))).(and3_ind (eq C c0 
(CSort n)) (eq nat (S (plus i x2)) O) (eq nat O O) (ex2_3 C T nat (\lambda 
(d: C).(\lambda (_: T).(\lambda (j: nat).(drop (plus i j) O d c0)))) (\lambda 
(d: C).(\lambda (u0: T).(\lambda (_: nat).(arity g d u0 (asucc g b)))))) 
(\lambda (_: (eq C c0 (CSort n))).(\lambda (H11: (eq nat (S (plus i x2)) 
O)).(\lambda (_: (eq nat O O)).(let H13 \def (eq_ind nat (S (plus i x2)) 
(\lambda (ee: nat).(match ee in nat return (\lambda (_: nat).Prop) with [O 
\Rightarrow False | (S _) \Rightarrow True])) I O H11) in (False_ind (ex2_3 C 
T nat (\lambda (d: C).(\lambda (_: T).(\lambda (j: nat).(drop (plus i j) O d 
c0)))) (\lambda (d: C).(\lambda (u0: T).(\lambda (_: nat).(arity g d u0 
(asucc g b)))))) H13))))) (drop_gen_sort n (S (plus i x2)) O c0 H8))))) 
(\lambda (d: C).(\lambda (IHd: (((drop (S (plus i x2)) O d c0) \to ((arity g 
d x1 (asucc g b)) \to (ex2_3 C T nat (\lambda (d0: C).(\lambda (_: 
T).(\lambda (j: nat).(drop (plus i j) O d0 c0)))) (\lambda (d0: C).(\lambda 
(u0: T).(\lambda (_: nat).(arity g d0 u0 (asucc g b)))))))))).(\lambda (k: 
K).(\lambda (t1: T).(\lambda (H8: (drop (S (plus i x2)) O (CHead d k t1) 
c0)).(\lambda (H9: (arity g (CHead d k t1) x1 (asucc g b))).(K_ind (\lambda 
(k0: K).((arity g (CHead d k0 t1) x1 (asucc g b)) \to ((drop (r k0 (plus i 
x2)) O d c0) \to (ex2_3 C T nat (\lambda (d0: C).(\lambda (_: T).(\lambda (j: 
nat).(drop (plus i j) O d0 c0)))) (\lambda (d0: C).(\lambda (u0: T).(\lambda 
(_: nat).(arity g d0 u0 (asucc g b))))))))) (\lambda (b0: B).(\lambda (H10: 
(arity g (CHead d (Bind b0) t1) x1 (asucc g b))).(\lambda (H11: (drop (r 
(Bind b0) (plus i x2)) O d c0)).(ex2_3_intro C T nat (\lambda (d0: 
C).(\lambda (_: T).(\lambda (j: nat).(drop (plus i j) O d0 c0)))) (\lambda 
(d0: C).(\lambda (u0: T).(\lambda (_: nat).(arity g d0 u0 (asucc g b))))) 
(CHead d (Bind b0) t1) x1 (S x2) (eq_ind nat (S (plus i x2)) (\lambda (n: 
nat).(drop n O (CHead d (Bind b0) t1) c0)) (drop_drop (Bind b0) (plus i x2) d 
c0 H11 t1) (plus i (S x2)) (plus_n_Sm i x2)) H10)))) (\lambda (f: F).(\lambda 
(H10: (arity g (CHead d (Flat f) t1) x1 (asucc g b))).(\lambda (H11: (drop (r 
(Flat f) (plus i x2)) O d c0)).(let H12 \def (IHd H11 (arity_cimp_conf g 
(CHead d (Flat f) t1) x1 (asucc g b) H10 d (cimp_flat_sx f d t1))) in 
(ex2_3_ind C T nat (\lambda (d0: C).(\lambda (_: T).(\lambda (j: nat).(drop 
(plus i j) O d0 c0)))) (\lambda (d0: C).(\lambda (u0: T).(\lambda (_: 
nat).(arity g d0 u0 (asucc g b))))) (ex2_3 C T nat (\lambda (d0: C).(\lambda 
(_: T).(\lambda (j: nat).(drop (plus i j) O d0 c0)))) (\lambda (d0: 
C).(\lambda (u0: T).(\lambda (_: nat).(arity g d0 u0 (asucc g b)))))) 
(\lambda (x3: C).(\lambda (x4: T).(\lambda (x5: nat).(\lambda (H13: (drop 
(plus i x5) O x3 c0)).(\lambda (H14: (arity g x3 x4 (asucc g 
b))).(ex2_3_intro C T nat (\lambda (d0: C).(\lambda (_: T).(\lambda (j: 
nat).(drop (plus i j) O d0 c0)))) (\lambda (d0: C).(\lambda (u0: T).(\lambda 
(_: nat).(arity g d0 u0 (asucc g b))))) x3 x4 x5 H13 H14)))))) H12))))) k H9 
(drop_gen_drop k d c0 t1 (plus i x2) H8)))))))) x0 H6 H7)))))) 
H5)))))))))))))) (\lambda (c0: C).(\lambda (u: T).(\lambda (a0: A).(\lambda 
(_: (arity g c0 u (asucc g a0))).(\lambda (_: ((\forall (i: nat).(\forall (b: 
A).((aprem i (asucc g a0) b) \to (ex2_3 C T nat (\lambda (d: C).(\lambda (_: 
T).(\lambda (j: nat).(drop (plus i j) O d c0)))) (\lambda (d: C).(\lambda 
(u0: T).(\lambda (_: nat).(arity g d u0 (asucc g b))))))))))).(\lambda (t0: 
T).(\lambda (_: (arity g c0 t0 a0)).(\lambda (H3: ((\forall (i: nat).(\forall 
(b: A).((aprem i a0 b) \to (ex2_3 C T nat (\lambda (d: C).(\lambda (_: 
T).(\lambda (j: nat).(drop (plus i j) O d c0)))) (\lambda (d: C).(\lambda 
(u0: T).(\lambda (_: nat).(arity g d u0 (asucc g b))))))))))).(\lambda (i: 
nat).(\lambda (b: A).(\lambda (H4: (aprem i a0 b)).(let H_x \def (H3 i b H4) 
in (let H5 \def H_x in (ex2_3_ind C T nat (\lambda (d: C).(\lambda (_: 
T).(\lambda (j: nat).(drop (plus i j) O d c0)))) (\lambda (d: C).(\lambda 
(u0: T).(\lambda (_: nat).(arity g d u0 (asucc g b))))) (ex2_3 C T nat 
(\lambda (d: C).(\lambda (_: T).(\lambda (j: nat).(drop (plus i j) O d c0)))) 
(\lambda (d: C).(\lambda (u0: T).(\lambda (_: nat).(arity g d u0 (asucc g 
b)))))) (\lambda (x0: C).(\lambda (x1: T).(\lambda (x2: nat).(\lambda (H6: 
(drop (plus i x2) O x0 c0)).(\lambda (H7: (arity g x0 x1 (asucc g 
b))).(ex2_3_intro C T nat (\lambda (d: C).(\lambda (_: T).(\lambda (j: 
nat).(drop (plus i j) O d c0)))) (\lambda (d: C).(\lambda (u0: T).(\lambda 
(_: nat).(arity g d u0 (asucc g b))))) x0 x1 x2 H6 H7)))))) H5)))))))))))))) 
(\lambda (c0: C).(\lambda (t0: T).(\lambda (a1: A).(\lambda (_: (arity g c0 
t0 a1)).(\lambda (H1: ((\forall (i: nat).(\forall (b: A).((aprem i a1 b) \to 
(ex2_3 C T nat (\lambda (d: C).(\lambda (_: T).(\lambda (j: nat).(drop (plus 
i j) O d c0)))) (\lambda (d: C).(\lambda (u: T).(\lambda (_: nat).(arity g d 
u (asucc g b))))))))))).(\lambda (a2: A).(\lambda (H2: (leq g a1 
a2)).(\lambda (i: nat).(\lambda (b: A).(\lambda (H3: (aprem i a2 b)).(let H_x 
\def (aprem_repl g a1 a2 H2 i b H3) in (let H4 \def H_x in (ex2_ind A 
(\lambda (b1: A).(leq g b1 b)) (\lambda (b1: A).(aprem i a1 b1)) (ex2_3 C T 
nat (\lambda (d: C).(\lambda (_: T).(\lambda (j: nat).(drop (plus i j) O d 
c0)))) (\lambda (d: C).(\lambda (u: T).(\lambda (_: nat).(arity g d u (asucc 
g b)))))) (\lambda (x: A).(\lambda (H5: (leq g x b)).(\lambda (H6: (aprem i 
a1 x)).(let H_x0 \def (H1 i x H6) in (let H7 \def H_x0 in (ex2_3_ind C T nat 
(\lambda (d: C).(\lambda (_: T).(\lambda (j: nat).(drop (plus i j) O d c0)))) 
(\lambda (d: C).(\lambda (u: T).(\lambda (_: nat).(arity g d u (asucc g 
x))))) (ex2_3 C T nat (\lambda (d: C).(\lambda (_: T).(\lambda (j: nat).(drop 
(plus i j) O d c0)))) (\lambda (d: C).(\lambda (u: T).(\lambda (_: 
nat).(arity g d u (asucc g b)))))) (\lambda (x0: C).(\lambda (x1: T).(\lambda 
(x2: nat).(\lambda (H8: (drop (plus i x2) O x0 c0)).(\lambda (H9: (arity g x0 
x1 (asucc g x))).(ex2_3_intro C T nat (\lambda (d: C).(\lambda (_: 
T).(\lambda (j: nat).(drop (plus i j) O d c0)))) (\lambda (d: C).(\lambda (u: 
T).(\lambda (_: nat).(arity g d u (asucc g b))))) x0 x1 x2 H8 (arity_repl g 
x0 x1 (asucc g x) H9 (asucc g b) (asucc_repl g x b H5)))))))) H7)))))) 
H4))))))))))))) c t a H))))).
(* COMMENTS
Initial nodes: 4526
END *)

