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

include "basic_1A/drop/defs.ma".

include "basic_1A/lift/fwd.ma".

include "basic_1A/r/props.ma".

include "basic_1A/C/fwd.ma".

implied rec lemma drop_ind (P: (nat \to (nat \to (C \to (C \to Prop))))) (f: 
(\forall (c: C).(P O O c c))) (f0: (\forall (k: K).(\forall (h: nat).(\forall 
(c: C).(\forall (e: C).((drop (r k h) O c e) \to ((P (r k h) O c e) \to 
(\forall (u: T).(P (S h) O (CHead c k u) e))))))))) (f1: (\forall (k: 
K).(\forall (h: nat).(\forall (d: nat).(\forall (c: C).(\forall (e: C).((drop 
h (r k d) c e) \to ((P h (r k d) c e) \to (\forall (u: T).(P h (S d) (CHead c 
k (lift h (r k d) u)) (CHead e k u))))))))))) (n: nat) (n0: nat) (c: C) (c0: 
C) (d: drop n n0 c c0) on d: P n n0 c c0 \def match d with [(drop_refl c1) 
\Rightarrow (f c1) | (drop_drop k h c1 e d0 u) \Rightarrow (f0 k h c1 e d0 
((drop_ind P f f0 f1) (r k h) O c1 e d0) u) | (drop_skip k h d0 c1 e d1 u) 
\Rightarrow (f1 k h d0 c1 e d1 ((drop_ind P f f0 f1) h (r k d0) c1 e d1) u)].

lemma drop_gen_sort:
 \forall (n: nat).(\forall (h: nat).(\forall (d: nat).(\forall (x: C).((drop 
h d (CSort n) x) \to (and3 (eq C x (CSort n)) (eq nat h O) (eq nat d O))))))
\def
 \lambda (n: nat).(\lambda (h: nat).(\lambda (d: nat).(\lambda (x: 
C).(\lambda (H: (drop h d (CSort n) x)).(insert_eq C (CSort n) (\lambda (c: 
C).(drop h d c x)) (\lambda (c: C).(and3 (eq C x c) (eq nat h O) (eq nat d 
O))) (\lambda (y: C).(\lambda (H0: (drop h d y x)).(drop_ind (\lambda (n0: 
nat).(\lambda (n1: nat).(\lambda (c: C).(\lambda (c0: C).((eq C c (CSort n)) 
\to (and3 (eq C c0 c) (eq nat n0 O) (eq nat n1 O))))))) (\lambda (c: 
C).(\lambda (H1: (eq C c (CSort n))).(let H2 \def (f_equal C C (\lambda (e: 
C).e) c (CSort n) H1) in (eq_ind_r C (CSort n) (\lambda (c0: C).(and3 (eq C 
c0 c0) (eq nat O O) (eq nat O O))) (and3_intro (eq C (CSort n) (CSort n)) (eq 
nat O O) (eq nat O O) (refl_equal C (CSort n)) (refl_equal nat O) (refl_equal 
nat O)) c H2)))) (\lambda (k: K).(\lambda (h0: nat).(\lambda (c: C).(\lambda 
(e: C).(\lambda (_: (drop (r k h0) O c e)).(\lambda (_: (((eq C c (CSort n)) 
\to (and3 (eq C e c) (eq nat (r k h0) O) (eq nat O O))))).(\lambda (u: 
T).(\lambda (H3: (eq C (CHead c k u) (CSort n))).(let H4 \def (eq_ind C 
(CHead c k u) (\lambda (ee: C).(match ee with [(CSort _) \Rightarrow False | 
(CHead _ _ _) \Rightarrow True])) I (CSort n) H3) in (False_ind (and3 (eq C e 
(CHead c k u)) (eq nat (S h0) O) (eq nat O O)) H4)))))))))) (\lambda (k: 
K).(\lambda (h0: nat).(\lambda (d0: nat).(\lambda (c: C).(\lambda (e: 
C).(\lambda (_: (drop h0 (r k d0) c e)).(\lambda (_: (((eq C c (CSort n)) \to 
(and3 (eq C e c) (eq nat h0 O) (eq nat (r k d0) O))))).(\lambda (u: 
T).(\lambda (H3: (eq C (CHead c k (lift h0 (r k d0) u)) (CSort n))).(let H4 
\def (eq_ind C (CHead c k (lift h0 (r k d0) u)) (\lambda (ee: C).(match ee 
with [(CSort _) \Rightarrow False | (CHead _ _ _) \Rightarrow True])) I 
(CSort n) H3) in (False_ind (and3 (eq C (CHead e k u) (CHead c k (lift h0 (r 
k d0) u))) (eq nat h0 O) (eq nat (S d0) O)) H4))))))))))) h d y x H0))) 
H))))).

lemma drop_gen_refl:
 \forall (x: C).(\forall (e: C).((drop O O x e) \to (eq C x e)))
\def
 \lambda (x: C).(\lambda (e: C).(\lambda (H: (drop O O x e)).(insert_eq nat O 
(\lambda (n: nat).(drop n O x e)) (\lambda (_: nat).(eq C x e)) (\lambda (y: 
nat).(\lambda (H0: (drop y O x e)).(insert_eq nat O (\lambda (n: nat).(drop y 
n x e)) (\lambda (n: nat).((eq nat y n) \to (eq C x e))) (\lambda (y0: 
nat).(\lambda (H1: (drop y y0 x e)).(drop_ind (\lambda (n: nat).(\lambda (n0: 
nat).(\lambda (c: C).(\lambda (c0: C).((eq nat n0 O) \to ((eq nat n n0) \to 
(eq C c c0))))))) (\lambda (c: C).(\lambda (_: (eq nat O O)).(\lambda (_: (eq 
nat O O)).(refl_equal C c)))) (\lambda (k: K).(\lambda (h: nat).(\lambda (c: 
C).(\lambda (e0: C).(\lambda (_: (drop (r k h) O c e0)).(\lambda (_: (((eq 
nat O O) \to ((eq nat (r k h) O) \to (eq C c e0))))).(\lambda (u: T).(\lambda 
(_: (eq nat O O)).(\lambda (H5: (eq nat (S h) O)).(let H6 \def (eq_ind nat (S 
h) (\lambda (ee: nat).(match ee with [O \Rightarrow False | (S _) \Rightarrow 
True])) I O H5) in (False_ind (eq C (CHead c k u) e0) H6))))))))))) (\lambda 
(k: K).(\lambda (h: nat).(\lambda (d: nat).(\lambda (c: C).(\lambda (e0: 
C).(\lambda (H2: (drop h (r k d) c e0)).(\lambda (H3: (((eq nat (r k d) O) 
\to ((eq nat h (r k d)) \to (eq C c e0))))).(\lambda (u: T).(\lambda (H4: (eq 
nat (S d) O)).(\lambda (H5: (eq nat h (S d))).(let H6 \def (f_equal nat nat 
(\lambda (e1: nat).e1) h (S d) H5) in (let H7 \def (eq_ind nat h (\lambda (n: 
nat).((eq nat (r k d) O) \to ((eq nat n (r k d)) \to (eq C c e0)))) H3 (S d) 
H6) in (let H8 \def (eq_ind nat h (\lambda (n: nat).(drop n (r k d) c e0)) H2 
(S d) H6) in (eq_ind_r nat (S d) (\lambda (n: nat).(eq C (CHead c k (lift n 
(r k d) u)) (CHead e0 k u))) (let H9 \def (eq_ind nat (S d) (\lambda (ee: 
nat).(match ee with [O \Rightarrow False | (S _) \Rightarrow True])) I O H4) 
in (False_ind (eq C (CHead c k (lift (S d) (r k d) u)) (CHead e0 k u)) H9)) h 
H6)))))))))))))) y y0 x e H1))) H0))) H))).

lemma drop_gen_drop:
 \forall (k: K).(\forall (c: C).(\forall (x: C).(\forall (u: T).(\forall (h: 
nat).((drop (S h) O (CHead c k u) x) \to (drop (r k h) O c x))))))
\def
 \lambda (k: K).(\lambda (c: C).(\lambda (x: C).(\lambda (u: T).(\lambda (h: 
nat).(\lambda (H: (drop (S h) O (CHead c k u) x)).(insert_eq C (CHead c k u) 
(\lambda (c0: C).(drop (S h) O c0 x)) (\lambda (_: C).(drop (r k h) O c x)) 
(\lambda (y: C).(\lambda (H0: (drop (S h) O y x)).(insert_eq nat O (\lambda 
(n: nat).(drop (S h) n y x)) (\lambda (n: nat).((eq C y (CHead c k u)) \to 
(drop (r k h) n c x))) (\lambda (y0: nat).(\lambda (H1: (drop (S h) y0 y 
x)).(insert_eq nat (S h) (\lambda (n: nat).(drop n y0 y x)) (\lambda (_: 
nat).((eq nat y0 O) \to ((eq C y (CHead c k u)) \to (drop (r k h) y0 c x)))) 
(\lambda (y1: nat).(\lambda (H2: (drop y1 y0 y x)).(drop_ind (\lambda (n: 
nat).(\lambda (n0: nat).(\lambda (c0: C).(\lambda (c1: C).((eq nat n (S h)) 
\to ((eq nat n0 O) \to ((eq C c0 (CHead c k u)) \to (drop (r k h) n0 c 
c1)))))))) (\lambda (c0: C).(\lambda (H3: (eq nat O (S h))).(\lambda (_: (eq 
nat O O)).(\lambda (H5: (eq C c0 (CHead c k u))).(eq_ind_r C (CHead c k u) 
(\lambda (c1: C).(drop (r k h) O c c1)) (let H6 \def (eq_ind nat O (\lambda 
(ee: nat).(match ee with [O \Rightarrow True | (S _) \Rightarrow False])) I 
(S h) H3) in (False_ind (drop (r k h) O c (CHead c k u)) H6)) c0 H5))))) 
(\lambda (k0: K).(\lambda (h0: nat).(\lambda (c0: C).(\lambda (e: C).(\lambda 
(H3: (drop (r k0 h0) O c0 e)).(\lambda (H4: (((eq nat (r k0 h0) (S h)) \to 
((eq nat O O) \to ((eq C c0 (CHead c k u)) \to (drop (r k h) O c 
e)))))).(\lambda (u0: T).(\lambda (H5: (eq nat (S h0) (S h))).(\lambda (_: 
(eq nat O O)).(\lambda (H7: (eq C (CHead c0 k0 u0) (CHead c k u))).(let H8 
\def (f_equal C C (\lambda (e0: C).(match e0 with [(CSort _) \Rightarrow c0 | 
(CHead c1 _ _) \Rightarrow c1])) (CHead c0 k0 u0) (CHead c k u) H7) in ((let 
H9 \def (f_equal C K (\lambda (e0: C).(match e0 with [(CSort _) \Rightarrow 
k0 | (CHead _ k1 _) \Rightarrow k1])) (CHead c0 k0 u0) (CHead c k u) H7) in 
((let H10 \def (f_equal C T (\lambda (e0: C).(match e0 with [(CSort _) 
\Rightarrow u0 | (CHead _ _ t) \Rightarrow t])) (CHead c0 k0 u0) (CHead c k 
u) H7) in (\lambda (H11: (eq K k0 k)).(\lambda (H12: (eq C c0 c)).(let H13 
\def (eq_ind C c0 (\lambda (c1: C).((eq nat (r k0 h0) (S h)) \to ((eq nat O 
O) \to ((eq C c1 (CHead c k u)) \to (drop (r k h) O c e))))) H4 c H12) in 
(let H14 \def (eq_ind C c0 (\lambda (c1: C).(drop (r k0 h0) O c1 e)) H3 c 
H12) in (let H15 \def (eq_ind K k0 (\lambda (k1: K).((eq nat (r k1 h0) (S h)) 
\to ((eq nat O O) \to ((eq C c (CHead c k u)) \to (drop (r k h) O c e))))) 
H13 k H11) in (let H16 \def (eq_ind K k0 (\lambda (k1: K).(drop (r k1 h0) O c 
e)) H14 k H11) in (let H17 \def (f_equal nat nat (\lambda (e0: nat).(match e0 
with [O \Rightarrow h0 | (S n) \Rightarrow n])) (S h0) (S h) H5) in (let H18 
\def (eq_ind nat h0 (\lambda (n: nat).((eq nat (r k n) (S h)) \to ((eq nat O 
O) \to ((eq C c (CHead c k u)) \to (drop (r k h) O c e))))) H15 h H17) in 
(let H19 \def (eq_ind nat h0 (\lambda (n: nat).(drop (r k n) O c e)) H16 h 
H17) in H19)))))))))) H9)) H8)))))))))))) (\lambda (k0: K).(\lambda (h0: 
nat).(\lambda (d: nat).(\lambda (c0: C).(\lambda (e: C).(\lambda (H3: (drop 
h0 (r k0 d) c0 e)).(\lambda (H4: (((eq nat h0 (S h)) \to ((eq nat (r k0 d) O) 
\to ((eq C c0 (CHead c k u)) \to (drop (r k h) (r k0 d) c e)))))).(\lambda 
(u0: T).(\lambda (H5: (eq nat h0 (S h))).(\lambda (H6: (eq nat (S d) 
O)).(\lambda (H7: (eq C (CHead c0 k0 (lift h0 (r k0 d) u0)) (CHead c k 
u))).(let H8 \def (eq_ind nat h0 (\lambda (n: nat).(eq C (CHead c0 k0 (lift n 
(r k0 d) u0)) (CHead c k u))) H7 (S h) H5) in (let H9 \def (eq_ind nat h0 
(\lambda (n: nat).((eq nat n (S h)) \to ((eq nat (r k0 d) O) \to ((eq C c0 
(CHead c k u)) \to (drop (r k h) (r k0 d) c e))))) H4 (S h) H5) in (let H10 
\def (eq_ind nat h0 (\lambda (n: nat).(drop n (r k0 d) c0 e)) H3 (S h) H5) in 
(let H11 \def (f_equal C C (\lambda (e0: C).(match e0 with [(CSort _) 
\Rightarrow c0 | (CHead c1 _ _) \Rightarrow c1])) (CHead c0 k0 (lift (S h) (r 
k0 d) u0)) (CHead c k u) H8) in ((let H12 \def (f_equal C K (\lambda (e0: 
C).(match e0 with [(CSort _) \Rightarrow k0 | (CHead _ k1 _) \Rightarrow 
k1])) (CHead c0 k0 (lift (S h) (r k0 d) u0)) (CHead c k u) H8) in ((let H13 
\def (f_equal C T (\lambda (e0: C).(match e0 with [(CSort _) \Rightarrow 
(lref_map (\lambda (x0: nat).(plus x0 (S h))) (r k0 d) u0) | (CHead _ _ t) 
\Rightarrow t])) (CHead c0 k0 (lift (S h) (r k0 d) u0)) (CHead c k u) H8) in 
(\lambda (H14: (eq K k0 k)).(\lambda (H15: (eq C c0 c)).(let H16 \def (eq_ind 
C c0 (\lambda (c1: C).((eq nat (S h) (S h)) \to ((eq nat (r k0 d) O) \to ((eq 
C c1 (CHead c k u)) \to (drop (r k h) (r k0 d) c e))))) H9 c H15) in (let H17 
\def (eq_ind C c0 (\lambda (c1: C).(drop (S h) (r k0 d) c1 e)) H10 c H15) in 
(let H18 \def (eq_ind K k0 (\lambda (k1: K).(eq T (lift (S h) (r k1 d) u0) 
u)) H13 k H14) in (let H19 \def (eq_ind K k0 (\lambda (k1: K).((eq nat (S h) 
(S h)) \to ((eq nat (r k1 d) O) \to ((eq C c (CHead c k u)) \to (drop (r k h) 
(r k1 d) c e))))) H16 k H14) in (let H20 \def (eq_ind K k0 (\lambda (k1: 
K).(drop (S h) (r k1 d) c e)) H17 k H14) in (eq_ind_r K k (\lambda (k1: 
K).(drop (r k h) (S d) c (CHead e k1 u0))) (let H21 \def (eq_ind_r T u 
(\lambda (t: T).((eq nat (S h) (S h)) \to ((eq nat (r k d) O) \to ((eq C c 
(CHead c k t)) \to (drop (r k h) (r k d) c e))))) H19 (lift (S h) (r k d) u0) 
H18) in (let H22 \def (eq_ind nat (S d) (\lambda (ee: nat).(match ee with [O 
\Rightarrow False | (S _) \Rightarrow True])) I O H6) in (False_ind (drop (r 
k h) (S d) c (CHead e k u0)) H22))) k0 H14))))))))) H12)) H11)))))))))))))))) 
y1 y0 y x H2))) H1))) H0))) H)))))).

lemma drop_gen_skip_r:
 \forall (c: C).(\forall (x: C).(\forall (u: T).(\forall (h: nat).(\forall 
(d: nat).(\forall (k: K).((drop h (S d) x (CHead c k u)) \to (ex2 C (\lambda 
(e: C).(eq C x (CHead e k (lift h (r k d) u)))) (\lambda (e: C).(drop h (r k 
d) e c)))))))))
\def
 \lambda (c: C).(\lambda (x: C).(\lambda (u: T).(\lambda (h: nat).(\lambda 
(d: nat).(\lambda (k: K).(\lambda (H: (drop h (S d) x (CHead c k 
u))).(insert_eq C (CHead c k u) (\lambda (c0: C).(drop h (S d) x c0)) 
(\lambda (_: C).(ex2 C (\lambda (e: C).(eq C x (CHead e k (lift h (r k d) 
u)))) (\lambda (e: C).(drop h (r k d) e c)))) (\lambda (y: C).(\lambda (H0: 
(drop h (S d) x y)).(insert_eq nat (S d) (\lambda (n: nat).(drop h n x y)) 
(\lambda (_: nat).((eq C y (CHead c k u)) \to (ex2 C (\lambda (e: C).(eq C x 
(CHead e k (lift h (r k d) u)))) (\lambda (e: C).(drop h (r k d) e c))))) 
(\lambda (y0: nat).(\lambda (H1: (drop h y0 x y)).(drop_ind (\lambda (n: 
nat).(\lambda (n0: nat).(\lambda (c0: C).(\lambda (c1: C).((eq nat n0 (S d)) 
\to ((eq C c1 (CHead c k u)) \to (ex2 C (\lambda (e: C).(eq C c0 (CHead e k 
(lift n (r k d) u)))) (\lambda (e: C).(drop n (r k d) e c))))))))) (\lambda 
(c0: C).(\lambda (H2: (eq nat O (S d))).(\lambda (H3: (eq C c0 (CHead c k 
u))).(eq_ind_r C (CHead c k u) (\lambda (c1: C).(ex2 C (\lambda (e: C).(eq C 
c1 (CHead e k (lift O (r k d) u)))) (\lambda (e: C).(drop O (r k d) e c)))) 
(let H4 \def (eq_ind nat O (\lambda (ee: nat).(match ee with [O \Rightarrow 
True | (S _) \Rightarrow False])) I (S d) H2) in (False_ind (ex2 C (\lambda 
(e: C).(eq C (CHead c k u) (CHead e k (lift O (r k d) u)))) (\lambda (e: 
C).(drop O (r k d) e c))) H4)) c0 H3)))) (\lambda (k0: K).(\lambda (h0: 
nat).(\lambda (c0: C).(\lambda (e: C).(\lambda (H2: (drop (r k0 h0) O c0 
e)).(\lambda (H3: (((eq nat O (S d)) \to ((eq C e (CHead c k u)) \to (ex2 C 
(\lambda (e0: C).(eq C c0 (CHead e0 k (lift (r k0 h0) (r k d) u)))) (\lambda 
(e0: C).(drop (r k0 h0) (r k d) e0 c))))))).(\lambda (u0: T).(\lambda (H4: 
(eq nat O (S d))).(\lambda (H5: (eq C e (CHead c k u))).(let H6 \def (eq_ind 
C e (\lambda (c1: C).((eq nat O (S d)) \to ((eq C c1 (CHead c k u)) \to (ex2 
C (\lambda (e0: C).(eq C c0 (CHead e0 k (lift (r k0 h0) (r k d) u)))) 
(\lambda (e0: C).(drop (r k0 h0) (r k d) e0 c)))))) H3 (CHead c k u) H5) in 
(let H7 \def (eq_ind C e (\lambda (c1: C).(drop (r k0 h0) O c0 c1)) H2 (CHead 
c k u) H5) in (let H8 \def (eq_ind nat O (\lambda (ee: nat).(match ee with [O 
\Rightarrow True | (S _) \Rightarrow False])) I (S d) H4) in (False_ind (ex2 
C (\lambda (e0: C).(eq C (CHead c0 k0 u0) (CHead e0 k (lift (S h0) (r k d) 
u)))) (\lambda (e0: C).(drop (S h0) (r k d) e0 c))) H8))))))))))))) (\lambda 
(k0: K).(\lambda (h0: nat).(\lambda (d0: nat).(\lambda (c0: C).(\lambda (e: 
C).(\lambda (H2: (drop h0 (r k0 d0) c0 e)).(\lambda (H3: (((eq nat (r k0 d0) 
(S d)) \to ((eq C e (CHead c k u)) \to (ex2 C (\lambda (e0: C).(eq C c0 
(CHead e0 k (lift h0 (r k d) u)))) (\lambda (e0: C).(drop h0 (r k d) e0 
c))))))).(\lambda (u0: T).(\lambda (H4: (eq nat (S d0) (S d))).(\lambda (H5: 
(eq C (CHead e k0 u0) (CHead c k u))).(let H6 \def (f_equal C C (\lambda (e0: 
C).(match e0 with [(CSort _) \Rightarrow e | (CHead c1 _ _) \Rightarrow c1])) 
(CHead e k0 u0) (CHead c k u) H5) in ((let H7 \def (f_equal C K (\lambda (e0: 
C).(match e0 with [(CSort _) \Rightarrow k0 | (CHead _ k1 _) \Rightarrow 
k1])) (CHead e k0 u0) (CHead c k u) H5) in ((let H8 \def (f_equal C T 
(\lambda (e0: C).(match e0 with [(CSort _) \Rightarrow u0 | (CHead _ _ t) 
\Rightarrow t])) (CHead e k0 u0) (CHead c k u) H5) in (\lambda (H9: (eq K k0 
k)).(\lambda (H10: (eq C e c)).(eq_ind_r T u (\lambda (t: T).(ex2 C (\lambda 
(e0: C).(eq C (CHead c0 k0 (lift h0 (r k0 d0) t)) (CHead e0 k (lift h0 (r k 
d) u)))) (\lambda (e0: C).(drop h0 (r k d) e0 c)))) (let H11 \def (eq_ind C e 
(\lambda (c1: C).((eq nat (r k0 d0) (S d)) \to ((eq C c1 (CHead c k u)) \to 
(ex2 C (\lambda (e0: C).(eq C c0 (CHead e0 k (lift h0 (r k d) u)))) (\lambda 
(e0: C).(drop h0 (r k d) e0 c)))))) H3 c H10) in (let H12 \def (eq_ind C e 
(\lambda (c1: C).(drop h0 (r k0 d0) c0 c1)) H2 c H10) in (let H13 \def 
(eq_ind K k0 (\lambda (k1: K).((eq nat (r k1 d0) (S d)) \to ((eq C c (CHead c 
k u)) \to (ex2 C (\lambda (e0: C).(eq C c0 (CHead e0 k (lift h0 (r k d) u)))) 
(\lambda (e0: C).(drop h0 (r k d) e0 c)))))) H11 k H9) in (let H14 \def 
(eq_ind K k0 (\lambda (k1: K).(drop h0 (r k1 d0) c0 c)) H12 k H9) in 
(eq_ind_r K k (\lambda (k1: K).(ex2 C (\lambda (e0: C).(eq C (CHead c0 k1 
(lift h0 (r k1 d0) u)) (CHead e0 k (lift h0 (r k d) u)))) (\lambda (e0: 
C).(drop h0 (r k d) e0 c)))) (let H15 \def (f_equal nat nat (\lambda (e0: 
nat).(match e0 with [O \Rightarrow d0 | (S n) \Rightarrow n])) (S d0) (S d) 
H4) in (let H16 \def (eq_ind nat d0 (\lambda (n: nat).((eq nat (r k n) (S d)) 
\to ((eq C c (CHead c k u)) \to (ex2 C (\lambda (e0: C).(eq C c0 (CHead e0 k 
(lift h0 (r k d) u)))) (\lambda (e0: C).(drop h0 (r k d) e0 c)))))) H13 d 
H15) in (let H17 \def (eq_ind nat d0 (\lambda (n: nat).(drop h0 (r k n) c0 
c)) H14 d H15) in (eq_ind_r nat d (\lambda (n: nat).(ex2 C (\lambda (e0: 
C).(eq C (CHead c0 k (lift h0 (r k n) u)) (CHead e0 k (lift h0 (r k d) u)))) 
(\lambda (e0: C).(drop h0 (r k d) e0 c)))) (ex_intro2 C (\lambda (e0: C).(eq 
C (CHead c0 k (lift h0 (r k d) u)) (CHead e0 k (lift h0 (r k d) u)))) 
(\lambda (e0: C).(drop h0 (r k d) e0 c)) c0 (refl_equal C (CHead c0 k (lift 
h0 (r k d) u))) H17) d0 H15)))) k0 H9))))) u0 H8)))) H7)) H6)))))))))))) h y0 
x y H1))) H0))) H))))))).

lemma drop_gen_skip_l:
 \forall (c: C).(\forall (x: C).(\forall (u: T).(\forall (h: nat).(\forall 
(d: nat).(\forall (k: K).((drop h (S d) (CHead c k u) x) \to (ex3_2 C T 
(\lambda (e: C).(\lambda (v: T).(eq C x (CHead e k v)))) (\lambda (_: 
C).(\lambda (v: T).(eq T u (lift h (r k d) v)))) (\lambda (e: C).(\lambda (_: 
T).(drop h (r k d) c e))))))))))
\def
 \lambda (c: C).(\lambda (x: C).(\lambda (u: T).(\lambda (h: nat).(\lambda 
(d: nat).(\lambda (k: K).(\lambda (H: (drop h (S d) (CHead c k u) 
x)).(insert_eq C (CHead c k u) (\lambda (c0: C).(drop h (S d) c0 x)) (\lambda 
(_: C).(ex3_2 C T (\lambda (e: C).(\lambda (v: T).(eq C x (CHead e k v)))) 
(\lambda (_: C).(\lambda (v: T).(eq T u (lift h (r k d) v)))) (\lambda (e: 
C).(\lambda (_: T).(drop h (r k d) c e))))) (\lambda (y: C).(\lambda (H0: 
(drop h (S d) y x)).(insert_eq nat (S d) (\lambda (n: nat).(drop h n y x)) 
(\lambda (_: nat).((eq C y (CHead c k u)) \to (ex3_2 C T (\lambda (e: 
C).(\lambda (v: T).(eq C x (CHead e k v)))) (\lambda (_: C).(\lambda (v: 
T).(eq T u (lift h (r k d) v)))) (\lambda (e: C).(\lambda (_: T).(drop h (r k 
d) c e)))))) (\lambda (y0: nat).(\lambda (H1: (drop h y0 y x)).(drop_ind 
(\lambda (n: nat).(\lambda (n0: nat).(\lambda (c0: C).(\lambda (c1: C).((eq 
nat n0 (S d)) \to ((eq C c0 (CHead c k u)) \to (ex3_2 C T (\lambda (e: 
C).(\lambda (v: T).(eq C c1 (CHead e k v)))) (\lambda (_: C).(\lambda (v: 
T).(eq T u (lift n (r k d) v)))) (\lambda (e: C).(\lambda (_: T).(drop n (r k 
d) c e)))))))))) (\lambda (c0: C).(\lambda (H2: (eq nat O (S d))).(\lambda 
(H3: (eq C c0 (CHead c k u))).(eq_ind_r C (CHead c k u) (\lambda (c1: 
C).(ex3_2 C T (\lambda (e: C).(\lambda (v: T).(eq C c1 (CHead e k v)))) 
(\lambda (_: C).(\lambda (v: T).(eq T u (lift O (r k d) v)))) (\lambda (e: 
C).(\lambda (_: T).(drop O (r k d) c e))))) (let H4 \def (eq_ind nat O 
(\lambda (ee: nat).(match ee with [O \Rightarrow True | (S _) \Rightarrow 
False])) I (S d) H2) in (False_ind (ex3_2 C T (\lambda (e: C).(\lambda (v: 
T).(eq C (CHead c k u) (CHead e k v)))) (\lambda (_: C).(\lambda (v: T).(eq T 
u (lift O (r k d) v)))) (\lambda (e: C).(\lambda (_: T).(drop O (r k d) c 
e)))) H4)) c0 H3)))) (\lambda (k0: K).(\lambda (h0: nat).(\lambda (c0: 
C).(\lambda (e: C).(\lambda (H2: (drop (r k0 h0) O c0 e)).(\lambda (H3: (((eq 
nat O (S d)) \to ((eq C c0 (CHead c k u)) \to (ex3_2 C T (\lambda (e0: 
C).(\lambda (v: T).(eq C e (CHead e0 k v)))) (\lambda (_: C).(\lambda (v: 
T).(eq T u (lift (r k0 h0) (r k d) v)))) (\lambda (e0: C).(\lambda (_: 
T).(drop (r k0 h0) (r k d) c e0)))))))).(\lambda (u0: T).(\lambda (H4: (eq 
nat O (S d))).(\lambda (H5: (eq C (CHead c0 k0 u0) (CHead c k u))).(let H6 
\def (f_equal C C (\lambda (e0: C).(match e0 with [(CSort _) \Rightarrow c0 | 
(CHead c1 _ _) \Rightarrow c1])) (CHead c0 k0 u0) (CHead c k u) H5) in ((let 
H7 \def (f_equal C K (\lambda (e0: C).(match e0 with [(CSort _) \Rightarrow 
k0 | (CHead _ k1 _) \Rightarrow k1])) (CHead c0 k0 u0) (CHead c k u) H5) in 
((let H8 \def (f_equal C T (\lambda (e0: C).(match e0 with [(CSort _) 
\Rightarrow u0 | (CHead _ _ t) \Rightarrow t])) (CHead c0 k0 u0) (CHead c k 
u) H5) in (\lambda (H9: (eq K k0 k)).(\lambda (H10: (eq C c0 c)).(let H11 
\def (eq_ind C c0 (\lambda (c1: C).((eq nat O (S d)) \to ((eq C c1 (CHead c k 
u)) \to (ex3_2 C T (\lambda (e0: C).(\lambda (v: T).(eq C e (CHead e0 k v)))) 
(\lambda (_: C).(\lambda (v: T).(eq T u (lift (r k0 h0) (r k d) v)))) 
(\lambda (e0: C).(\lambda (_: T).(drop (r k0 h0) (r k d) c e0))))))) H3 c 
H10) in (let H12 \def (eq_ind C c0 (\lambda (c1: C).(drop (r k0 h0) O c1 e)) 
H2 c H10) in (let H13 \def (eq_ind K k0 (\lambda (k1: K).((eq nat O (S d)) 
\to ((eq C c (CHead c k u)) \to (ex3_2 C T (\lambda (e0: C).(\lambda (v: 
T).(eq C e (CHead e0 k v)))) (\lambda (_: C).(\lambda (v: T).(eq T u (lift (r 
k1 h0) (r k d) v)))) (\lambda (e0: C).(\lambda (_: T).(drop (r k1 h0) (r k d) 
c e0))))))) H11 k H9) in (let H14 \def (eq_ind K k0 (\lambda (k1: K).(drop (r 
k1 h0) O c e)) H12 k H9) in (let H15 \def (eq_ind nat O (\lambda (ee: 
nat).(match ee with [O \Rightarrow True | (S _) \Rightarrow False])) I (S d) 
H4) in (False_ind (ex3_2 C T (\lambda (e0: C).(\lambda (v: T).(eq C e (CHead 
e0 k v)))) (\lambda (_: C).(\lambda (v: T).(eq T u (lift (S h0) (r k d) v)))) 
(\lambda (e0: C).(\lambda (_: T).(drop (S h0) (r k d) c e0)))) H15))))))))) 
H7)) H6))))))))))) (\lambda (k0: K).(\lambda (h0: nat).(\lambda (d0: 
nat).(\lambda (c0: C).(\lambda (e: C).(\lambda (H2: (drop h0 (r k0 d0) c0 
e)).(\lambda (H3: (((eq nat (r k0 d0) (S d)) \to ((eq C c0 (CHead c k u)) \to 
(ex3_2 C T (\lambda (e0: C).(\lambda (v: T).(eq C e (CHead e0 k v)))) 
(\lambda (_: C).(\lambda (v: T).(eq T u (lift h0 (r k d) v)))) (\lambda (e0: 
C).(\lambda (_: T).(drop h0 (r k d) c e0)))))))).(\lambda (u0: T).(\lambda 
(H4: (eq nat (S d0) (S d))).(\lambda (H5: (eq C (CHead c0 k0 (lift h0 (r k0 
d0) u0)) (CHead c k u))).(let H6 \def (f_equal C C (\lambda (e0: C).(match e0 
with [(CSort _) \Rightarrow c0 | (CHead c1 _ _) \Rightarrow c1])) (CHead c0 
k0 (lift h0 (r k0 d0) u0)) (CHead c k u) H5) in ((let H7 \def (f_equal C K 
(\lambda (e0: C).(match e0 with [(CSort _) \Rightarrow k0 | (CHead _ k1 _) 
\Rightarrow k1])) (CHead c0 k0 (lift h0 (r k0 d0) u0)) (CHead c k u) H5) in 
((let H8 \def (f_equal C T (\lambda (e0: C).(match e0 with [(CSort _) 
\Rightarrow (lref_map (\lambda (x0: nat).(plus x0 h0)) (r k0 d0) u0) | (CHead 
_ _ t) \Rightarrow t])) (CHead c0 k0 (lift h0 (r k0 d0) u0)) (CHead c k u) 
H5) in (\lambda (H9: (eq K k0 k)).(\lambda (H10: (eq C c0 c)).(let H11 \def 
(eq_ind C c0 (\lambda (c1: C).((eq nat (r k0 d0) (S d)) \to ((eq C c1 (CHead 
c k u)) \to (ex3_2 C T (\lambda (e0: C).(\lambda (v: T).(eq C e (CHead e0 k 
v)))) (\lambda (_: C).(\lambda (v: T).(eq T u (lift h0 (r k d) v)))) (\lambda 
(e0: C).(\lambda (_: T).(drop h0 (r k d) c e0))))))) H3 c H10) in (let H12 
\def (eq_ind C c0 (\lambda (c1: C).(drop h0 (r k0 d0) c1 e)) H2 c H10) in 
(let H13 \def (eq_ind K k0 (\lambda (k1: K).(eq T (lift h0 (r k1 d0) u0) u)) 
H8 k H9) in (let H14 \def (eq_ind K k0 (\lambda (k1: K).((eq nat (r k1 d0) (S 
d)) \to ((eq C c (CHead c k u)) \to (ex3_2 C T (\lambda (e0: C).(\lambda (v: 
T).(eq C e (CHead e0 k v)))) (\lambda (_: C).(\lambda (v: T).(eq T u (lift h0 
(r k d) v)))) (\lambda (e0: C).(\lambda (_: T).(drop h0 (r k d) c e0))))))) 
H11 k H9) in (let H15 \def (eq_ind K k0 (\lambda (k1: K).(drop h0 (r k1 d0) c 
e)) H12 k H9) in (eq_ind_r K k (\lambda (k1: K).(ex3_2 C T (\lambda (e0: 
C).(\lambda (v: T).(eq C (CHead e k1 u0) (CHead e0 k v)))) (\lambda (_: 
C).(\lambda (v: T).(eq T u (lift h0 (r k d) v)))) (\lambda (e0: C).(\lambda 
(_: T).(drop h0 (r k d) c e0))))) (let H16 \def (eq_ind_r T u (\lambda (t: 
T).((eq nat (r k d0) (S d)) \to ((eq C c (CHead c k t)) \to (ex3_2 C T 
(\lambda (e0: C).(\lambda (v: T).(eq C e (CHead e0 k v)))) (\lambda (_: 
C).(\lambda (v: T).(eq T t (lift h0 (r k d) v)))) (\lambda (e0: C).(\lambda 
(_: T).(drop h0 (r k d) c e0))))))) H14 (lift h0 (r k d0) u0) H13) in (eq_ind 
T (lift h0 (r k d0) u0) (\lambda (t: T).(ex3_2 C T (\lambda (e0: C).(\lambda 
(v: T).(eq C (CHead e k u0) (CHead e0 k v)))) (\lambda (_: C).(\lambda (v: 
T).(eq T t (lift h0 (r k d) v)))) (\lambda (e0: C).(\lambda (_: T).(drop h0 
(r k d) c e0))))) (let H17 \def (f_equal nat nat (\lambda (e0: nat).(match e0 
with [O \Rightarrow d0 | (S n) \Rightarrow n])) (S d0) (S d) H4) in (let H18 
\def (eq_ind nat d0 (\lambda (n: nat).((eq nat (r k n) (S d)) \to ((eq C c 
(CHead c k (lift h0 (r k n) u0))) \to (ex3_2 C T (\lambda (e0: C).(\lambda 
(v: T).(eq C e (CHead e0 k v)))) (\lambda (_: C).(\lambda (v: T).(eq T (lift 
h0 (r k n) u0) (lift h0 (r k d) v)))) (\lambda (e0: C).(\lambda (_: T).(drop 
h0 (r k d) c e0))))))) H16 d H17) in (let H19 \def (eq_ind nat d0 (\lambda 
(n: nat).(drop h0 (r k n) c e)) H15 d H17) in (eq_ind_r nat d (\lambda (n: 
nat).(ex3_2 C T (\lambda (e0: C).(\lambda (v: T).(eq C (CHead e k u0) (CHead 
e0 k v)))) (\lambda (_: C).(\lambda (v: T).(eq T (lift h0 (r k n) u0) (lift 
h0 (r k d) v)))) (\lambda (e0: C).(\lambda (_: T).(drop h0 (r k d) c e0))))) 
(ex3_2_intro C T (\lambda (e0: C).(\lambda (v: T).(eq C (CHead e k u0) (CHead 
e0 k v)))) (\lambda (_: C).(\lambda (v: T).(eq T (lift h0 (r k d) u0) (lift 
h0 (r k d) v)))) (\lambda (e0: C).(\lambda (_: T).(drop h0 (r k d) c e0))) e 
u0 (refl_equal C (CHead e k u0)) (refl_equal T (lift h0 (r k d) u0)) H19) d0 
H17)))) u H13)) k0 H9))))))))) H7)) H6)))))))))))) h y0 y x H1))) H0))) 
H))))))).

lemma drop_S:
 \forall (b: B).(\forall (c: C).(\forall (e: C).(\forall (u: T).(\forall (h: 
nat).((drop h O c (CHead e (Bind b) u)) \to (drop (S h) O c e))))))
\def
 \lambda (b: B).(\lambda (c: C).(C_ind (\lambda (c0: C).(\forall (e: 
C).(\forall (u: T).(\forall (h: nat).((drop h O c0 (CHead e (Bind b) u)) \to 
(drop (S h) O c0 e)))))) (\lambda (n: nat).(\lambda (e: C).(\lambda (u: 
T).(\lambda (h: nat).(\lambda (H: (drop h O (CSort n) (CHead e (Bind b) 
u))).(and3_ind (eq C (CHead e (Bind b) u) (CSort n)) (eq nat h O) (eq nat O 
O) (drop (S h) O (CSort n) e) (\lambda (H0: (eq C (CHead e (Bind b) u) (CSort 
n))).(\lambda (H1: (eq nat h O)).(\lambda (_: (eq nat O O)).(eq_ind_r nat O 
(\lambda (n0: nat).(drop (S n0) O (CSort n) e)) (let H3 \def (eq_ind C (CHead 
e (Bind b) u) (\lambda (ee: C).(match ee with [(CSort _) \Rightarrow False | 
(CHead _ _ _) \Rightarrow True])) I (CSort n) H0) in (False_ind (drop (S O) O 
(CSort n) e) H3)) h H1)))) (drop_gen_sort n h O (CHead e (Bind b) u) H))))))) 
(\lambda (c0: C).(\lambda (H: ((\forall (e: C).(\forall (u: T).(\forall (h: 
nat).((drop h O c0 (CHead e (Bind b) u)) \to (drop (S h) O c0 
e))))))).(\lambda (k: K).(\lambda (t: T).(\lambda (e: C).(\lambda (u: 
T).(\lambda (h: nat).(nat_ind (\lambda (n: nat).((drop n O (CHead c0 k t) 
(CHead e (Bind b) u)) \to (drop (S n) O (CHead c0 k t) e))) (\lambda (H0: 
(drop O O (CHead c0 k t) (CHead e (Bind b) u))).(let H1 \def (f_equal C C 
(\lambda (e0: C).(match e0 with [(CSort _) \Rightarrow c0 | (CHead c1 _ _) 
\Rightarrow c1])) (CHead c0 k t) (CHead e (Bind b) u) (drop_gen_refl (CHead 
c0 k t) (CHead e (Bind b) u) H0)) in ((let H2 \def (f_equal C K (\lambda (e0: 
C).(match e0 with [(CSort _) \Rightarrow k | (CHead _ k0 _) \Rightarrow k0])) 
(CHead c0 k t) (CHead e (Bind b) u) (drop_gen_refl (CHead c0 k t) (CHead e 
(Bind b) u) H0)) in ((let H3 \def (f_equal C T (\lambda (e0: C).(match e0 
with [(CSort _) \Rightarrow t | (CHead _ _ t0) \Rightarrow t0])) (CHead c0 k 
t) (CHead e (Bind b) u) (drop_gen_refl (CHead c0 k t) (CHead e (Bind b) u) 
H0)) in (\lambda (H4: (eq K k (Bind b))).(\lambda (H5: (eq C c0 e)).(eq_ind C 
c0 (\lambda (c1: C).(drop (S O) O (CHead c0 k t) c1)) (eq_ind_r K (Bind b) 
(\lambda (k0: K).(drop (S O) O (CHead c0 k0 t) c0)) (drop_drop (Bind b) O c0 
c0 (drop_refl c0) t) k H4) e H5)))) H2)) H1))) (\lambda (n: nat).(\lambda (_: 
(((drop n O (CHead c0 k t) (CHead e (Bind b) u)) \to (drop (S n) O (CHead c0 
k t) e)))).(\lambda (H1: (drop (S n) O (CHead c0 k t) (CHead e (Bind b) 
u))).(drop_drop k (S n) c0 e (eq_ind_r nat (S (r k n)) (\lambda (n0: 
nat).(drop n0 O c0 e)) (H e u (r k n) (drop_gen_drop k c0 (CHead e (Bind b) 
u) t n H1)) (r k (S n)) (r_S k n)) t)))) h)))))))) c)).

theorem drop_mono:
 \forall (c: C).(\forall (x1: C).(\forall (d: nat).(\forall (h: nat).((drop h 
d c x1) \to (\forall (x2: C).((drop h d c x2) \to (eq C x1 x2)))))))
\def
 \lambda (c: C).(C_ind (\lambda (c0: C).(\forall (x1: C).(\forall (d: 
nat).(\forall (h: nat).((drop h d c0 x1) \to (\forall (x2: C).((drop h d c0 
x2) \to (eq C x1 x2)))))))) (\lambda (n: nat).(\lambda (x1: C).(\lambda (d: 
nat).(\lambda (h: nat).(\lambda (H: (drop h d (CSort n) x1)).(\lambda (x2: 
C).(\lambda (H0: (drop h d (CSort n) x2)).(and3_ind (eq C x2 (CSort n)) (eq 
nat h O) (eq nat d O) (eq C x1 x2) (\lambda (H1: (eq C x2 (CSort 
n))).(\lambda (H2: (eq nat h O)).(\lambda (H3: (eq nat d O)).(and3_ind (eq C 
x1 (CSort n)) (eq nat h O) (eq nat d O) (eq C x1 x2) (\lambda (H4: (eq C x1 
(CSort n))).(\lambda (H5: (eq nat h O)).(\lambda (H6: (eq nat d O)).(eq_ind_r 
C (CSort n) (\lambda (c0: C).(eq C x1 c0)) (let H7 \def (eq_ind nat h 
(\lambda (n0: nat).(eq nat n0 O)) H2 O H5) in (let H8 \def (eq_ind nat d 
(\lambda (n0: nat).(eq nat n0 O)) H3 O H6) in (eq_ind_r C (CSort n) (\lambda 
(c0: C).(eq C c0 (CSort n))) (refl_equal C (CSort n)) x1 H4))) x2 H1)))) 
(drop_gen_sort n h d x1 H))))) (drop_gen_sort n h d x2 H0))))))))) (\lambda 
(c0: C).(\lambda (H: ((\forall (x1: C).(\forall (d: nat).(\forall (h: 
nat).((drop h d c0 x1) \to (\forall (x2: C).((drop h d c0 x2) \to (eq C x1 
x2))))))))).(\lambda (k: K).(\lambda (t: T).(\lambda (x1: C).(\lambda (d: 
nat).(nat_ind (\lambda (n: nat).(\forall (h: nat).((drop h n (CHead c0 k t) 
x1) \to (\forall (x2: C).((drop h n (CHead c0 k t) x2) \to (eq C x1 x2)))))) 
(\lambda (h: nat).(nat_ind (\lambda (n: nat).((drop n O (CHead c0 k t) x1) 
\to (\forall (x2: C).((drop n O (CHead c0 k t) x2) \to (eq C x1 x2))))) 
(\lambda (H0: (drop O O (CHead c0 k t) x1)).(\lambda (x2: C).(\lambda (H1: 
(drop O O (CHead c0 k t) x2)).(eq_ind C (CHead c0 k t) (\lambda (c1: C).(eq C 
x1 c1)) (eq_ind C (CHead c0 k t) (\lambda (c1: C).(eq C c1 (CHead c0 k t))) 
(refl_equal C (CHead c0 k t)) x1 (drop_gen_refl (CHead c0 k t) x1 H0)) x2 
(drop_gen_refl (CHead c0 k t) x2 H1))))) (\lambda (n: nat).(\lambda (_: 
(((drop n O (CHead c0 k t) x1) \to (\forall (x2: C).((drop n O (CHead c0 k t) 
x2) \to (eq C x1 x2)))))).(\lambda (H1: (drop (S n) O (CHead c0 k t) 
x1)).(\lambda (x2: C).(\lambda (H2: (drop (S n) O (CHead c0 k t) x2)).(H x1 O 
(r k n) (drop_gen_drop k c0 x1 t n H1) x2 (drop_gen_drop k c0 x2 t n 
H2))))))) h)) (\lambda (n: nat).(\lambda (H0: ((\forall (h: nat).((drop h n 
(CHead c0 k t) x1) \to (\forall (x2: C).((drop h n (CHead c0 k t) x2) \to (eq 
C x1 x2))))))).(\lambda (h: nat).(\lambda (H1: (drop h (S n) (CHead c0 k t) 
x1)).(\lambda (x2: C).(\lambda (H2: (drop h (S n) (CHead c0 k t) 
x2)).(ex3_2_ind C T (\lambda (e: C).(\lambda (v: T).(eq C x2 (CHead e k v)))) 
(\lambda (_: C).(\lambda (v: T).(eq T t (lift h (r k n) v)))) (\lambda (e: 
C).(\lambda (_: T).(drop h (r k n) c0 e))) (eq C x1 x2) (\lambda (x0: 
C).(\lambda (x3: T).(\lambda (H3: (eq C x2 (CHead x0 k x3))).(\lambda (H4: 
(eq T t (lift h (r k n) x3))).(\lambda (H5: (drop h (r k n) c0 
x0)).(ex3_2_ind C T (\lambda (e: C).(\lambda (v: T).(eq C x1 (CHead e k v)))) 
(\lambda (_: C).(\lambda (v: T).(eq T t (lift h (r k n) v)))) (\lambda (e: 
C).(\lambda (_: T).(drop h (r k n) c0 e))) (eq C x1 x2) (\lambda (x4: 
C).(\lambda (x5: T).(\lambda (H6: (eq C x1 (CHead x4 k x5))).(\lambda (H7: 
(eq T t (lift h (r k n) x5))).(\lambda (H8: (drop h (r k n) c0 x4)).(eq_ind_r 
C (CHead x0 k x3) (\lambda (c1: C).(eq C x1 c1)) (let H9 \def (eq_ind C x1 
(\lambda (c1: C).(\forall (h0: nat).((drop h0 n (CHead c0 k t) c1) \to 
(\forall (x6: C).((drop h0 n (CHead c0 k t) x6) \to (eq C c1 x6)))))) H0 
(CHead x4 k x5) H6) in (eq_ind_r C (CHead x4 k x5) (\lambda (c1: C).(eq C c1 
(CHead x0 k x3))) (let H10 \def (eq_ind T t (\lambda (t0: T).(\forall (h0: 
nat).((drop h0 n (CHead c0 k t0) (CHead x4 k x5)) \to (\forall (x6: C).((drop 
h0 n (CHead c0 k t0) x6) \to (eq C (CHead x4 k x5) x6)))))) H9 (lift h (r k 
n) x5) H7) in (let H11 \def (eq_ind T t (\lambda (t0: T).(eq T t0 (lift h (r 
k n) x3))) H4 (lift h (r k n) x5) H7) in (let H12 \def (eq_ind T x5 (\lambda 
(t0: T).(\forall (h0: nat).((drop h0 n (CHead c0 k (lift h (r k n) t0)) 
(CHead x4 k t0)) \to (\forall (x6: C).((drop h0 n (CHead c0 k (lift h (r k n) 
t0)) x6) \to (eq C (CHead x4 k t0) x6)))))) H10 x3 (lift_inj x5 x3 h (r k n) 
H11)) in (eq_ind_r T x3 (\lambda (t0: T).(eq C (CHead x4 k t0) (CHead x0 k 
x3))) (sym_eq C (CHead x0 k x3) (CHead x4 k x3) (sym_eq C (CHead x4 k x3) 
(CHead x0 k x3) (sym_eq C (CHead x0 k x3) (CHead x4 k x3) (f_equal3 C K T C 
CHead x0 x4 k k x3 x3 (H x0 (r k n) h H5 x4 H8) (refl_equal K k) (refl_equal 
T x3))))) x5 (lift_inj x5 x3 h (r k n) H11))))) x1 H6)) x2 H3)))))) 
(drop_gen_skip_l c0 x1 t h n k H1))))))) (drop_gen_skip_l c0 x2 t h n k 
H2)))))))) d))))))) c).

