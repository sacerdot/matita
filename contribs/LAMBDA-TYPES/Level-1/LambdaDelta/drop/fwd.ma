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

set "baseuri" "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/drop/fwd".

include "drop/defs.ma".

theorem drop_gen_sort:
 \forall (n: nat).(\forall (h: nat).(\forall (d: nat).(\forall (x: C).((drop 
h d (CSort n) x) \to (and3 (eq C x (CSort n)) (eq nat h O) (eq nat d O))))))
\def
 \lambda (n: nat).(\lambda (h: nat).(\lambda (d: nat).(\lambda (x: 
C).(\lambda (H: (drop h d (CSort n) x)).(insert_eq C (CSort n) (\lambda (c: 
C).(drop h d c x)) (and3 (eq C x (CSort n)) (eq nat h O) (eq nat d O)) 
(\lambda (y: C).(\lambda (H0: (drop h d y x)).(drop_ind (\lambda (n0: 
nat).(\lambda (n1: nat).(\lambda (c: C).(\lambda (c0: C).((eq C c (CSort n)) 
\to (and3 (eq C c0 (CSort n)) (eq nat n0 O) (eq nat n1 O))))))) (\lambda (c: 
C).(\lambda (H1: (eq C c (CSort n))).(let H2 \def (f_equal C C (\lambda (e: 
C).e) c (CSort n) H1) in (eq_ind_r C (CSort n) (\lambda (c0: C).(and3 (eq C 
c0 (CSort n)) (eq nat O O) (eq nat O O))) (and3_intro (eq C (CSort n) (CSort 
n)) (eq nat O O) (eq nat O O) (refl_equal C (CSort n)) (refl_equal nat O) 
(refl_equal nat O)) c H2)))) (\lambda (k: K).(\lambda (h0: nat).(\lambda (c: 
C).(\lambda (e: C).(\lambda (_: (drop (r k h0) O c e)).(\lambda (_: (((eq C c 
(CSort n)) \to (and3 (eq C e (CSort n)) (eq nat (r k h0) O) (eq nat O 
O))))).(\lambda (u: T).(\lambda (H3: (eq C (CHead c k u) (CSort n))).(let H4 
\def (eq_ind C (CHead c k u) (\lambda (ee: C).(match ee in C return (\lambda 
(_: C).Prop) with [(CSort _) \Rightarrow False | (CHead _ _ _) \Rightarrow 
True])) I (CSort n) H3) in (False_ind (and3 (eq C e (CSort n)) (eq nat (S h0) 
O) (eq nat O O)) H4)))))))))) (\lambda (k: K).(\lambda (h0: nat).(\lambda 
(d0: nat).(\lambda (c: C).(\lambda (e: C).(\lambda (_: (drop h0 (r k d0) c 
e)).(\lambda (_: (((eq C c (CSort n)) \to (and3 (eq C e (CSort n)) (eq nat h0 
O) (eq nat (r k d0) O))))).(\lambda (u: T).(\lambda (H3: (eq C (CHead c k 
(lift h0 (r k d0) u)) (CSort n))).(let H4 \def (eq_ind C (CHead c k (lift h0 
(r k d0) u)) (\lambda (ee: C).(match ee in C return (\lambda (_: C).Prop) 
with [(CSort _) \Rightarrow False | (CHead _ _ _) \Rightarrow True])) I 
(CSort n) H3) in (False_ind (and3 (eq C (CHead e k u) (CSort n)) (eq nat h0 
O) (eq nat (S d0) O)) H4))))))))))) h d y x H0))) H))))).

theorem drop_gen_refl:
 \forall (x: C).(\forall (e: C).((drop O O x e) \to (eq C x e)))
\def
 \lambda (x: C).(\lambda (e: C).(\lambda (H: (drop O O x e)).(insert_eq nat O 
(\lambda (n: nat).(drop n O x e)) (eq C x e) (\lambda (y: nat).(\lambda (H0: 
(drop y O x e)).(insert_eq nat O (\lambda (n: nat).(drop y n x e)) ((eq nat y 
O) \to (eq C x e)) (\lambda (y0: nat).(\lambda (H1: (drop y y0 x 
e)).(drop_ind (\lambda (n: nat).(\lambda (n0: nat).(\lambda (c: C).(\lambda 
(c0: C).((eq nat n0 O) \to ((eq nat n O) \to (eq C c c0))))))) (\lambda (c: 
C).(\lambda (_: (eq nat O O)).(\lambda (_: (eq nat O O)).(refl_equal C c)))) 
(\lambda (k: K).(\lambda (h: nat).(\lambda (c: C).(\lambda (e0: C).(\lambda 
(_: (drop (r k h) O c e0)).(\lambda (_: (((eq nat O O) \to ((eq nat (r k h) 
O) \to (eq C c e0))))).(\lambda (u: T).(\lambda (_: (eq nat O O)).(\lambda 
(H5: (eq nat (S h) O)).(let H6 \def (eq_ind nat (S h) (\lambda (ee: 
nat).(match ee in nat return (\lambda (_: nat).Prop) with [O \Rightarrow 
False | (S _) \Rightarrow True])) I O H5) in (False_ind (eq C (CHead c k u) 
e0) H6))))))))))) (\lambda (k: K).(\lambda (h: nat).(\lambda (d: 
nat).(\lambda (c: C).(\lambda (e0: C).(\lambda (H2: (drop h (r k d) c 
e0)).(\lambda (H3: (((eq nat (r k d) O) \to ((eq nat h O) \to (eq C c 
e0))))).(\lambda (u: T).(\lambda (H4: (eq nat (S d) O)).(\lambda (H5: (eq nat 
h O)).(let H6 \def (f_equal nat nat (\lambda (e1: nat).e1) h O H5) in (let H7 
\def (eq_ind nat h (\lambda (n: nat).((eq nat (r k d) O) \to ((eq nat n O) 
\to (eq C c e0)))) H3 O H6) in (let H8 \def (eq_ind nat h (\lambda (n: 
nat).(drop n (r k d) c e0)) H2 O H6) in (eq_ind_r nat O (\lambda (n: nat).(eq 
C (CHead c k (lift n (r k d) u)) (CHead e0 k u))) (let H9 \def (eq_ind nat (S 
d) (\lambda (ee: nat).(match ee in nat return (\lambda (_: nat).Prop) with [O 
\Rightarrow False | (S _) \Rightarrow True])) I O H4) in (False_ind (eq C 
(CHead c k (lift O (r k d) u)) (CHead e0 k u)) H9)) h H6)))))))))))))) y y0 x 
e H1))) H0))) H))).

theorem drop_gen_drop:
 \forall (k: K).(\forall (c: C).(\forall (x: C).(\forall (u: T).(\forall (h: 
nat).((drop (S h) O (CHead c k u) x) \to (drop (r k h) O c x))))))
\def
 \lambda (k: K).(\lambda (c: C).(\lambda (x: C).(\lambda (u: T).(\lambda (h: 
nat).(\lambda (H: (drop (S h) O (CHead c k u) x)).(insert_eq C (CHead c k u) 
(\lambda (c0: C).(drop (S h) O c0 x)) (drop (r k h) O c x) (\lambda (y: 
C).(\lambda (H0: (drop (S h) O y x)).(insert_eq nat O (\lambda (n: nat).(drop 
(S h) n y x)) ((eq C y (CHead c k u)) \to (drop (r k h) O c x)) (\lambda (y0: 
nat).(\lambda (H1: (drop (S h) y0 y x)).(insert_eq nat (S h) (\lambda (n: 
nat).(drop n y0 y x)) ((eq nat y0 O) \to ((eq C y (CHead c k u)) \to (drop (r 
k h) O c x))) (\lambda (y1: nat).(\lambda (H2: (drop y1 y0 y x)).(drop_ind 
(\lambda (n: nat).(\lambda (n0: nat).(\lambda (c0: C).(\lambda (c1: C).((eq 
nat n (S h)) \to ((eq nat n0 O) \to ((eq C c0 (CHead c k u)) \to (drop (r k 
h) O c c1)))))))) (\lambda (c0: C).(\lambda (H3: (eq nat O (S h))).(\lambda 
(_: (eq nat O O)).(\lambda (_: (eq C c0 (CHead c k u))).(let H6 \def (match 
H3 in eq return (\lambda (n: nat).(\lambda (_: (eq ? ? n)).((eq nat n (S h)) 
\to (drop (r k h) O c c0)))) with [refl_equal \Rightarrow (\lambda (H6: (eq 
nat O (S h))).(let H7 \def (eq_ind nat O (\lambda (e: nat).(match e in nat 
return (\lambda (_: nat).Prop) with [O \Rightarrow True | (S _) \Rightarrow 
False])) I (S h) H6) in (False_ind (drop (r k h) O c c0) H7)))]) in (H6 
(refl_equal nat (S h)))))))) (\lambda (k0: K).(\lambda (h0: nat).(\lambda 
(c0: C).(\lambda (e: C).(\lambda (H3: (drop (r k0 h0) O c0 e)).(\lambda (_: 
(((eq nat (r k0 h0) (S h)) \to ((eq nat O O) \to ((eq C c0 (CHead c k u)) \to 
(drop (r k h) O c e)))))).(\lambda (u0: T).(\lambda (H5: (eq nat (S h0) (S 
h))).(\lambda (_: (eq nat O O)).(\lambda (H7: (eq C (CHead c0 k0 u0) (CHead c 
k u))).(let H8 \def (match H5 in eq return (\lambda (n: nat).(\lambda (_: (eq 
? ? n)).((eq nat n (S h)) \to (drop (r k h) O c e)))) with [refl_equal 
\Rightarrow (\lambda (H8: (eq nat (S h0) (S h))).(let H9 \def (f_equal nat 
nat (\lambda (e0: nat).(match e0 in nat return (\lambda (_: nat).nat) with [O 
\Rightarrow h0 | (S n) \Rightarrow n])) (S h0) (S h) H8) in (eq_ind nat h 
(\lambda (_: nat).(drop (r k h) O c e)) (let H10 \def (match H7 in eq return 
(\lambda (c1: C).(\lambda (_: (eq ? ? c1)).((eq C c1 (CHead c k u)) \to (drop 
(r k h) O c e)))) with [refl_equal \Rightarrow (\lambda (H10: (eq C (CHead c0 
k0 u0) (CHead c k u))).(let H11 \def (f_equal C T (\lambda (e0: C).(match e0 
in C return (\lambda (_: C).T) with [(CSort _) \Rightarrow u0 | (CHead _ _ t) 
\Rightarrow t])) (CHead c0 k0 u0) (CHead c k u) H10) in ((let H12 \def 
(f_equal C K (\lambda (e0: C).(match e0 in C return (\lambda (_: C).K) with 
[(CSort _) \Rightarrow k0 | (CHead _ k1 _) \Rightarrow k1])) (CHead c0 k0 u0) 
(CHead c k u) H10) in ((let H13 \def (f_equal C C (\lambda (e0: C).(match e0 
in C return (\lambda (_: C).C) with [(CSort _) \Rightarrow c0 | (CHead c1 _ 
_) \Rightarrow c1])) (CHead c0 k0 u0) (CHead c k u) H10) in (eq_ind C c 
(\lambda (_: C).((eq K k0 k) \to ((eq T u0 u) \to (drop (r k h) O c e)))) 
(\lambda (H14: (eq K k0 k)).(eq_ind K k (\lambda (_: K).((eq T u0 u) \to 
(drop (r k h) O c e))) (\lambda (H15: (eq T u0 u)).(eq_ind T u (\lambda (_: 
T).(drop (r k h) O c e)) (eq_ind nat h0 (\lambda (n: nat).(drop (r k n) O c 
e)) (eq_ind C c0 (\lambda (c1: C).(drop (r k h0) O c1 e)) (eq_ind K k0 
(\lambda (k1: K).(drop (r k1 h0) O c0 e)) H3 k H14) c H13) h H9) u0 (sym_eq T 
u0 u H15))) k0 (sym_eq K k0 k H14))) c0 (sym_eq C c0 c H13))) H12)) H11)))]) 
in (H10 (refl_equal C (CHead c k u)))) h0 (sym_eq nat h0 h H9))))]) in (H8 
(refl_equal nat (S h)))))))))))))) (\lambda (k0: K).(\lambda (h0: 
nat).(\lambda (d: nat).(\lambda (c0: C).(\lambda (e: C).(\lambda (_: (drop h0 
(r k0 d) c0 e)).(\lambda (_: (((eq nat h0 (S h)) \to ((eq nat (r k0 d) O) \to 
((eq C c0 (CHead c k u)) \to (drop (r k h) O c e)))))).(\lambda (u0: 
T).(\lambda (_: (eq nat h0 (S h))).(\lambda (H6: (eq nat (S d) O)).(\lambda 
(_: (eq C (CHead c0 k0 (lift h0 (r k0 d) u0)) (CHead c k u))).(let H8 \def 
(match H6 in eq return (\lambda (n: nat).(\lambda (_: (eq ? ? n)).((eq nat n 
O) \to (drop (r k h) O c (CHead e k0 u0))))) with [refl_equal \Rightarrow 
(\lambda (H8: (eq nat (S d) O)).(let H9 \def (eq_ind nat (S d) (\lambda (e0: 
nat).(match e0 in nat return (\lambda (_: nat).Prop) with [O \Rightarrow 
False | (S _) \Rightarrow True])) I O H8) in (False_ind (drop (r k h) O c 
(CHead e k0 u0)) H9)))]) in (H8 (refl_equal nat O)))))))))))))) y1 y0 y x 
H2))) H1))) H0))) H)))))).

theorem drop_gen_skip_r:
 \forall (c: C).(\forall (x: C).(\forall (u: T).(\forall (h: nat).(\forall 
(d: nat).(\forall (k: K).((drop h (S d) x (CHead c k u)) \to (ex2 C (\lambda 
(e: C).(eq C x (CHead e k (lift h (r k d) u)))) (\lambda (e: C).(drop h (r k 
d) e c)))))))))
\def
 \lambda (c: C).(\lambda (x: C).(\lambda (u: T).(\lambda (h: nat).(\lambda 
(d: nat).(\lambda (k: K).(\lambda (H: (drop h (S d) x (CHead c k u))).(let H0 
\def (match H in drop return (\lambda (n: nat).(\lambda (n0: nat).(\lambda 
(c0: C).(\lambda (c1: C).(\lambda (_: (drop n n0 c0 c1)).((eq nat n h) \to 
((eq nat n0 (S d)) \to ((eq C c0 x) \to ((eq C c1 (CHead c k u)) \to (ex2 C 
(\lambda (e: C).(eq C x (CHead e k (lift h (r k d) u)))) (\lambda (e: 
C).(drop h (r k d) e c)))))))))))) with [(drop_refl c0) \Rightarrow (\lambda 
(H0: (eq nat O h)).(\lambda (H1: (eq nat O (S d))).(\lambda (H2: (eq C c0 
x)).(\lambda (H3: (eq C c0 (CHead c k u))).(eq_ind nat O (\lambda (n: 
nat).((eq nat O (S d)) \to ((eq C c0 x) \to ((eq C c0 (CHead c k u)) \to (ex2 
C (\lambda (e: C).(eq C x (CHead e k (lift n (r k d) u)))) (\lambda (e: 
C).(drop n (r k d) e c))))))) (\lambda (H4: (eq nat O (S d))).(let H5 \def 
(eq_ind nat O (\lambda (e: nat).(match e in nat return (\lambda (_: 
nat).Prop) with [O \Rightarrow True | (S _) \Rightarrow False])) I (S d) H4) 
in (False_ind ((eq C c0 x) \to ((eq C c0 (CHead c k u)) \to (ex2 C (\lambda 
(e: C).(eq C x (CHead e k (lift O (r k d) u)))) (\lambda (e: C).(drop O (r k 
d) e c))))) H5))) h H0 H1 H2 H3))))) | (drop_drop k0 h0 c0 e H0 u0) 
\Rightarrow (\lambda (H1: (eq nat (S h0) h)).(\lambda (H2: (eq nat O (S 
d))).(\lambda (H3: (eq C (CHead c0 k0 u0) x)).(\lambda (H4: (eq C e (CHead c 
k u))).(eq_ind nat (S h0) (\lambda (n: nat).((eq nat O (S d)) \to ((eq C 
(CHead c0 k0 u0) x) \to ((eq C e (CHead c k u)) \to ((drop (r k0 h0) O c0 e) 
\to (ex2 C (\lambda (e0: C).(eq C x (CHead e0 k (lift n (r k d) u)))) 
(\lambda (e0: C).(drop n (r k d) e0 c)))))))) (\lambda (H5: (eq nat O (S 
d))).(let H6 \def (eq_ind nat O (\lambda (e0: nat).(match e0 in nat return 
(\lambda (_: nat).Prop) with [O \Rightarrow True | (S _) \Rightarrow False])) 
I (S d) H5) in (False_ind ((eq C (CHead c0 k0 u0) x) \to ((eq C e (CHead c k 
u)) \to ((drop (r k0 h0) O c0 e) \to (ex2 C (\lambda (e0: C).(eq C x (CHead 
e0 k (lift (S h0) (r k d) u)))) (\lambda (e0: C).(drop (S h0) (r k d) e0 
c)))))) H6))) h H1 H2 H3 H4 H0))))) | (drop_skip k0 h0 d0 c0 e H0 u0) 
\Rightarrow (\lambda (H1: (eq nat h0 h)).(\lambda (H2: (eq nat (S d0) (S 
d))).(\lambda (H3: (eq C (CHead c0 k0 (lift h0 (r k0 d0) u0)) x)).(\lambda 
(H4: (eq C (CHead e k0 u0) (CHead c k u))).(eq_ind nat h (\lambda (n: 
nat).((eq nat (S d0) (S d)) \to ((eq C (CHead c0 k0 (lift n (r k0 d0) u0)) x) 
\to ((eq C (CHead e k0 u0) (CHead c k u)) \to ((drop n (r k0 d0) c0 e) \to 
(ex2 C (\lambda (e0: C).(eq C x (CHead e0 k (lift h (r k d) u)))) (\lambda 
(e0: C).(drop h (r k d) e0 c)))))))) (\lambda (H5: (eq nat (S d0) (S 
d))).(let H6 \def (f_equal nat nat (\lambda (e0: nat).(match e0 in nat return 
(\lambda (_: nat).nat) with [O \Rightarrow d0 | (S n) \Rightarrow n])) (S d0) 
(S d) H5) in (eq_ind nat d (\lambda (n: nat).((eq C (CHead c0 k0 (lift h (r 
k0 n) u0)) x) \to ((eq C (CHead e k0 u0) (CHead c k u)) \to ((drop h (r k0 n) 
c0 e) \to (ex2 C (\lambda (e0: C).(eq C x (CHead e0 k (lift h (r k d) u)))) 
(\lambda (e0: C).(drop h (r k d) e0 c))))))) (\lambda (H7: (eq C (CHead c0 k0 
(lift h (r k0 d) u0)) x)).(eq_ind C (CHead c0 k0 (lift h (r k0 d) u0)) 
(\lambda (c1: C).((eq C (CHead e k0 u0) (CHead c k u)) \to ((drop h (r k0 d) 
c0 e) \to (ex2 C (\lambda (e0: C).(eq C c1 (CHead e0 k (lift h (r k d) u)))) 
(\lambda (e0: C).(drop h (r k d) e0 c)))))) (\lambda (H8: (eq C (CHead e k0 
u0) (CHead c k u))).(let H9 \def (f_equal C T (\lambda (e0: C).(match e0 in C 
return (\lambda (_: C).T) with [(CSort _) \Rightarrow u0 | (CHead _ _ t) 
\Rightarrow t])) (CHead e k0 u0) (CHead c k u) H8) in ((let H10 \def (f_equal 
C K (\lambda (e0: C).(match e0 in C return (\lambda (_: C).K) with [(CSort _) 
\Rightarrow k0 | (CHead _ k1 _) \Rightarrow k1])) (CHead e k0 u0) (CHead c k 
u) H8) in ((let H11 \def (f_equal C C (\lambda (e0: C).(match e0 in C return 
(\lambda (_: C).C) with [(CSort _) \Rightarrow e | (CHead c1 _ _) \Rightarrow 
c1])) (CHead e k0 u0) (CHead c k u) H8) in (eq_ind C c (\lambda (c1: C).((eq 
K k0 k) \to ((eq T u0 u) \to ((drop h (r k0 d) c0 c1) \to (ex2 C (\lambda 
(e0: C).(eq C (CHead c0 k0 (lift h (r k0 d) u0)) (CHead e0 k (lift h (r k d) 
u)))) (\lambda (e0: C).(drop h (r k d) e0 c))))))) (\lambda (H12: (eq K k0 
k)).(eq_ind K k (\lambda (k1: K).((eq T u0 u) \to ((drop h (r k1 d) c0 c) \to 
(ex2 C (\lambda (e0: C).(eq C (CHead c0 k1 (lift h (r k1 d) u0)) (CHead e0 k 
(lift h (r k d) u)))) (\lambda (e0: C).(drop h (r k d) e0 c)))))) (\lambda 
(H13: (eq T u0 u)).(eq_ind T u (\lambda (t: T).((drop h (r k d) c0 c) \to 
(ex2 C (\lambda (e0: C).(eq C (CHead c0 k (lift h (r k d) t)) (CHead e0 k 
(lift h (r k d) u)))) (\lambda (e0: C).(drop h (r k d) e0 c))))) (\lambda 
(H14: (drop h (r k d) c0 c)).(let H15 \def (eq_ind T u0 (\lambda (t: T).(eq C 
(CHead c0 k0 (lift h (r k0 d) t)) x)) H7 u H13) in (let H16 \def (eq_ind K k0 
(\lambda (k1: K).(eq C (CHead c0 k1 (lift h (r k1 d) u)) x)) H15 k H12) in 
(let H17 \def (eq_ind_r C x (\lambda (c1: C).(drop h (S d) c1 (CHead c k u))) 
H (CHead c0 k (lift h (r k d) u)) H16) in (ex_intro2 C (\lambda (e0: C).(eq C 
(CHead c0 k (lift h (r k d) u)) (CHead e0 k (lift h (r k d) u)))) (\lambda 
(e0: C).(drop h (r k d) e0 c)) c0 (refl_equal C (CHead c0 k (lift h (r k d) 
u))) H14))))) u0 (sym_eq T u0 u H13))) k0 (sym_eq K k0 k H12))) e (sym_eq C e 
c H11))) H10)) H9))) x H7)) d0 (sym_eq nat d0 d H6)))) h0 (sym_eq nat h0 h 
H1) H2 H3 H4 H0)))))]) in (H0 (refl_equal nat h) (refl_equal nat (S d)) 
(refl_equal C x) (refl_equal C (CHead c k u)))))))))).

theorem drop_gen_skip_l:
 \forall (c: C).(\forall (x: C).(\forall (u: T).(\forall (h: nat).(\forall 
(d: nat).(\forall (k: K).((drop h (S d) (CHead c k u) x) \to (ex3_2 C T 
(\lambda (e: C).(\lambda (v: T).(eq C x (CHead e k v)))) (\lambda (_: 
C).(\lambda (v: T).(eq T u (lift h (r k d) v)))) (\lambda (e: C).(\lambda (_: 
T).(drop h (r k d) c e))))))))))
\def
 \lambda (c: C).(\lambda (x: C).(\lambda (u: T).(\lambda (h: nat).(\lambda 
(d: nat).(\lambda (k: K).(\lambda (H: (drop h (S d) (CHead c k u) x)).(let H0 
\def (match H in drop return (\lambda (n: nat).(\lambda (n0: nat).(\lambda 
(c0: C).(\lambda (c1: C).(\lambda (_: (drop n n0 c0 c1)).((eq nat n h) \to 
((eq nat n0 (S d)) \to ((eq C c0 (CHead c k u)) \to ((eq C c1 x) \to (ex3_2 C 
T (\lambda (e: C).(\lambda (v: T).(eq C x (CHead e k v)))) (\lambda (_: 
C).(\lambda (v: T).(eq T u (lift h (r k d) v)))) (\lambda (e: C).(\lambda (_: 
T).(drop h (r k d) c e))))))))))))) with [(drop_refl c0) \Rightarrow (\lambda 
(H0: (eq nat O h)).(\lambda (H1: (eq nat O (S d))).(\lambda (H2: (eq C c0 
(CHead c k u))).(\lambda (H3: (eq C c0 x)).(eq_ind nat O (\lambda (n: 
nat).((eq nat O (S d)) \to ((eq C c0 (CHead c k u)) \to ((eq C c0 x) \to 
(ex3_2 C T (\lambda (e: C).(\lambda (v: T).(eq C x (CHead e k v)))) (\lambda 
(_: C).(\lambda (v: T).(eq T u (lift n (r k d) v)))) (\lambda (e: C).(\lambda 
(_: T).(drop n (r k d) c e)))))))) (\lambda (H4: (eq nat O (S d))).(let H5 
\def (eq_ind nat O (\lambda (e: nat).(match e in nat return (\lambda (_: 
nat).Prop) with [O \Rightarrow True | (S _) \Rightarrow False])) I (S d) H4) 
in (False_ind ((eq C c0 (CHead c k u)) \to ((eq C c0 x) \to (ex3_2 C T 
(\lambda (e: C).(\lambda (v: T).(eq C x (CHead e k v)))) (\lambda (_: 
C).(\lambda (v: T).(eq T u (lift O (r k d) v)))) (\lambda (e: C).(\lambda (_: 
T).(drop O (r k d) c e)))))) H5))) h H0 H1 H2 H3))))) | (drop_drop k0 h0 c0 e 
H0 u0) \Rightarrow (\lambda (H1: (eq nat (S h0) h)).(\lambda (H2: (eq nat O 
(S d))).(\lambda (H3: (eq C (CHead c0 k0 u0) (CHead c k u))).(\lambda (H4: 
(eq C e x)).(eq_ind nat (S h0) (\lambda (n: nat).((eq nat O (S d)) \to ((eq C 
(CHead c0 k0 u0) (CHead c k u)) \to ((eq C e x) \to ((drop (r k0 h0) O c0 e) 
\to (ex3_2 C T (\lambda (e0: C).(\lambda (v: T).(eq C x (CHead e0 k v)))) 
(\lambda (_: C).(\lambda (v: T).(eq T u (lift n (r k d) v)))) (\lambda (e0: 
C).(\lambda (_: T).(drop n (r k d) c e0))))))))) (\lambda (H5: (eq nat O (S 
d))).(let H6 \def (eq_ind nat O (\lambda (e0: nat).(match e0 in nat return 
(\lambda (_: nat).Prop) with [O \Rightarrow True | (S _) \Rightarrow False])) 
I (S d) H5) in (False_ind ((eq C (CHead c0 k0 u0) (CHead c k u)) \to ((eq C e 
x) \to ((drop (r k0 h0) O c0 e) \to (ex3_2 C T (\lambda (e0: C).(\lambda (v: 
T).(eq C x (CHead e0 k v)))) (\lambda (_: C).(\lambda (v: T).(eq T u (lift (S 
h0) (r k d) v)))) (\lambda (e0: C).(\lambda (_: T).(drop (S h0) (r k d) c 
e0))))))) H6))) h H1 H2 H3 H4 H0))))) | (drop_skip k0 h0 d0 c0 e H0 u0) 
\Rightarrow (\lambda (H1: (eq nat h0 h)).(\lambda (H2: (eq nat (S d0) (S 
d))).(\lambda (H3: (eq C (CHead c0 k0 (lift h0 (r k0 d0) u0)) (CHead c k 
u))).(\lambda (H4: (eq C (CHead e k0 u0) x)).(eq_ind nat h (\lambda (n: 
nat).((eq nat (S d0) (S d)) \to ((eq C (CHead c0 k0 (lift n (r k0 d0) u0)) 
(CHead c k u)) \to ((eq C (CHead e k0 u0) x) \to ((drop n (r k0 d0) c0 e) \to 
(ex3_2 C T (\lambda (e0: C).(\lambda (v: T).(eq C x (CHead e0 k v)))) 
(\lambda (_: C).(\lambda (v: T).(eq T u (lift h (r k d) v)))) (\lambda (e0: 
C).(\lambda (_: T).(drop h (r k d) c e0))))))))) (\lambda (H5: (eq nat (S d0) 
(S d))).(let H6 \def (f_equal nat nat (\lambda (e0: nat).(match e0 in nat 
return (\lambda (_: nat).nat) with [O \Rightarrow d0 | (S n) \Rightarrow n])) 
(S d0) (S d) H5) in (eq_ind nat d (\lambda (n: nat).((eq C (CHead c0 k0 (lift 
h (r k0 n) u0)) (CHead c k u)) \to ((eq C (CHead e k0 u0) x) \to ((drop h (r 
k0 n) c0 e) \to (ex3_2 C T (\lambda (e0: C).(\lambda (v: T).(eq C x (CHead e0 
k v)))) (\lambda (_: C).(\lambda (v: T).(eq T u (lift h (r k d) v)))) 
(\lambda (e0: C).(\lambda (_: T).(drop h (r k d) c e0)))))))) (\lambda (H7: 
(eq C (CHead c0 k0 (lift h (r k0 d) u0)) (CHead c k u))).(let H8 \def 
(f_equal C T (\lambda (e0: C).(match e0 in C return (\lambda (_: C).T) with 
[(CSort _) \Rightarrow ((let rec lref_map (f: ((nat \to nat))) (d1: nat) (t: 
T) on t: T \def (match t with [(TSort n) \Rightarrow (TSort n) | (TLRef i) 
\Rightarrow (TLRef (match (blt i d1) with [true \Rightarrow i | false 
\Rightarrow (f i)])) | (THead k1 u1 t0) \Rightarrow (THead k1 (lref_map f d1 
u1) (lref_map f (s k1 d1) t0))]) in lref_map) (\lambda (x0: nat).(plus x0 h)) 
(r k0 d) u0) | (CHead _ _ t) \Rightarrow t])) (CHead c0 k0 (lift h (r k0 d) 
u0)) (CHead c k u) H7) in ((let H9 \def (f_equal C K (\lambda (e0: C).(match 
e0 in C return (\lambda (_: C).K) with [(CSort _) \Rightarrow k0 | (CHead _ 
k1 _) \Rightarrow k1])) (CHead c0 k0 (lift h (r k0 d) u0)) (CHead c k u) H7) 
in ((let H10 \def (f_equal C C (\lambda (e0: C).(match e0 in C return 
(\lambda (_: C).C) with [(CSort _) \Rightarrow c0 | (CHead c1 _ _) 
\Rightarrow c1])) (CHead c0 k0 (lift h (r k0 d) u0)) (CHead c k u) H7) in 
(eq_ind C c (\lambda (c1: C).((eq K k0 k) \to ((eq T (lift h (r k0 d) u0) u) 
\to ((eq C (CHead e k0 u0) x) \to ((drop h (r k0 d) c1 e) \to (ex3_2 C T 
(\lambda (e0: C).(\lambda (v: T).(eq C x (CHead e0 k v)))) (\lambda (_: 
C).(\lambda (v: T).(eq T u (lift h (r k d) v)))) (\lambda (e0: C).(\lambda 
(_: T).(drop h (r k d) c e0))))))))) (\lambda (H11: (eq K k0 k)).(eq_ind K k 
(\lambda (k1: K).((eq T (lift h (r k1 d) u0) u) \to ((eq C (CHead e k1 u0) x) 
\to ((drop h (r k1 d) c e) \to (ex3_2 C T (\lambda (e0: C).(\lambda (v: 
T).(eq C x (CHead e0 k v)))) (\lambda (_: C).(\lambda (v: T).(eq T u (lift h 
(r k d) v)))) (\lambda (e0: C).(\lambda (_: T).(drop h (r k d) c e0)))))))) 
(\lambda (H12: (eq T (lift h (r k d) u0) u)).(eq_ind T (lift h (r k d) u0) 
(\lambda (t: T).((eq C (CHead e k u0) x) \to ((drop h (r k d) c e) \to (ex3_2 
C T (\lambda (e0: C).(\lambda (v: T).(eq C x (CHead e0 k v)))) (\lambda (_: 
C).(\lambda (v: T).(eq T t (lift h (r k d) v)))) (\lambda (e0: C).(\lambda 
(_: T).(drop h (r k d) c e0))))))) (\lambda (H13: (eq C (CHead e k u0) 
x)).(eq_ind C (CHead e k u0) (\lambda (c1: C).((drop h (r k d) c e) \to 
(ex3_2 C T (\lambda (e0: C).(\lambda (v: T).(eq C c1 (CHead e0 k v)))) 
(\lambda (_: C).(\lambda (v: T).(eq T (lift h (r k d) u0) (lift h (r k d) 
v)))) (\lambda (e0: C).(\lambda (_: T).(drop h (r k d) c e0)))))) (\lambda 
(H14: (drop h (r k d) c e)).(let H15 \def (eq_ind_r T u (\lambda (t: T).(drop 
h (S d) (CHead c k t) x)) H (lift h (r k d) u0) H12) in (let H16 \def 
(eq_ind_r C x (\lambda (c1: C).(drop h (S d) (CHead c k (lift h (r k d) u0)) 
c1)) H15 (CHead e k u0) H13) in (ex3_2_intro C T (\lambda (e0: C).(\lambda 
(v: T).(eq C (CHead e k u0) (CHead e0 k v)))) (\lambda (_: C).(\lambda (v: 
T).(eq T (lift h (r k d) u0) (lift h (r k d) v)))) (\lambda (e0: C).(\lambda 
(_: T).(drop h (r k d) c e0))) e u0 (refl_equal C (CHead e k u0)) (refl_equal 
T (lift h (r k d) u0)) H14)))) x H13)) u H12)) k0 (sym_eq K k0 k H11))) c0 
(sym_eq C c0 c H10))) H9)) H8))) d0 (sym_eq nat d0 d H6)))) h0 (sym_eq nat h0 
h H1) H2 H3 H4 H0)))))]) in (H0 (refl_equal nat h) (refl_equal nat (S d)) 
(refl_equal C (CHead c k u)) (refl_equal C x))))))))).

