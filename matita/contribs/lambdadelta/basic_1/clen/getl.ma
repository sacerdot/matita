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

include "Basic-1/clen/defs.ma".

include "Basic-1/getl/props.ma".

theorem getl_ctail_clen:
 \forall (b: B).(\forall (t: T).(\forall (c: C).(ex nat (\lambda (n: 
nat).(getl (clen c) (CTail (Bind b) t c) (CHead (CSort n) (Bind b) t))))))
\def
 \lambda (b: B).(\lambda (t: T).(\lambda (c: C).(C_ind (\lambda (c0: C).(ex 
nat (\lambda (n: nat).(getl (clen c0) (CTail (Bind b) t c0) (CHead (CSort n) 
(Bind b) t))))) (\lambda (n: nat).(ex_intro nat (\lambda (n0: nat).(getl O 
(CHead (CSort n) (Bind b) t) (CHead (CSort n0) (Bind b) t))) n (getl_refl b 
(CSort n) t))) (\lambda (c0: C).(\lambda (H: (ex nat (\lambda (n: nat).(getl 
(clen c0) (CTail (Bind b) t c0) (CHead (CSort n) (Bind b) t))))).(\lambda (k: 
K).(\lambda (t0: T).(let H0 \def H in (ex_ind nat (\lambda (n: nat).(getl 
(clen c0) (CTail (Bind b) t c0) (CHead (CSort n) (Bind b) t))) (ex nat 
(\lambda (n: nat).(getl (s k (clen c0)) (CHead (CTail (Bind b) t c0) k t0) 
(CHead (CSort n) (Bind b) t)))) (\lambda (x: nat).(\lambda (H1: (getl (clen 
c0) (CTail (Bind b) t c0) (CHead (CSort x) (Bind b) t))).(K_ind (\lambda (k0: 
K).(ex nat (\lambda (n: nat).(getl (s k0 (clen c0)) (CHead (CTail (Bind b) t 
c0) k0 t0) (CHead (CSort n) (Bind b) t))))) (\lambda (b0: B).(ex_intro nat 
(\lambda (n: nat).(getl (S (clen c0)) (CHead (CTail (Bind b) t c0) (Bind b0) 
t0) (CHead (CSort n) (Bind b) t))) x (getl_head (Bind b0) (clen c0) (CTail 
(Bind b) t c0) (CHead (CSort x) (Bind b) t) H1 t0))) (\lambda (f: 
F).(ex_intro nat (\lambda (n: nat).(getl (clen c0) (CHead (CTail (Bind b) t 
c0) (Flat f) t0) (CHead (CSort n) (Bind b) t))) x (getl_flat (CTail (Bind b) 
t c0) (CHead (CSort x) (Bind b) t) (clen c0) H1 f t0))) k))) H0)))))) c))).
(* COMMENTS
Initial nodes: 459
END *)

theorem getl_gen_tail:
 \forall (k: K).(\forall (b: B).(\forall (u1: T).(\forall (u2: T).(\forall 
(c2: C).(\forall (c1: C).(\forall (i: nat).((getl i (CTail k u1 c1) (CHead c2 
(Bind b) u2)) \to (or (ex2 C (\lambda (e: C).(eq C c2 (CTail k u1 e))) 
(\lambda (e: C).(getl i c1 (CHead e (Bind b) u2)))) (ex4 nat (\lambda (_: 
nat).(eq nat i (clen c1))) (\lambda (_: nat).(eq K k (Bind b))) (\lambda (_: 
nat).(eq T u1 u2)) (\lambda (n: nat).(eq C c2 (CSort n))))))))))))
\def
 \lambda (k: K).(\lambda (b: B).(\lambda (u1: T).(\lambda (u2: T).(\lambda 
(c2: C).(\lambda (c1: C).(C_ind (\lambda (c: C).(\forall (i: nat).((getl i 
(CTail k u1 c) (CHead c2 (Bind b) u2)) \to (or (ex2 C (\lambda (e: C).(eq C 
c2 (CTail k u1 e))) (\lambda (e: C).(getl i c (CHead e (Bind b) u2)))) (ex4 
nat (\lambda (_: nat).(eq nat i (clen c))) (\lambda (_: nat).(eq K k (Bind 
b))) (\lambda (_: nat).(eq T u1 u2)) (\lambda (n: nat).(eq C c2 (CSort 
n)))))))) (\lambda (n: nat).(\lambda (i: nat).(nat_ind (\lambda (n0: 
nat).((getl n0 (CTail k u1 (CSort n)) (CHead c2 (Bind b) u2)) \to (or (ex2 C 
(\lambda (e: C).(eq C c2 (CTail k u1 e))) (\lambda (e: C).(getl n0 (CSort n) 
(CHead e (Bind b) u2)))) (ex4 nat (\lambda (_: nat).(eq nat n0 (clen (CSort 
n)))) (\lambda (_: nat).(eq K k (Bind b))) (\lambda (_: nat).(eq T u1 u2)) 
(\lambda (n1: nat).(eq C c2 (CSort n1))))))) (\lambda (H: (getl O (CHead 
(CSort n) k u1) (CHead c2 (Bind b) u2))).(K_ind (\lambda (k0: K).((clear 
(CHead (CSort n) k0 u1) (CHead c2 (Bind b) u2)) \to (or (ex2 C (\lambda (e: 
C).(eq C c2 (CTail k0 u1 e))) (\lambda (e: C).(getl O (CSort n) (CHead e 
(Bind b) u2)))) (ex4 nat (\lambda (_: nat).(eq nat O O)) (\lambda (_: 
nat).(eq K k0 (Bind b))) (\lambda (_: nat).(eq T u1 u2)) (\lambda (n0: 
nat).(eq C c2 (CSort n0))))))) (\lambda (b0: B).(\lambda (H0: (clear (CHead 
(CSort n) (Bind b0) u1) (CHead c2 (Bind b) u2))).(let H1 \def (f_equal C C 
(\lambda (e: C).(match e in C return (\lambda (_: C).C) with [(CSort _) 
\Rightarrow c2 | (CHead c _ _) \Rightarrow c])) (CHead c2 (Bind b) u2) (CHead 
(CSort n) (Bind b0) u1) (clear_gen_bind b0 (CSort n) (CHead c2 (Bind b) u2) 
u1 H0)) in ((let H2 \def (f_equal C B (\lambda (e: C).(match e in C return 
(\lambda (_: C).B) with [(CSort _) \Rightarrow b | (CHead _ k0 _) \Rightarrow 
(match k0 in K return (\lambda (_: K).B) with [(Bind b1) \Rightarrow b1 | 
(Flat _) \Rightarrow b])])) (CHead c2 (Bind b) u2) (CHead (CSort n) (Bind b0) 
u1) (clear_gen_bind b0 (CSort n) (CHead c2 (Bind b) u2) u1 H0)) in ((let H3 
\def (f_equal C T (\lambda (e: C).(match e in C return (\lambda (_: C).T) 
with [(CSort _) \Rightarrow u2 | (CHead _ _ t) \Rightarrow t])) (CHead c2 
(Bind b) u2) (CHead (CSort n) (Bind b0) u1) (clear_gen_bind b0 (CSort n) 
(CHead c2 (Bind b) u2) u1 H0)) in (\lambda (H4: (eq B b b0)).(\lambda (H5: 
(eq C c2 (CSort n))).(eq_ind_r C (CSort n) (\lambda (c: C).(or (ex2 C 
(\lambda (e: C).(eq C c (CTail (Bind b0) u1 e))) (\lambda (e: C).(getl O 
(CSort n) (CHead e (Bind b) u2)))) (ex4 nat (\lambda (_: nat).(eq nat O O)) 
(\lambda (_: nat).(eq K (Bind b0) (Bind b))) (\lambda (_: nat).(eq T u1 u2)) 
(\lambda (n0: nat).(eq C c (CSort n0)))))) (eq_ind_r T u1 (\lambda (t: T).(or 
(ex2 C (\lambda (e: C).(eq C (CSort n) (CTail (Bind b0) u1 e))) (\lambda (e: 
C).(getl O (CSort n) (CHead e (Bind b) t)))) (ex4 nat (\lambda (_: nat).(eq 
nat O O)) (\lambda (_: nat).(eq K (Bind b0) (Bind b))) (\lambda (_: nat).(eq 
T u1 t)) (\lambda (n0: nat).(eq C (CSort n) (CSort n0)))))) (eq_ind_r B b0 
(\lambda (b1: B).(or (ex2 C (\lambda (e: C).(eq C (CSort n) (CTail (Bind b0) 
u1 e))) (\lambda (e: C).(getl O (CSort n) (CHead e (Bind b1) u1)))) (ex4 nat 
(\lambda (_: nat).(eq nat O O)) (\lambda (_: nat).(eq K (Bind b0) (Bind b1))) 
(\lambda (_: nat).(eq T u1 u1)) (\lambda (n0: nat).(eq C (CSort n) (CSort 
n0)))))) (or_intror (ex2 C (\lambda (e: C).(eq C (CSort n) (CTail (Bind b0) 
u1 e))) (\lambda (e: C).(getl O (CSort n) (CHead e (Bind b0) u1)))) (ex4 nat 
(\lambda (_: nat).(eq nat O O)) (\lambda (_: nat).(eq K (Bind b0) (Bind b0))) 
(\lambda (_: nat).(eq T u1 u1)) (\lambda (n0: nat).(eq C (CSort n) (CSort 
n0)))) (ex4_intro nat (\lambda (_: nat).(eq nat O O)) (\lambda (_: nat).(eq K 
(Bind b0) (Bind b0))) (\lambda (_: nat).(eq T u1 u1)) (\lambda (n0: nat).(eq 
C (CSort n) (CSort n0))) n (refl_equal nat O) (refl_equal K (Bind b0)) 
(refl_equal T u1) (refl_equal C (CSort n)))) b H4) u2 H3) c2 H5)))) H2)) 
H1)))) (\lambda (f: F).(\lambda (H0: (clear (CHead (CSort n) (Flat f) u1) 
(CHead c2 (Bind b) u2))).(clear_gen_sort (CHead c2 (Bind b) u2) n 
(clear_gen_flat f (CSort n) (CHead c2 (Bind b) u2) u1 H0) (or (ex2 C (\lambda 
(e: C).(eq C c2 (CTail (Flat f) u1 e))) (\lambda (e: C).(getl O (CSort n) 
(CHead e (Bind b) u2)))) (ex4 nat (\lambda (_: nat).(eq nat O O)) (\lambda 
(_: nat).(eq K (Flat f) (Bind b))) (\lambda (_: nat).(eq T u1 u2)) (\lambda 
(n0: nat).(eq C c2 (CSort n0)))))))) k (getl_gen_O (CHead (CSort n) k u1) 
(CHead c2 (Bind b) u2) H))) (\lambda (n0: nat).(\lambda (_: (((getl n0 (CHead 
(CSort n) k u1) (CHead c2 (Bind b) u2)) \to (or (ex2 C (\lambda (e: C).(eq C 
c2 (CTail k u1 e))) (\lambda (e: C).(getl n0 (CSort n) (CHead e (Bind b) 
u2)))) (ex4 nat (\lambda (_: nat).(eq nat n0 O)) (\lambda (_: nat).(eq K k 
(Bind b))) (\lambda (_: nat).(eq T u1 u2)) (\lambda (n1: nat).(eq C c2 (CSort 
n1)))))))).(\lambda (H0: (getl (S n0) (CHead (CSort n) k u1) (CHead c2 (Bind 
b) u2))).(getl_gen_sort n (r k n0) (CHead c2 (Bind b) u2) (getl_gen_S k 
(CSort n) (CHead c2 (Bind b) u2) u1 n0 H0) (or (ex2 C (\lambda (e: C).(eq C 
c2 (CTail k u1 e))) (\lambda (e: C).(getl (S n0) (CSort n) (CHead e (Bind b) 
u2)))) (ex4 nat (\lambda (_: nat).(eq nat (S n0) O)) (\lambda (_: nat).(eq K 
k (Bind b))) (\lambda (_: nat).(eq T u1 u2)) (\lambda (n1: nat).(eq C c2 
(CSort n1))))))))) i))) (\lambda (c: C).(\lambda (H: ((\forall (i: 
nat).((getl i (CTail k u1 c) (CHead c2 (Bind b) u2)) \to (or (ex2 C (\lambda 
(e: C).(eq C c2 (CTail k u1 e))) (\lambda (e: C).(getl i c (CHead e (Bind b) 
u2)))) (ex4 nat (\lambda (_: nat).(eq nat i (clen c))) (\lambda (_: nat).(eq 
K k (Bind b))) (\lambda (_: nat).(eq T u1 u2)) (\lambda (n: nat).(eq C c2 
(CSort n))))))))).(\lambda (k0: K).(\lambda (t: T).(\lambda (i: nat).(nat_ind 
(\lambda (n: nat).((getl n (CTail k u1 (CHead c k0 t)) (CHead c2 (Bind b) 
u2)) \to (or (ex2 C (\lambda (e: C).(eq C c2 (CTail k u1 e))) (\lambda (e: 
C).(getl n (CHead c k0 t) (CHead e (Bind b) u2)))) (ex4 nat (\lambda (_: 
nat).(eq nat n (clen (CHead c k0 t)))) (\lambda (_: nat).(eq K k (Bind b))) 
(\lambda (_: nat).(eq T u1 u2)) (\lambda (n0: nat).(eq C c2 (CSort n0))))))) 
(\lambda (H0: (getl O (CHead (CTail k u1 c) k0 t) (CHead c2 (Bind b) 
u2))).(K_ind (\lambda (k1: K).((clear (CHead (CTail k u1 c) k1 t) (CHead c2 
(Bind b) u2)) \to (or (ex2 C (\lambda (e: C).(eq C c2 (CTail k u1 e))) 
(\lambda (e: C).(getl O (CHead c k1 t) (CHead e (Bind b) u2)))) (ex4 nat 
(\lambda (_: nat).(eq nat O (s k1 (clen c)))) (\lambda (_: nat).(eq K k (Bind 
b))) (\lambda (_: nat).(eq T u1 u2)) (\lambda (n: nat).(eq C c2 (CSort 
n))))))) (\lambda (b0: B).(\lambda (H1: (clear (CHead (CTail k u1 c) (Bind 
b0) t) (CHead c2 (Bind b) u2))).(let H2 \def (f_equal C C (\lambda (e: 
C).(match e in C return (\lambda (_: C).C) with [(CSort _) \Rightarrow c2 | 
(CHead c0 _ _) \Rightarrow c0])) (CHead c2 (Bind b) u2) (CHead (CTail k u1 c) 
(Bind b0) t) (clear_gen_bind b0 (CTail k u1 c) (CHead c2 (Bind b) u2) t H1)) 
in ((let H3 \def (f_equal C B (\lambda (e: C).(match e in C return (\lambda 
(_: C).B) with [(CSort _) \Rightarrow b | (CHead _ k1 _) \Rightarrow (match 
k1 in K return (\lambda (_: K).B) with [(Bind b1) \Rightarrow b1 | (Flat _) 
\Rightarrow b])])) (CHead c2 (Bind b) u2) (CHead (CTail k u1 c) (Bind b0) t) 
(clear_gen_bind b0 (CTail k u1 c) (CHead c2 (Bind b) u2) t H1)) in ((let H4 
\def (f_equal C T (\lambda (e: C).(match e in C return (\lambda (_: C).T) 
with [(CSort _) \Rightarrow u2 | (CHead _ _ t0) \Rightarrow t0])) (CHead c2 
(Bind b) u2) (CHead (CTail k u1 c) (Bind b0) t) (clear_gen_bind b0 (CTail k 
u1 c) (CHead c2 (Bind b) u2) t H1)) in (\lambda (H5: (eq B b b0)).(\lambda 
(H6: (eq C c2 (CTail k u1 c))).(eq_ind T u2 (\lambda (t0: T).(or (ex2 C 
(\lambda (e: C).(eq C c2 (CTail k u1 e))) (\lambda (e: C).(getl O (CHead c 
(Bind b0) t0) (CHead e (Bind b) u2)))) (ex4 nat (\lambda (_: nat).(eq nat O 
(s (Bind b0) (clen c)))) (\lambda (_: nat).(eq K k (Bind b))) (\lambda (_: 
nat).(eq T u1 u2)) (\lambda (n: nat).(eq C c2 (CSort n)))))) (eq_ind B b 
(\lambda (b1: B).(or (ex2 C (\lambda (e: C).(eq C c2 (CTail k u1 e))) 
(\lambda (e: C).(getl O (CHead c (Bind b1) u2) (CHead e (Bind b) u2)))) (ex4 
nat (\lambda (_: nat).(eq nat O (s (Bind b1) (clen c)))) (\lambda (_: 
nat).(eq K k (Bind b))) (\lambda (_: nat).(eq T u1 u2)) (\lambda (n: nat).(eq 
C c2 (CSort n)))))) (let H7 \def (eq_ind C c2 (\lambda (c0: C).(\forall (i0: 
nat).((getl i0 (CTail k u1 c) (CHead c0 (Bind b) u2)) \to (or (ex2 C (\lambda 
(e: C).(eq C c0 (CTail k u1 e))) (\lambda (e: C).(getl i0 c (CHead e (Bind b) 
u2)))) (ex4 nat (\lambda (_: nat).(eq nat i0 (clen c))) (\lambda (_: nat).(eq 
K k (Bind b))) (\lambda (_: nat).(eq T u1 u2)) (\lambda (n: nat).(eq C c0 
(CSort n)))))))) H (CTail k u1 c) H6) in (eq_ind_r C (CTail k u1 c) (\lambda 
(c0: C).(or (ex2 C (\lambda (e: C).(eq C c0 (CTail k u1 e))) (\lambda (e: 
C).(getl O (CHead c (Bind b) u2) (CHead e (Bind b) u2)))) (ex4 nat (\lambda 
(_: nat).(eq nat O (s (Bind b) (clen c)))) (\lambda (_: nat).(eq K k (Bind 
b))) (\lambda (_: nat).(eq T u1 u2)) (\lambda (n: nat).(eq C c0 (CSort 
n)))))) (or_introl (ex2 C (\lambda (e: C).(eq C (CTail k u1 c) (CTail k u1 
e))) (\lambda (e: C).(getl O (CHead c (Bind b) u2) (CHead e (Bind b) u2)))) 
(ex4 nat (\lambda (_: nat).(eq nat O (s (Bind b) (clen c)))) (\lambda (_: 
nat).(eq K k (Bind b))) (\lambda (_: nat).(eq T u1 u2)) (\lambda (n: nat).(eq 
C (CTail k u1 c) (CSort n)))) (ex_intro2 C (\lambda (e: C).(eq C (CTail k u1 
c) (CTail k u1 e))) (\lambda (e: C).(getl O (CHead c (Bind b) u2) (CHead e 
(Bind b) u2))) c (refl_equal C (CTail k u1 c)) (getl_refl b c u2))) c2 H6)) 
b0 H5) t H4)))) H3)) H2)))) (\lambda (f: F).(\lambda (H1: (clear (CHead 
(CTail k u1 c) (Flat f) t) (CHead c2 (Bind b) u2))).(let H2 \def (H O 
(getl_intro O (CTail k u1 c) (CHead c2 (Bind b) u2) (CTail k u1 c) (drop_refl 
(CTail k u1 c)) (clear_gen_flat f (CTail k u1 c) (CHead c2 (Bind b) u2) t 
H1))) in (or_ind (ex2 C (\lambda (e: C).(eq C c2 (CTail k u1 e))) (\lambda 
(e: C).(getl O c (CHead e (Bind b) u2)))) (ex4 nat (\lambda (_: nat).(eq nat 
O (clen c))) (\lambda (_: nat).(eq K k (Bind b))) (\lambda (_: nat).(eq T u1 
u2)) (\lambda (n: nat).(eq C c2 (CSort n)))) (or (ex2 C (\lambda (e: C).(eq C 
c2 (CTail k u1 e))) (\lambda (e: C).(getl O (CHead c (Flat f) t) (CHead e 
(Bind b) u2)))) (ex4 nat (\lambda (_: nat).(eq nat O (s (Flat f) (clen c)))) 
(\lambda (_: nat).(eq K k (Bind b))) (\lambda (_: nat).(eq T u1 u2)) (\lambda 
(n: nat).(eq C c2 (CSort n))))) (\lambda (H3: (ex2 C (\lambda (e: C).(eq C c2 
(CTail k u1 e))) (\lambda (e: C).(getl O c (CHead e (Bind b) u2))))).(ex2_ind 
C (\lambda (e: C).(eq C c2 (CTail k u1 e))) (\lambda (e: C).(getl O c (CHead 
e (Bind b) u2))) (or (ex2 C (\lambda (e: C).(eq C c2 (CTail k u1 e))) 
(\lambda (e: C).(getl O (CHead c (Flat f) t) (CHead e (Bind b) u2)))) (ex4 
nat (\lambda (_: nat).(eq nat O (s (Flat f) (clen c)))) (\lambda (_: nat).(eq 
K k (Bind b))) (\lambda (_: nat).(eq T u1 u2)) (\lambda (n: nat).(eq C c2 
(CSort n))))) (\lambda (x: C).(\lambda (H4: (eq C c2 (CTail k u1 
x))).(\lambda (H5: (getl O c (CHead x (Bind b) u2))).(eq_ind_r C (CTail k u1 
x) (\lambda (c0: C).(or (ex2 C (\lambda (e: C).(eq C c0 (CTail k u1 e))) 
(\lambda (e: C).(getl O (CHead c (Flat f) t) (CHead e (Bind b) u2)))) (ex4 
nat (\lambda (_: nat).(eq nat O (s (Flat f) (clen c)))) (\lambda (_: nat).(eq 
K k (Bind b))) (\lambda (_: nat).(eq T u1 u2)) (\lambda (n: nat).(eq C c0 
(CSort n)))))) (or_introl (ex2 C (\lambda (e: C).(eq C (CTail k u1 x) (CTail 
k u1 e))) (\lambda (e: C).(getl O (CHead c (Flat f) t) (CHead e (Bind b) 
u2)))) (ex4 nat (\lambda (_: nat).(eq nat O (s (Flat f) (clen c)))) (\lambda 
(_: nat).(eq K k (Bind b))) (\lambda (_: nat).(eq T u1 u2)) (\lambda (n: 
nat).(eq C (CTail k u1 x) (CSort n)))) (ex_intro2 C (\lambda (e: C).(eq C 
(CTail k u1 x) (CTail k u1 e))) (\lambda (e: C).(getl O (CHead c (Flat f) t) 
(CHead e (Bind b) u2))) x (refl_equal C (CTail k u1 x)) (getl_flat c (CHead x 
(Bind b) u2) O H5 f t))) c2 H4)))) H3)) (\lambda (H3: (ex4 nat (\lambda (_: 
nat).(eq nat O (clen c))) (\lambda (_: nat).(eq K k (Bind b))) (\lambda (_: 
nat).(eq T u1 u2)) (\lambda (n: nat).(eq C c2 (CSort n))))).(ex4_ind nat 
(\lambda (_: nat).(eq nat O (clen c))) (\lambda (_: nat).(eq K k (Bind b))) 
(\lambda (_: nat).(eq T u1 u2)) (\lambda (n: nat).(eq C c2 (CSort n))) (or 
(ex2 C (\lambda (e: C).(eq C c2 (CTail k u1 e))) (\lambda (e: C).(getl O 
(CHead c (Flat f) t) (CHead e (Bind b) u2)))) (ex4 nat (\lambda (_: nat).(eq 
nat O (s (Flat f) (clen c)))) (\lambda (_: nat).(eq K k (Bind b))) (\lambda 
(_: nat).(eq T u1 u2)) (\lambda (n: nat).(eq C c2 (CSort n))))) (\lambda (x0: 
nat).(\lambda (H4: (eq nat O (clen c))).(\lambda (H5: (eq K k (Bind 
b))).(\lambda (H6: (eq T u1 u2)).(\lambda (H7: (eq C c2 (CSort 
x0))).(eq_ind_r C (CSort x0) (\lambda (c0: C).(or (ex2 C (\lambda (e: C).(eq 
C c0 (CTail k u1 e))) (\lambda (e: C).(getl O (CHead c (Flat f) t) (CHead e 
(Bind b) u2)))) (ex4 nat (\lambda (_: nat).(eq nat O (s (Flat f) (clen c)))) 
(\lambda (_: nat).(eq K k (Bind b))) (\lambda (_: nat).(eq T u1 u2)) (\lambda 
(n: nat).(eq C c0 (CSort n)))))) (eq_ind T u1 (\lambda (t0: T).(or (ex2 C 
(\lambda (e: C).(eq C (CSort x0) (CTail k u1 e))) (\lambda (e: C).(getl O 
(CHead c (Flat f) t) (CHead e (Bind b) t0)))) (ex4 nat (\lambda (_: nat).(eq 
nat O (s (Flat f) (clen c)))) (\lambda (_: nat).(eq K k (Bind b))) (\lambda 
(_: nat).(eq T u1 t0)) (\lambda (n: nat).(eq C (CSort x0) (CSort n)))))) 
(eq_ind_r K (Bind b) (\lambda (k1: K).(or (ex2 C (\lambda (e: C).(eq C (CSort 
x0) (CTail k1 u1 e))) (\lambda (e: C).(getl O (CHead c (Flat f) t) (CHead e 
(Bind b) u1)))) (ex4 nat (\lambda (_: nat).(eq nat O (s (Flat f) (clen c)))) 
(\lambda (_: nat).(eq K k1 (Bind b))) (\lambda (_: nat).(eq T u1 u1)) 
(\lambda (n: nat).(eq C (CSort x0) (CSort n)))))) (or_intror (ex2 C (\lambda 
(e: C).(eq C (CSort x0) (CTail (Bind b) u1 e))) (\lambda (e: C).(getl O 
(CHead c (Flat f) t) (CHead e (Bind b) u1)))) (ex4 nat (\lambda (_: nat).(eq 
nat O (s (Flat f) (clen c)))) (\lambda (_: nat).(eq K (Bind b) (Bind b))) 
(\lambda (_: nat).(eq T u1 u1)) (\lambda (n: nat).(eq C (CSort x0) (CSort 
n)))) (ex4_intro nat (\lambda (_: nat).(eq nat O (s (Flat f) (clen c)))) 
(\lambda (_: nat).(eq K (Bind b) (Bind b))) (\lambda (_: nat).(eq T u1 u1)) 
(\lambda (n: nat).(eq C (CSort x0) (CSort n))) x0 H4 (refl_equal K (Bind b)) 
(refl_equal T u1) (refl_equal C (CSort x0)))) k H5) u2 H6) c2 H7)))))) H3)) 
H2)))) k0 (getl_gen_O (CHead (CTail k u1 c) k0 t) (CHead c2 (Bind b) u2) 
H0))) (\lambda (n: nat).(\lambda (H0: (((getl n (CHead (CTail k u1 c) k0 t) 
(CHead c2 (Bind b) u2)) \to (or (ex2 C (\lambda (e: C).(eq C c2 (CTail k u1 
e))) (\lambda (e: C).(getl n (CHead c k0 t) (CHead e (Bind b) u2)))) (ex4 nat 
(\lambda (_: nat).(eq nat n (s k0 (clen c)))) (\lambda (_: nat).(eq K k (Bind 
b))) (\lambda (_: nat).(eq T u1 u2)) (\lambda (n0: nat).(eq C c2 (CSort 
n0)))))))).(\lambda (H1: (getl (S n) (CHead (CTail k u1 c) k0 t) (CHead c2 
(Bind b) u2))).(let H_x \def (H (r k0 n) (getl_gen_S k0 (CTail k u1 c) (CHead 
c2 (Bind b) u2) t n H1)) in (let H2 \def H_x in (or_ind (ex2 C (\lambda (e: 
C).(eq C c2 (CTail k u1 e))) (\lambda (e: C).(getl (r k0 n) c (CHead e (Bind 
b) u2)))) (ex4 nat (\lambda (_: nat).(eq nat (r k0 n) (clen c))) (\lambda (_: 
nat).(eq K k (Bind b))) (\lambda (_: nat).(eq T u1 u2)) (\lambda (n0: 
nat).(eq C c2 (CSort n0)))) (or (ex2 C (\lambda (e: C).(eq C c2 (CTail k u1 
e))) (\lambda (e: C).(getl (S n) (CHead c k0 t) (CHead e (Bind b) u2)))) (ex4 
nat (\lambda (_: nat).(eq nat (S n) (s k0 (clen c)))) (\lambda (_: nat).(eq K 
k (Bind b))) (\lambda (_: nat).(eq T u1 u2)) (\lambda (n0: nat).(eq C c2 
(CSort n0))))) (\lambda (H3: (ex2 C (\lambda (e: C).(eq C c2 (CTail k u1 e))) 
(\lambda (e: C).(getl (r k0 n) c (CHead e (Bind b) u2))))).(ex2_ind C 
(\lambda (e: C).(eq C c2 (CTail k u1 e))) (\lambda (e: C).(getl (r k0 n) c 
(CHead e (Bind b) u2))) (or (ex2 C (\lambda (e: C).(eq C c2 (CTail k u1 e))) 
(\lambda (e: C).(getl (S n) (CHead c k0 t) (CHead e (Bind b) u2)))) (ex4 nat 
(\lambda (_: nat).(eq nat (S n) (s k0 (clen c)))) (\lambda (_: nat).(eq K k 
(Bind b))) (\lambda (_: nat).(eq T u1 u2)) (\lambda (n0: nat).(eq C c2 (CSort 
n0))))) (\lambda (x: C).(\lambda (H4: (eq C c2 (CTail k u1 x))).(\lambda (H5: 
(getl (r k0 n) c (CHead x (Bind b) u2))).(let H6 \def (eq_ind C c2 (\lambda 
(c0: C).(getl (r k0 n) (CTail k u1 c) (CHead c0 (Bind b) u2))) (getl_gen_S k0 
(CTail k u1 c) (CHead c2 (Bind b) u2) t n H1) (CTail k u1 x) H4) in (let H7 
\def (eq_ind C c2 (\lambda (c0: C).((getl n (CHead (CTail k u1 c) k0 t) 
(CHead c0 (Bind b) u2)) \to (or (ex2 C (\lambda (e: C).(eq C c0 (CTail k u1 
e))) (\lambda (e: C).(getl n (CHead c k0 t) (CHead e (Bind b) u2)))) (ex4 nat 
(\lambda (_: nat).(eq nat n (s k0 (clen c)))) (\lambda (_: nat).(eq K k (Bind 
b))) (\lambda (_: nat).(eq T u1 u2)) (\lambda (n0: nat).(eq C c0 (CSort 
n0))))))) H0 (CTail k u1 x) H4) in (eq_ind_r C (CTail k u1 x) (\lambda (c0: 
C).(or (ex2 C (\lambda (e: C).(eq C c0 (CTail k u1 e))) (\lambda (e: C).(getl 
(S n) (CHead c k0 t) (CHead e (Bind b) u2)))) (ex4 nat (\lambda (_: nat).(eq 
nat (S n) (s k0 (clen c)))) (\lambda (_: nat).(eq K k (Bind b))) (\lambda (_: 
nat).(eq T u1 u2)) (\lambda (n0: nat).(eq C c0 (CSort n0)))))) (or_introl 
(ex2 C (\lambda (e: C).(eq C (CTail k u1 x) (CTail k u1 e))) (\lambda (e: 
C).(getl (S n) (CHead c k0 t) (CHead e (Bind b) u2)))) (ex4 nat (\lambda (_: 
nat).(eq nat (S n) (s k0 (clen c)))) (\lambda (_: nat).(eq K k (Bind b))) 
(\lambda (_: nat).(eq T u1 u2)) (\lambda (n0: nat).(eq C (CTail k u1 x) 
(CSort n0)))) (ex_intro2 C (\lambda (e: C).(eq C (CTail k u1 x) (CTail k u1 
e))) (\lambda (e: C).(getl (S n) (CHead c k0 t) (CHead e (Bind b) u2))) x 
(refl_equal C (CTail k u1 x)) (getl_head k0 n c (CHead x (Bind b) u2) H5 t))) 
c2 H4)))))) H3)) (\lambda (H3: (ex4 nat (\lambda (_: nat).(eq nat (r k0 n) 
(clen c))) (\lambda (_: nat).(eq K k (Bind b))) (\lambda (_: nat).(eq T u1 
u2)) (\lambda (n0: nat).(eq C c2 (CSort n0))))).(ex4_ind nat (\lambda (_: 
nat).(eq nat (r k0 n) (clen c))) (\lambda (_: nat).(eq K k (Bind b))) 
(\lambda (_: nat).(eq T u1 u2)) (\lambda (n0: nat).(eq C c2 (CSort n0))) (or 
(ex2 C (\lambda (e: C).(eq C c2 (CTail k u1 e))) (\lambda (e: C).(getl (S n) 
(CHead c k0 t) (CHead e (Bind b) u2)))) (ex4 nat (\lambda (_: nat).(eq nat (S 
n) (s k0 (clen c)))) (\lambda (_: nat).(eq K k (Bind b))) (\lambda (_: 
nat).(eq T u1 u2)) (\lambda (n0: nat).(eq C c2 (CSort n0))))) (\lambda (x0: 
nat).(\lambda (H4: (eq nat (r k0 n) (clen c))).(\lambda (H5: (eq K k (Bind 
b))).(\lambda (H6: (eq T u1 u2)).(\lambda (H7: (eq C c2 (CSort x0))).(let H8 
\def (eq_ind C c2 (\lambda (c0: C).(getl (r k0 n) (CTail k u1 c) (CHead c0 
(Bind b) u2))) (getl_gen_S k0 (CTail k u1 c) (CHead c2 (Bind b) u2) t n H1) 
(CSort x0) H7) in (let H9 \def (eq_ind C c2 (\lambda (c0: C).((getl n (CHead 
(CTail k u1 c) k0 t) (CHead c0 (Bind b) u2)) \to (or (ex2 C (\lambda (e: 
C).(eq C c0 (CTail k u1 e))) (\lambda (e: C).(getl n (CHead c k0 t) (CHead e 
(Bind b) u2)))) (ex4 nat (\lambda (_: nat).(eq nat n (s k0 (clen c)))) 
(\lambda (_: nat).(eq K k (Bind b))) (\lambda (_: nat).(eq T u1 u2)) (\lambda 
(n0: nat).(eq C c0 (CSort n0))))))) H0 (CSort x0) H7) in (eq_ind_r C (CSort 
x0) (\lambda (c0: C).(or (ex2 C (\lambda (e: C).(eq C c0 (CTail k u1 e))) 
(\lambda (e: C).(getl (S n) (CHead c k0 t) (CHead e (Bind b) u2)))) (ex4 nat 
(\lambda (_: nat).(eq nat (S n) (s k0 (clen c)))) (\lambda (_: nat).(eq K k 
(Bind b))) (\lambda (_: nat).(eq T u1 u2)) (\lambda (n0: nat).(eq C c0 (CSort 
n0)))))) (let H10 \def (eq_ind_r T u2 (\lambda (t0: T).((getl n (CHead (CTail 
k u1 c) k0 t) (CHead (CSort x0) (Bind b) t0)) \to (or (ex2 C (\lambda (e: 
C).(eq C (CSort x0) (CTail k u1 e))) (\lambda (e: C).(getl n (CHead c k0 t) 
(CHead e (Bind b) t0)))) (ex4 nat (\lambda (_: nat).(eq nat n (s k0 (clen 
c)))) (\lambda (_: nat).(eq K k (Bind b))) (\lambda (_: nat).(eq T u1 t0)) 
(\lambda (n0: nat).(eq C (CSort x0) (CSort n0))))))) H9 u1 H6) in (let H11 
\def (eq_ind_r T u2 (\lambda (t0: T).(getl (r k0 n) (CTail k u1 c) (CHead 
(CSort x0) (Bind b) t0))) H8 u1 H6) in (eq_ind T u1 (\lambda (t0: T).(or (ex2 
C (\lambda (e: C).(eq C (CSort x0) (CTail k u1 e))) (\lambda (e: C).(getl (S 
n) (CHead c k0 t) (CHead e (Bind b) t0)))) (ex4 nat (\lambda (_: nat).(eq nat 
(S n) (s k0 (clen c)))) (\lambda (_: nat).(eq K k (Bind b))) (\lambda (_: 
nat).(eq T u1 t0)) (\lambda (n0: nat).(eq C (CSort x0) (CSort n0)))))) (let 
H12 \def (eq_ind K k (\lambda (k1: K).((getl n (CHead (CTail k1 u1 c) k0 t) 
(CHead (CSort x0) (Bind b) u1)) \to (or (ex2 C (\lambda (e: C).(eq C (CSort 
x0) (CTail k1 u1 e))) (\lambda (e: C).(getl n (CHead c k0 t) (CHead e (Bind 
b) u1)))) (ex4 nat (\lambda (_: nat).(eq nat n (s k0 (clen c)))) (\lambda (_: 
nat).(eq K k1 (Bind b))) (\lambda (_: nat).(eq T u1 u1)) (\lambda (n0: 
nat).(eq C (CSort x0) (CSort n0))))))) H10 (Bind b) H5) in (let H13 \def 
(eq_ind K k (\lambda (k1: K).(getl (r k0 n) (CTail k1 u1 c) (CHead (CSort x0) 
(Bind b) u1))) H11 (Bind b) H5) in (eq_ind_r K (Bind b) (\lambda (k1: K).(or 
(ex2 C (\lambda (e: C).(eq C (CSort x0) (CTail k1 u1 e))) (\lambda (e: 
C).(getl (S n) (CHead c k0 t) (CHead e (Bind b) u1)))) (ex4 nat (\lambda (_: 
nat).(eq nat (S n) (s k0 (clen c)))) (\lambda (_: nat).(eq K k1 (Bind b))) 
(\lambda (_: nat).(eq T u1 u1)) (\lambda (n0: nat).(eq C (CSort x0) (CSort 
n0)))))) (eq_ind nat (r k0 n) (\lambda (n0: nat).(or (ex2 C (\lambda (e: 
C).(eq C (CSort x0) (CTail (Bind b) u1 e))) (\lambda (e: C).(getl (S n) 
(CHead c k0 t) (CHead e (Bind b) u1)))) (ex4 nat (\lambda (_: nat).(eq nat (S 
n) (s k0 n0))) (\lambda (_: nat).(eq K (Bind b) (Bind b))) (\lambda (_: 
nat).(eq T u1 u1)) (\lambda (n1: nat).(eq C (CSort x0) (CSort n1)))))) 
(eq_ind_r nat (S n) (\lambda (n0: nat).(or (ex2 C (\lambda (e: C).(eq C 
(CSort x0) (CTail (Bind b) u1 e))) (\lambda (e: C).(getl (S n) (CHead c k0 t) 
(CHead e (Bind b) u1)))) (ex4 nat (\lambda (_: nat).(eq nat (S n) n0)) 
(\lambda (_: nat).(eq K (Bind b) (Bind b))) (\lambda (_: nat).(eq T u1 u1)) 
(\lambda (n1: nat).(eq C (CSort x0) (CSort n1)))))) (or_intror (ex2 C 
(\lambda (e: C).(eq C (CSort x0) (CTail (Bind b) u1 e))) (\lambda (e: 
C).(getl (S n) (CHead c k0 t) (CHead e (Bind b) u1)))) (ex4 nat (\lambda (_: 
nat).(eq nat (S n) (S n))) (\lambda (_: nat).(eq K (Bind b) (Bind b))) 
(\lambda (_: nat).(eq T u1 u1)) (\lambda (n0: nat).(eq C (CSort x0) (CSort 
n0)))) (ex4_intro nat (\lambda (_: nat).(eq nat (S n) (S n))) (\lambda (_: 
nat).(eq K (Bind b) (Bind b))) (\lambda (_: nat).(eq T u1 u1)) (\lambda (n0: 
nat).(eq C (CSort x0) (CSort n0))) x0 (refl_equal nat (S n)) (refl_equal K 
(Bind b)) (refl_equal T u1) (refl_equal C (CSort x0)))) (s k0 (r k0 n)) (s_r 
k0 n)) (clen c) H4) k H5))) u2 H6))) c2 H7)))))))) H3)) H2)))))) i)))))) 
c1)))))).
(* COMMENTS
Initial nodes: 7489
END *)

