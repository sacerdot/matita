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

set "baseuri" "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/wcpr0/getl".

include "wcpr0/defs.ma".

include "getl/props.ma".

theorem wcpr0_drop:
 \forall (c1: C).(\forall (c2: C).((wcpr0 c1 c2) \to (\forall (h: 
nat).(\forall (e1: C).(\forall (u1: T).(\forall (k: K).((drop h O c1 (CHead 
e1 k u1)) \to (ex3_2 C T (\lambda (e2: C).(\lambda (u2: T).(drop h O c2 
(CHead e2 k u2)))) (\lambda (e2: C).(\lambda (_: T).(wcpr0 e1 e2))) (\lambda 
(_: C).(\lambda (u2: T).(pr0 u1 u2)))))))))))
\def
 \lambda (c1: C).(\lambda (c2: C).(\lambda (H: (wcpr0 c1 c2)).(wcpr0_ind 
(\lambda (c: C).(\lambda (c0: C).(\forall (h: nat).(\forall (e1: C).(\forall 
(u1: T).(\forall (k: K).((drop h O c (CHead e1 k u1)) \to (ex3_2 C T (\lambda 
(e2: C).(\lambda (u2: T).(drop h O c0 (CHead e2 k u2)))) (\lambda (e2: 
C).(\lambda (_: T).(wcpr0 e1 e2))) (\lambda (_: C).(\lambda (u2: T).(pr0 u1 
u2))))))))))) (\lambda (c: C).(\lambda (h: nat).(\lambda (e1: C).(\lambda 
(u1: T).(\lambda (k: K).(\lambda (H0: (drop h O c (CHead e1 k 
u1))).(ex3_2_intro C T (\lambda (e2: C).(\lambda (u2: T).(drop h O c (CHead 
e2 k u2)))) (\lambda (e2: C).(\lambda (_: T).(wcpr0 e1 e2))) (\lambda (_: 
C).(\lambda (u2: T).(pr0 u1 u2))) e1 u1 H0 (wcpr0_refl e1) (pr0_refl 
u1)))))))) (\lambda (c0: C).(\lambda (c3: C).(\lambda (H0: (wcpr0 c0 
c3)).(\lambda (H1: ((\forall (h: nat).(\forall (e1: C).(\forall (u1: 
T).(\forall (k: K).((drop h O c0 (CHead e1 k u1)) \to (ex3_2 C T (\lambda 
(e2: C).(\lambda (u2: T).(drop h O c3 (CHead e2 k u2)))) (\lambda (e2: 
C).(\lambda (_: T).(wcpr0 e1 e2))) (\lambda (_: C).(\lambda (u2: T).(pr0 u1 
u2))))))))))).(\lambda (u1: T).(\lambda (u2: T).(\lambda (H2: (pr0 u1 
u2)).(\lambda (k: K).(\lambda (h: nat).(nat_ind (\lambda (n: nat).(\forall 
(e1: C).(\forall (u3: T).(\forall (k0: K).((drop n O (CHead c0 k u1) (CHead 
e1 k0 u3)) \to (ex3_2 C T (\lambda (e2: C).(\lambda (u4: T).(drop n O (CHead 
c3 k u2) (CHead e2 k0 u4)))) (\lambda (e2: C).(\lambda (_: T).(wcpr0 e1 e2))) 
(\lambda (_: C).(\lambda (u4: T).(pr0 u3 u4))))))))) (\lambda (e1: 
C).(\lambda (u0: T).(\lambda (k0: K).(\lambda (H3: (drop O O (CHead c0 k u1) 
(CHead e1 k0 u0))).(let H4 \def (match (drop_gen_refl (CHead c0 k u1) (CHead 
e1 k0 u0) H3) in eq return (\lambda (c: C).(\lambda (_: (eq ? ? c)).((eq C c 
(CHead e1 k0 u0)) \to (ex3_2 C T (\lambda (e2: C).(\lambda (u3: T).(drop O O 
(CHead c3 k u2) (CHead e2 k0 u3)))) (\lambda (e2: C).(\lambda (_: T).(wcpr0 
e1 e2))) (\lambda (_: C).(\lambda (u3: T).(pr0 u0 u3))))))) with [refl_equal 
\Rightarrow (\lambda (H4: (eq C (CHead c0 k u1) (CHead e1 k0 u0))).(let H5 
\def (f_equal C T (\lambda (e: C).(match e in C return (\lambda (_: C).T) 
with [(CSort _) \Rightarrow u1 | (CHead _ _ t) \Rightarrow t])) (CHead c0 k 
u1) (CHead e1 k0 u0) H4) in ((let H6 \def (f_equal C K (\lambda (e: C).(match 
e in C return (\lambda (_: C).K) with [(CSort _) \Rightarrow k | (CHead _ k1 
_) \Rightarrow k1])) (CHead c0 k u1) (CHead e1 k0 u0) H4) in ((let H7 \def 
(f_equal C C (\lambda (e: C).(match e in C return (\lambda (_: C).C) with 
[(CSort _) \Rightarrow c0 | (CHead c _ _) \Rightarrow c])) (CHead c0 k u1) 
(CHead e1 k0 u0) H4) in (eq_ind C e1 (\lambda (_: C).((eq K k k0) \to ((eq T 
u1 u0) \to (ex3_2 C T (\lambda (e2: C).(\lambda (u3: T).(drop O O (CHead c3 k 
u2) (CHead e2 k0 u3)))) (\lambda (e2: C).(\lambda (_: T).(wcpr0 e1 e2))) 
(\lambda (_: C).(\lambda (u3: T).(pr0 u0 u3))))))) (\lambda (H8: (eq K k 
k0)).(eq_ind K k0 (\lambda (k1: K).((eq T u1 u0) \to (ex3_2 C T (\lambda (e2: 
C).(\lambda (u3: T).(drop O O (CHead c3 k1 u2) (CHead e2 k0 u3)))) (\lambda 
(e2: C).(\lambda (_: T).(wcpr0 e1 e2))) (\lambda (_: C).(\lambda (u3: T).(pr0 
u0 u3)))))) (\lambda (H9: (eq T u1 u0)).(eq_ind T u0 (\lambda (_: T).(ex3_2 C 
T (\lambda (e2: C).(\lambda (u3: T).(drop O O (CHead c3 k0 u2) (CHead e2 k0 
u3)))) (\lambda (e2: C).(\lambda (_: T).(wcpr0 e1 e2))) (\lambda (_: 
C).(\lambda (u3: T).(pr0 u0 u3))))) (let H10 \def (eq_ind T u1 (\lambda (t: 
T).(pr0 t u2)) H2 u0 H9) in (let H11 \def (eq_ind C c0 (\lambda (c: C).(wcpr0 
c c3)) H0 e1 H7) in (ex3_2_intro C T (\lambda (e2: C).(\lambda (u3: T).(drop 
O O (CHead c3 k0 u2) (CHead e2 k0 u3)))) (\lambda (e2: C).(\lambda (_: 
T).(wcpr0 e1 e2))) (\lambda (_: C).(\lambda (u3: T).(pr0 u0 u3))) c3 u2 
(drop_refl (CHead c3 k0 u2)) H11 H10))) u1 (sym_eq T u1 u0 H9))) k (sym_eq K 
k k0 H8))) c0 (sym_eq C c0 e1 H7))) H6)) H5)))]) in (H4 (refl_equal C (CHead 
e1 k0 u0)))))))) (K_ind (\lambda (k0: K).(\forall (n: nat).(((\forall (e1: 
C).(\forall (u3: T).(\forall (k1: K).((drop n O (CHead c0 k0 u1) (CHead e1 k1 
u3)) \to (ex3_2 C T (\lambda (e2: C).(\lambda (u4: T).(drop n O (CHead c3 k0 
u2) (CHead e2 k1 u4)))) (\lambda (e2: C).(\lambda (_: T).(wcpr0 e1 e2))) 
(\lambda (_: C).(\lambda (u4: T).(pr0 u3 u4))))))))) \to (\forall (e1: 
C).(\forall (u3: T).(\forall (k1: K).((drop (S n) O (CHead c0 k0 u1) (CHead 
e1 k1 u3)) \to (ex3_2 C T (\lambda (e2: C).(\lambda (u4: T).(drop (S n) O 
(CHead c3 k0 u2) (CHead e2 k1 u4)))) (\lambda (e2: C).(\lambda (_: T).(wcpr0 
e1 e2))) (\lambda (_: C).(\lambda (u4: T).(pr0 u3 u4))))))))))) (\lambda (b: 
B).(\lambda (n: nat).(\lambda (_: ((\forall (e1: C).(\forall (u3: T).(\forall 
(k0: K).((drop n O (CHead c0 (Bind b) u1) (CHead e1 k0 u3)) \to (ex3_2 C T 
(\lambda (e2: C).(\lambda (u4: T).(drop n O (CHead c3 (Bind b) u2) (CHead e2 
k0 u4)))) (\lambda (e2: C).(\lambda (_: T).(wcpr0 e1 e2))) (\lambda (_: 
C).(\lambda (u4: T).(pr0 u3 u4)))))))))).(\lambda (e1: C).(\lambda (u0: 
T).(\lambda (k0: K).(\lambda (H4: (drop (S n) O (CHead c0 (Bind b) u1) (CHead 
e1 k0 u0))).(ex3_2_ind C T (\lambda (e2: C).(\lambda (u3: T).(drop n O c3 
(CHead e2 k0 u3)))) (\lambda (e2: C).(\lambda (_: T).(wcpr0 e1 e2))) (\lambda 
(_: C).(\lambda (u3: T).(pr0 u0 u3))) (ex3_2 C T (\lambda (e2: C).(\lambda 
(u3: T).(drop (S n) O (CHead c3 (Bind b) u2) (CHead e2 k0 u3)))) (\lambda 
(e2: C).(\lambda (_: T).(wcpr0 e1 e2))) (\lambda (_: C).(\lambda (u3: T).(pr0 
u0 u3)))) (\lambda (x0: C).(\lambda (x1: T).(\lambda (H5: (drop n O c3 (CHead 
x0 k0 x1))).(\lambda (H6: (wcpr0 e1 x0)).(\lambda (H7: (pr0 u0 
x1)).(ex3_2_intro C T (\lambda (e2: C).(\lambda (u3: T).(drop (S n) O (CHead 
c3 (Bind b) u2) (CHead e2 k0 u3)))) (\lambda (e2: C).(\lambda (_: T).(wcpr0 
e1 e2))) (\lambda (_: C).(\lambda (u3: T).(pr0 u0 u3))) x0 x1 (drop_drop 
(Bind b) n c3 (CHead x0 k0 x1) H5 u2) H6 H7)))))) (H1 n e1 u0 k0 
(drop_gen_drop (Bind b) c0 (CHead e1 k0 u0) u1 n H4)))))))))) (\lambda (f: 
F).(\lambda (n: nat).(\lambda (_: ((\forall (e1: C).(\forall (u3: T).(\forall 
(k0: K).((drop n O (CHead c0 (Flat f) u1) (CHead e1 k0 u3)) \to (ex3_2 C T 
(\lambda (e2: C).(\lambda (u4: T).(drop n O (CHead c3 (Flat f) u2) (CHead e2 
k0 u4)))) (\lambda (e2: C).(\lambda (_: T).(wcpr0 e1 e2))) (\lambda (_: 
C).(\lambda (u4: T).(pr0 u3 u4)))))))))).(\lambda (e1: C).(\lambda (u0: 
T).(\lambda (k0: K).(\lambda (H4: (drop (S n) O (CHead c0 (Flat f) u1) (CHead 
e1 k0 u0))).(ex3_2_ind C T (\lambda (e2: C).(\lambda (u3: T).(drop (S n) O c3 
(CHead e2 k0 u3)))) (\lambda (e2: C).(\lambda (_: T).(wcpr0 e1 e2))) (\lambda 
(_: C).(\lambda (u3: T).(pr0 u0 u3))) (ex3_2 C T (\lambda (e2: C).(\lambda 
(u3: T).(drop (S n) O (CHead c3 (Flat f) u2) (CHead e2 k0 u3)))) (\lambda 
(e2: C).(\lambda (_: T).(wcpr0 e1 e2))) (\lambda (_: C).(\lambda (u3: T).(pr0 
u0 u3)))) (\lambda (x0: C).(\lambda (x1: T).(\lambda (H5: (drop (S n) O c3 
(CHead x0 k0 x1))).(\lambda (H6: (wcpr0 e1 x0)).(\lambda (H7: (pr0 u0 
x1)).(ex3_2_intro C T (\lambda (e2: C).(\lambda (u3: T).(drop (S n) O (CHead 
c3 (Flat f) u2) (CHead e2 k0 u3)))) (\lambda (e2: C).(\lambda (_: T).(wcpr0 
e1 e2))) (\lambda (_: C).(\lambda (u3: T).(pr0 u0 u3))) x0 x1 (drop_drop 
(Flat f) n c3 (CHead x0 k0 x1) H5 u2) H6 H7)))))) (H1 (S n) e1 u0 k0 
(drop_gen_drop (Flat f) c0 (CHead e1 k0 u0) u1 n H4)))))))))) k) h)))))))))) 
c1 c2 H))).

theorem wcpr0_drop_back:
 \forall (c1: C).(\forall (c2: C).((wcpr0 c2 c1) \to (\forall (h: 
nat).(\forall (e1: C).(\forall (u1: T).(\forall (k: K).((drop h O c1 (CHead 
e1 k u1)) \to (ex3_2 C T (\lambda (e2: C).(\lambda (u2: T).(drop h O c2 
(CHead e2 k u2)))) (\lambda (e2: C).(\lambda (_: T).(wcpr0 e2 e1))) (\lambda 
(_: C).(\lambda (u2: T).(pr0 u2 u1)))))))))))
\def
 \lambda (c1: C).(\lambda (c2: C).(\lambda (H: (wcpr0 c2 c1)).(wcpr0_ind 
(\lambda (c: C).(\lambda (c0: C).(\forall (h: nat).(\forall (e1: C).(\forall 
(u1: T).(\forall (k: K).((drop h O c0 (CHead e1 k u1)) \to (ex3_2 C T 
(\lambda (e2: C).(\lambda (u2: T).(drop h O c (CHead e2 k u2)))) (\lambda 
(e2: C).(\lambda (_: T).(wcpr0 e2 e1))) (\lambda (_: C).(\lambda (u2: T).(pr0 
u2 u1))))))))))) (\lambda (c: C).(\lambda (h: nat).(\lambda (e1: C).(\lambda 
(u1: T).(\lambda (k: K).(\lambda (H0: (drop h O c (CHead e1 k 
u1))).(ex3_2_intro C T (\lambda (e2: C).(\lambda (u2: T).(drop h O c (CHead 
e2 k u2)))) (\lambda (e2: C).(\lambda (_: T).(wcpr0 e2 e1))) (\lambda (_: 
C).(\lambda (u2: T).(pr0 u2 u1))) e1 u1 H0 (wcpr0_refl e1) (pr0_refl 
u1)))))))) (\lambda (c0: C).(\lambda (c3: C).(\lambda (H0: (wcpr0 c0 
c3)).(\lambda (H1: ((\forall (h: nat).(\forall (e1: C).(\forall (u1: 
T).(\forall (k: K).((drop h O c3 (CHead e1 k u1)) \to (ex3_2 C T (\lambda 
(e2: C).(\lambda (u2: T).(drop h O c0 (CHead e2 k u2)))) (\lambda (e2: 
C).(\lambda (_: T).(wcpr0 e2 e1))) (\lambda (_: C).(\lambda (u2: T).(pr0 u2 
u1))))))))))).(\lambda (u1: T).(\lambda (u2: T).(\lambda (H2: (pr0 u1 
u2)).(\lambda (k: K).(\lambda (h: nat).(nat_ind (\lambda (n: nat).(\forall 
(e1: C).(\forall (u3: T).(\forall (k0: K).((drop n O (CHead c3 k u2) (CHead 
e1 k0 u3)) \to (ex3_2 C T (\lambda (e2: C).(\lambda (u4: T).(drop n O (CHead 
c0 k u1) (CHead e2 k0 u4)))) (\lambda (e2: C).(\lambda (_: T).(wcpr0 e2 e1))) 
(\lambda (_: C).(\lambda (u4: T).(pr0 u4 u3))))))))) (\lambda (e1: 
C).(\lambda (u0: T).(\lambda (k0: K).(\lambda (H3: (drop O O (CHead c3 k u2) 
(CHead e1 k0 u0))).(let H4 \def (match (drop_gen_refl (CHead c3 k u2) (CHead 
e1 k0 u0) H3) in eq return (\lambda (c: C).(\lambda (_: (eq ? ? c)).((eq C c 
(CHead e1 k0 u0)) \to (ex3_2 C T (\lambda (e2: C).(\lambda (u3: T).(drop O O 
(CHead c0 k u1) (CHead e2 k0 u3)))) (\lambda (e2: C).(\lambda (_: T).(wcpr0 
e2 e1))) (\lambda (_: C).(\lambda (u3: T).(pr0 u3 u0))))))) with [refl_equal 
\Rightarrow (\lambda (H4: (eq C (CHead c3 k u2) (CHead e1 k0 u0))).(let H5 
\def (f_equal C T (\lambda (e: C).(match e in C return (\lambda (_: C).T) 
with [(CSort _) \Rightarrow u2 | (CHead _ _ t) \Rightarrow t])) (CHead c3 k 
u2) (CHead e1 k0 u0) H4) in ((let H6 \def (f_equal C K (\lambda (e: C).(match 
e in C return (\lambda (_: C).K) with [(CSort _) \Rightarrow k | (CHead _ k1 
_) \Rightarrow k1])) (CHead c3 k u2) (CHead e1 k0 u0) H4) in ((let H7 \def 
(f_equal C C (\lambda (e: C).(match e in C return (\lambda (_: C).C) with 
[(CSort _) \Rightarrow c3 | (CHead c _ _) \Rightarrow c])) (CHead c3 k u2) 
(CHead e1 k0 u0) H4) in (eq_ind C e1 (\lambda (_: C).((eq K k k0) \to ((eq T 
u2 u0) \to (ex3_2 C T (\lambda (e2: C).(\lambda (u3: T).(drop O O (CHead c0 k 
u1) (CHead e2 k0 u3)))) (\lambda (e2: C).(\lambda (_: T).(wcpr0 e2 e1))) 
(\lambda (_: C).(\lambda (u3: T).(pr0 u3 u0))))))) (\lambda (H8: (eq K k 
k0)).(eq_ind K k0 (\lambda (k1: K).((eq T u2 u0) \to (ex3_2 C T (\lambda (e2: 
C).(\lambda (u3: T).(drop O O (CHead c0 k1 u1) (CHead e2 k0 u3)))) (\lambda 
(e2: C).(\lambda (_: T).(wcpr0 e2 e1))) (\lambda (_: C).(\lambda (u3: T).(pr0 
u3 u0)))))) (\lambda (H9: (eq T u2 u0)).(eq_ind T u0 (\lambda (_: T).(ex3_2 C 
T (\lambda (e2: C).(\lambda (u3: T).(drop O O (CHead c0 k0 u1) (CHead e2 k0 
u3)))) (\lambda (e2: C).(\lambda (_: T).(wcpr0 e2 e1))) (\lambda (_: 
C).(\lambda (u3: T).(pr0 u3 u0))))) (let H10 \def (eq_ind T u2 (\lambda (t: 
T).(pr0 u1 t)) H2 u0 H9) in (let H11 \def (eq_ind C c3 (\lambda (c: C).(wcpr0 
c0 c)) H0 e1 H7) in (ex3_2_intro C T (\lambda (e2: C).(\lambda (u3: T).(drop 
O O (CHead c0 k0 u1) (CHead e2 k0 u3)))) (\lambda (e2: C).(\lambda (_: 
T).(wcpr0 e2 e1))) (\lambda (_: C).(\lambda (u3: T).(pr0 u3 u0))) c0 u1 
(drop_refl (CHead c0 k0 u1)) H11 H10))) u2 (sym_eq T u2 u0 H9))) k (sym_eq K 
k k0 H8))) c3 (sym_eq C c3 e1 H7))) H6)) H5)))]) in (H4 (refl_equal C (CHead 
e1 k0 u0)))))))) (K_ind (\lambda (k0: K).(\forall (n: nat).(((\forall (e1: 
C).(\forall (u3: T).(\forall (k1: K).((drop n O (CHead c3 k0 u2) (CHead e1 k1 
u3)) \to (ex3_2 C T (\lambda (e2: C).(\lambda (u4: T).(drop n O (CHead c0 k0 
u1) (CHead e2 k1 u4)))) (\lambda (e2: C).(\lambda (_: T).(wcpr0 e2 e1))) 
(\lambda (_: C).(\lambda (u4: T).(pr0 u4 u3))))))))) \to (\forall (e1: 
C).(\forall (u3: T).(\forall (k1: K).((drop (S n) O (CHead c3 k0 u2) (CHead 
e1 k1 u3)) \to (ex3_2 C T (\lambda (e2: C).(\lambda (u4: T).(drop (S n) O 
(CHead c0 k0 u1) (CHead e2 k1 u4)))) (\lambda (e2: C).(\lambda (_: T).(wcpr0 
e2 e1))) (\lambda (_: C).(\lambda (u4: T).(pr0 u4 u3))))))))))) (\lambda (b: 
B).(\lambda (n: nat).(\lambda (_: ((\forall (e1: C).(\forall (u3: T).(\forall 
(k0: K).((drop n O (CHead c3 (Bind b) u2) (CHead e1 k0 u3)) \to (ex3_2 C T 
(\lambda (e2: C).(\lambda (u4: T).(drop n O (CHead c0 (Bind b) u1) (CHead e2 
k0 u4)))) (\lambda (e2: C).(\lambda (_: T).(wcpr0 e2 e1))) (\lambda (_: 
C).(\lambda (u4: T).(pr0 u4 u3)))))))))).(\lambda (e1: C).(\lambda (u0: 
T).(\lambda (k0: K).(\lambda (H4: (drop (S n) O (CHead c3 (Bind b) u2) (CHead 
e1 k0 u0))).(ex3_2_ind C T (\lambda (e2: C).(\lambda (u3: T).(drop n O c0 
(CHead e2 k0 u3)))) (\lambda (e2: C).(\lambda (_: T).(wcpr0 e2 e1))) (\lambda 
(_: C).(\lambda (u3: T).(pr0 u3 u0))) (ex3_2 C T (\lambda (e2: C).(\lambda 
(u3: T).(drop (S n) O (CHead c0 (Bind b) u1) (CHead e2 k0 u3)))) (\lambda 
(e2: C).(\lambda (_: T).(wcpr0 e2 e1))) (\lambda (_: C).(\lambda (u3: T).(pr0 
u3 u0)))) (\lambda (x0: C).(\lambda (x1: T).(\lambda (H5: (drop n O c0 (CHead 
x0 k0 x1))).(\lambda (H6: (wcpr0 x0 e1)).(\lambda (H7: (pr0 x1 
u0)).(ex3_2_intro C T (\lambda (e2: C).(\lambda (u3: T).(drop (S n) O (CHead 
c0 (Bind b) u1) (CHead e2 k0 u3)))) (\lambda (e2: C).(\lambda (_: T).(wcpr0 
e2 e1))) (\lambda (_: C).(\lambda (u3: T).(pr0 u3 u0))) x0 x1 (drop_drop 
(Bind b) n c0 (CHead x0 k0 x1) H5 u1) H6 H7)))))) (H1 n e1 u0 k0 
(drop_gen_drop (Bind b) c3 (CHead e1 k0 u0) u2 n H4)))))))))) (\lambda (f: 
F).(\lambda (n: nat).(\lambda (_: ((\forall (e1: C).(\forall (u3: T).(\forall 
(k0: K).((drop n O (CHead c3 (Flat f) u2) (CHead e1 k0 u3)) \to (ex3_2 C T 
(\lambda (e2: C).(\lambda (u4: T).(drop n O (CHead c0 (Flat f) u1) (CHead e2 
k0 u4)))) (\lambda (e2: C).(\lambda (_: T).(wcpr0 e2 e1))) (\lambda (_: 
C).(\lambda (u4: T).(pr0 u4 u3)))))))))).(\lambda (e1: C).(\lambda (u0: 
T).(\lambda (k0: K).(\lambda (H4: (drop (S n) O (CHead c3 (Flat f) u2) (CHead 
e1 k0 u0))).(ex3_2_ind C T (\lambda (e2: C).(\lambda (u3: T).(drop (S n) O c0 
(CHead e2 k0 u3)))) (\lambda (e2: C).(\lambda (_: T).(wcpr0 e2 e1))) (\lambda 
(_: C).(\lambda (u3: T).(pr0 u3 u0))) (ex3_2 C T (\lambda (e2: C).(\lambda 
(u3: T).(drop (S n) O (CHead c0 (Flat f) u1) (CHead e2 k0 u3)))) (\lambda 
(e2: C).(\lambda (_: T).(wcpr0 e2 e1))) (\lambda (_: C).(\lambda (u3: T).(pr0 
u3 u0)))) (\lambda (x0: C).(\lambda (x1: T).(\lambda (H5: (drop (S n) O c0 
(CHead x0 k0 x1))).(\lambda (H6: (wcpr0 x0 e1)).(\lambda (H7: (pr0 x1 
u0)).(ex3_2_intro C T (\lambda (e2: C).(\lambda (u3: T).(drop (S n) O (CHead 
c0 (Flat f) u1) (CHead e2 k0 u3)))) (\lambda (e2: C).(\lambda (_: T).(wcpr0 
e2 e1))) (\lambda (_: C).(\lambda (u3: T).(pr0 u3 u0))) x0 x1 (drop_drop 
(Flat f) n c0 (CHead x0 k0 x1) H5 u1) H6 H7)))))) (H1 (S n) e1 u0 k0 
(drop_gen_drop (Flat f) c3 (CHead e1 k0 u0) u2 n H4)))))))))) k) h)))))))))) 
c2 c1 H))).

theorem wcpr0_getl:
 \forall (c1: C).(\forall (c2: C).((wcpr0 c1 c2) \to (\forall (h: 
nat).(\forall (e1: C).(\forall (u1: T).(\forall (k: K).((getl h c1 (CHead e1 
k u1)) \to (ex3_2 C T (\lambda (e2: C).(\lambda (u2: T).(getl h c2 (CHead e2 
k u2)))) (\lambda (e2: C).(\lambda (_: T).(wcpr0 e1 e2))) (\lambda (_: 
C).(\lambda (u2: T).(pr0 u1 u2)))))))))))
\def
 \lambda (c1: C).(\lambda (c2: C).(\lambda (H: (wcpr0 c1 c2)).(wcpr0_ind 
(\lambda (c: C).(\lambda (c0: C).(\forall (h: nat).(\forall (e1: C).(\forall 
(u1: T).(\forall (k: K).((getl h c (CHead e1 k u1)) \to (ex3_2 C T (\lambda 
(e2: C).(\lambda (u2: T).(getl h c0 (CHead e2 k u2)))) (\lambda (e2: 
C).(\lambda (_: T).(wcpr0 e1 e2))) (\lambda (_: C).(\lambda (u2: T).(pr0 u1 
u2))))))))))) (\lambda (c: C).(\lambda (h: nat).(\lambda (e1: C).(\lambda 
(u1: T).(\lambda (k: K).(\lambda (H0: (getl h c (CHead e1 k 
u1))).(ex3_2_intro C T (\lambda (e2: C).(\lambda (u2: T).(getl h c (CHead e2 
k u2)))) (\lambda (e2: C).(\lambda (_: T).(wcpr0 e1 e2))) (\lambda (_: 
C).(\lambda (u2: T).(pr0 u1 u2))) e1 u1 H0 (wcpr0_refl e1) (pr0_refl 
u1)))))))) (\lambda (c0: C).(\lambda (c3: C).(\lambda (H0: (wcpr0 c0 
c3)).(\lambda (H1: ((\forall (h: nat).(\forall (e1: C).(\forall (u1: 
T).(\forall (k: K).((getl h c0 (CHead e1 k u1)) \to (ex3_2 C T (\lambda (e2: 
C).(\lambda (u2: T).(getl h c3 (CHead e2 k u2)))) (\lambda (e2: C).(\lambda 
(_: T).(wcpr0 e1 e2))) (\lambda (_: C).(\lambda (u2: T).(pr0 u1 
u2))))))))))).(\lambda (u1: T).(\lambda (u2: T).(\lambda (H2: (pr0 u1 
u2)).(\lambda (k: K).(\lambda (h: nat).(nat_ind (\lambda (n: nat).(\forall 
(e1: C).(\forall (u3: T).(\forall (k0: K).((getl n (CHead c0 k u1) (CHead e1 
k0 u3)) \to (ex3_2 C T (\lambda (e2: C).(\lambda (u4: T).(getl n (CHead c3 k 
u2) (CHead e2 k0 u4)))) (\lambda (e2: C).(\lambda (_: T).(wcpr0 e1 e2))) 
(\lambda (_: C).(\lambda (u4: T).(pr0 u3 u4))))))))) (\lambda (e1: 
C).(\lambda (u0: T).(\lambda (k0: K).(\lambda (H3: (getl O (CHead c0 k u1) 
(CHead e1 k0 u0))).(K_ind (\lambda (k1: K).((clear (CHead c0 k1 u1) (CHead e1 
k0 u0)) \to (ex3_2 C T (\lambda (e2: C).(\lambda (u3: T).(getl O (CHead c3 k1 
u2) (CHead e2 k0 u3)))) (\lambda (e2: C).(\lambda (_: T).(wcpr0 e1 e2))) 
(\lambda (_: C).(\lambda (u3: T).(pr0 u0 u3)))))) (\lambda (b: B).(\lambda 
(H4: (clear (CHead c0 (Bind b) u1) (CHead e1 k0 u0))).(let H5 \def (f_equal C 
C (\lambda (e: C).(match e in C return (\lambda (_: C).C) with [(CSort _) 
\Rightarrow e1 | (CHead c _ _) \Rightarrow c])) (CHead e1 k0 u0) (CHead c0 
(Bind b) u1) (clear_gen_bind b c0 (CHead e1 k0 u0) u1 H4)) in ((let H6 \def 
(f_equal C K (\lambda (e: C).(match e in C return (\lambda (_: C).K) with 
[(CSort _) \Rightarrow k0 | (CHead _ k1 _) \Rightarrow k1])) (CHead e1 k0 u0) 
(CHead c0 (Bind b) u1) (clear_gen_bind b c0 (CHead e1 k0 u0) u1 H4)) in ((let 
H7 \def (f_equal C T (\lambda (e: C).(match e in C return (\lambda (_: C).T) 
with [(CSort _) \Rightarrow u0 | (CHead _ _ t) \Rightarrow t])) (CHead e1 k0 
u0) (CHead c0 (Bind b) u1) (clear_gen_bind b c0 (CHead e1 k0 u0) u1 H4)) in 
(\lambda (H8: (eq K k0 (Bind b))).(\lambda (H9: (eq C e1 c0)).(eq_ind_r K 
(Bind b) (\lambda (k1: K).(ex3_2 C T (\lambda (e2: C).(\lambda (u3: T).(getl 
O (CHead c3 (Bind b) u2) (CHead e2 k1 u3)))) (\lambda (e2: C).(\lambda (_: 
T).(wcpr0 e1 e2))) (\lambda (_: C).(\lambda (u3: T).(pr0 u0 u3))))) (eq_ind_r 
T u1 (\lambda (t: T).(ex3_2 C T (\lambda (e2: C).(\lambda (u3: T).(getl O 
(CHead c3 (Bind b) u2) (CHead e2 (Bind b) u3)))) (\lambda (e2: C).(\lambda 
(_: T).(wcpr0 e1 e2))) (\lambda (_: C).(\lambda (u3: T).(pr0 t u3))))) 
(eq_ind_r C c0 (\lambda (c: C).(ex3_2 C T (\lambda (e2: C).(\lambda (u3: 
T).(getl O (CHead c3 (Bind b) u2) (CHead e2 (Bind b) u3)))) (\lambda (e2: 
C).(\lambda (_: T).(wcpr0 c e2))) (\lambda (_: C).(\lambda (u3: T).(pr0 u1 
u3))))) (ex3_2_intro C T (\lambda (e2: C).(\lambda (u3: T).(getl O (CHead c3 
(Bind b) u2) (CHead e2 (Bind b) u3)))) (\lambda (e2: C).(\lambda (_: 
T).(wcpr0 c0 e2))) (\lambda (_: C).(\lambda (u3: T).(pr0 u1 u3))) c3 u2 
(getl_refl b c3 u2) H0 H2) e1 H9) u0 H7) k0 H8)))) H6)) H5)))) (\lambda (f: 
F).(\lambda (H4: (clear (CHead c0 (Flat f) u1) (CHead e1 k0 u0))).(let H5 
\def (H1 O e1 u0 k0 (getl_intro O c0 (CHead e1 k0 u0) c0 (drop_refl c0) 
(clear_gen_flat f c0 (CHead e1 k0 u0) u1 H4))) in (ex3_2_ind C T (\lambda 
(e2: C).(\lambda (u3: T).(getl O c3 (CHead e2 k0 u3)))) (\lambda (e2: 
C).(\lambda (_: T).(wcpr0 e1 e2))) (\lambda (_: C).(\lambda (u3: T).(pr0 u0 
u3))) (ex3_2 C T (\lambda (e2: C).(\lambda (u3: T).(getl O (CHead c3 (Flat f) 
u2) (CHead e2 k0 u3)))) (\lambda (e2: C).(\lambda (_: T).(wcpr0 e1 e2))) 
(\lambda (_: C).(\lambda (u3: T).(pr0 u0 u3)))) (\lambda (x0: C).(\lambda 
(x1: T).(\lambda (H6: (getl O c3 (CHead x0 k0 x1))).(\lambda (H7: (wcpr0 e1 
x0)).(\lambda (H8: (pr0 u0 x1)).(ex3_2_intro C T (\lambda (e2: C).(\lambda 
(u3: T).(getl O (CHead c3 (Flat f) u2) (CHead e2 k0 u3)))) (\lambda (e2: 
C).(\lambda (_: T).(wcpr0 e1 e2))) (\lambda (_: C).(\lambda (u3: T).(pr0 u0 
u3))) x0 x1 (getl_flat c3 (CHead x0 k0 x1) O H6 f u2) H7 H8)))))) H5)))) k 
(getl_gen_O (CHead c0 k u1) (CHead e1 k0 u0) H3)))))) (K_ind (\lambda (k0: 
K).(\forall (n: nat).(((\forall (e1: C).(\forall (u3: T).(\forall (k1: 
K).((getl n (CHead c0 k0 u1) (CHead e1 k1 u3)) \to (ex3_2 C T (\lambda (e2: 
C).(\lambda (u4: T).(getl n (CHead c3 k0 u2) (CHead e2 k1 u4)))) (\lambda 
(e2: C).(\lambda (_: T).(wcpr0 e1 e2))) (\lambda (_: C).(\lambda (u4: T).(pr0 
u3 u4))))))))) \to (\forall (e1: C).(\forall (u3: T).(\forall (k1: K).((getl 
(S n) (CHead c0 k0 u1) (CHead e1 k1 u3)) \to (ex3_2 C T (\lambda (e2: 
C).(\lambda (u4: T).(getl (S n) (CHead c3 k0 u2) (CHead e2 k1 u4)))) (\lambda 
(e2: C).(\lambda (_: T).(wcpr0 e1 e2))) (\lambda (_: C).(\lambda (u4: T).(pr0 
u3 u4))))))))))) (\lambda (b: B).(\lambda (n: nat).(\lambda (_: ((\forall 
(e1: C).(\forall (u3: T).(\forall (k0: K).((getl n (CHead c0 (Bind b) u1) 
(CHead e1 k0 u3)) \to (ex3_2 C T (\lambda (e2: C).(\lambda (u4: T).(getl n 
(CHead c3 (Bind b) u2) (CHead e2 k0 u4)))) (\lambda (e2: C).(\lambda (_: 
T).(wcpr0 e1 e2))) (\lambda (_: C).(\lambda (u4: T).(pr0 u3 
u4)))))))))).(\lambda (e1: C).(\lambda (u0: T).(\lambda (k0: K).(\lambda (H4: 
(getl (S n) (CHead c0 (Bind b) u1) (CHead e1 k0 u0))).(let H5 \def (H1 n e1 
u0 k0 (getl_gen_S (Bind b) c0 (CHead e1 k0 u0) u1 n H4)) in (ex3_2_ind C T 
(\lambda (e2: C).(\lambda (u3: T).(getl n c3 (CHead e2 k0 u3)))) (\lambda 
(e2: C).(\lambda (_: T).(wcpr0 e1 e2))) (\lambda (_: C).(\lambda (u3: T).(pr0 
u0 u3))) (ex3_2 C T (\lambda (e2: C).(\lambda (u3: T).(getl (S n) (CHead c3 
(Bind b) u2) (CHead e2 k0 u3)))) (\lambda (e2: C).(\lambda (_: T).(wcpr0 e1 
e2))) (\lambda (_: C).(\lambda (u3: T).(pr0 u0 u3)))) (\lambda (x0: 
C).(\lambda (x1: T).(\lambda (H6: (getl n c3 (CHead x0 k0 x1))).(\lambda (H7: 
(wcpr0 e1 x0)).(\lambda (H8: (pr0 u0 x1)).(ex3_2_intro C T (\lambda (e2: 
C).(\lambda (u3: T).(getl (S n) (CHead c3 (Bind b) u2) (CHead e2 k0 u3)))) 
(\lambda (e2: C).(\lambda (_: T).(wcpr0 e1 e2))) (\lambda (_: C).(\lambda 
(u3: T).(pr0 u0 u3))) x0 x1 (getl_head (Bind b) n c3 (CHead x0 k0 x1) H6 u2) 
H7 H8)))))) H5))))))))) (\lambda (f: F).(\lambda (n: nat).(\lambda (_: 
((\forall (e1: C).(\forall (u3: T).(\forall (k0: K).((getl n (CHead c0 (Flat 
f) u1) (CHead e1 k0 u3)) \to (ex3_2 C T (\lambda (e2: C).(\lambda (u4: 
T).(getl n (CHead c3 (Flat f) u2) (CHead e2 k0 u4)))) (\lambda (e2: 
C).(\lambda (_: T).(wcpr0 e1 e2))) (\lambda (_: C).(\lambda (u4: T).(pr0 u3 
u4)))))))))).(\lambda (e1: C).(\lambda (u0: T).(\lambda (k0: K).(\lambda (H4: 
(getl (S n) (CHead c0 (Flat f) u1) (CHead e1 k0 u0))).(let H5 \def (H1 (S n) 
e1 u0 k0 (getl_gen_S (Flat f) c0 (CHead e1 k0 u0) u1 n H4)) in (ex3_2_ind C T 
(\lambda (e2: C).(\lambda (u3: T).(getl (S n) c3 (CHead e2 k0 u3)))) (\lambda 
(e2: C).(\lambda (_: T).(wcpr0 e1 e2))) (\lambda (_: C).(\lambda (u3: T).(pr0 
u0 u3))) (ex3_2 C T (\lambda (e2: C).(\lambda (u3: T).(getl (S n) (CHead c3 
(Flat f) u2) (CHead e2 k0 u3)))) (\lambda (e2: C).(\lambda (_: T).(wcpr0 e1 
e2))) (\lambda (_: C).(\lambda (u3: T).(pr0 u0 u3)))) (\lambda (x0: 
C).(\lambda (x1: T).(\lambda (H6: (getl (S n) c3 (CHead x0 k0 x1))).(\lambda 
(H7: (wcpr0 e1 x0)).(\lambda (H8: (pr0 u0 x1)).(ex3_2_intro C T (\lambda (e2: 
C).(\lambda (u3: T).(getl (S n) (CHead c3 (Flat f) u2) (CHead e2 k0 u3)))) 
(\lambda (e2: C).(\lambda (_: T).(wcpr0 e1 e2))) (\lambda (_: C).(\lambda 
(u3: T).(pr0 u0 u3))) x0 x1 (getl_head (Flat f) n c3 (CHead x0 k0 x1) H6 u2) 
H7 H8)))))) H5))))))))) k) h)))))))))) c1 c2 H))).

theorem wcpr0_getl_back:
 \forall (c1: C).(\forall (c2: C).((wcpr0 c2 c1) \to (\forall (h: 
nat).(\forall (e1: C).(\forall (u1: T).(\forall (k: K).((getl h c1 (CHead e1 
k u1)) \to (ex3_2 C T (\lambda (e2: C).(\lambda (u2: T).(getl h c2 (CHead e2 
k u2)))) (\lambda (e2: C).(\lambda (_: T).(wcpr0 e2 e1))) (\lambda (_: 
C).(\lambda (u2: T).(pr0 u2 u1)))))))))))
\def
 \lambda (c1: C).(\lambda (c2: C).(\lambda (H: (wcpr0 c2 c1)).(wcpr0_ind 
(\lambda (c: C).(\lambda (c0: C).(\forall (h: nat).(\forall (e1: C).(\forall 
(u1: T).(\forall (k: K).((getl h c0 (CHead e1 k u1)) \to (ex3_2 C T (\lambda 
(e2: C).(\lambda (u2: T).(getl h c (CHead e2 k u2)))) (\lambda (e2: 
C).(\lambda (_: T).(wcpr0 e2 e1))) (\lambda (_: C).(\lambda (u2: T).(pr0 u2 
u1))))))))))) (\lambda (c: C).(\lambda (h: nat).(\lambda (e1: C).(\lambda 
(u1: T).(\lambda (k: K).(\lambda (H0: (getl h c (CHead e1 k 
u1))).(ex3_2_intro C T (\lambda (e2: C).(\lambda (u2: T).(getl h c (CHead e2 
k u2)))) (\lambda (e2: C).(\lambda (_: T).(wcpr0 e2 e1))) (\lambda (_: 
C).(\lambda (u2: T).(pr0 u2 u1))) e1 u1 H0 (wcpr0_refl e1) (pr0_refl 
u1)))))))) (\lambda (c0: C).(\lambda (c3: C).(\lambda (H0: (wcpr0 c0 
c3)).(\lambda (H1: ((\forall (h: nat).(\forall (e1: C).(\forall (u1: 
T).(\forall (k: K).((getl h c3 (CHead e1 k u1)) \to (ex3_2 C T (\lambda (e2: 
C).(\lambda (u2: T).(getl h c0 (CHead e2 k u2)))) (\lambda (e2: C).(\lambda 
(_: T).(wcpr0 e2 e1))) (\lambda (_: C).(\lambda (u2: T).(pr0 u2 
u1))))))))))).(\lambda (u1: T).(\lambda (u2: T).(\lambda (H2: (pr0 u1 
u2)).(\lambda (k: K).(\lambda (h: nat).(nat_ind (\lambda (n: nat).(\forall 
(e1: C).(\forall (u3: T).(\forall (k0: K).((getl n (CHead c3 k u2) (CHead e1 
k0 u3)) \to (ex3_2 C T (\lambda (e2: C).(\lambda (u4: T).(getl n (CHead c0 k 
u1) (CHead e2 k0 u4)))) (\lambda (e2: C).(\lambda (_: T).(wcpr0 e2 e1))) 
(\lambda (_: C).(\lambda (u4: T).(pr0 u4 u3))))))))) (\lambda (e1: 
C).(\lambda (u0: T).(\lambda (k0: K).(\lambda (H3: (getl O (CHead c3 k u2) 
(CHead e1 k0 u0))).(K_ind (\lambda (k1: K).((clear (CHead c3 k1 u2) (CHead e1 
k0 u0)) \to (ex3_2 C T (\lambda (e2: C).(\lambda (u3: T).(getl O (CHead c0 k1 
u1) (CHead e2 k0 u3)))) (\lambda (e2: C).(\lambda (_: T).(wcpr0 e2 e1))) 
(\lambda (_: C).(\lambda (u3: T).(pr0 u3 u0)))))) (\lambda (b: B).(\lambda 
(H4: (clear (CHead c3 (Bind b) u2) (CHead e1 k0 u0))).(let H5 \def (f_equal C 
C (\lambda (e: C).(match e in C return (\lambda (_: C).C) with [(CSort _) 
\Rightarrow e1 | (CHead c _ _) \Rightarrow c])) (CHead e1 k0 u0) (CHead c3 
(Bind b) u2) (clear_gen_bind b c3 (CHead e1 k0 u0) u2 H4)) in ((let H6 \def 
(f_equal C K (\lambda (e: C).(match e in C return (\lambda (_: C).K) with 
[(CSort _) \Rightarrow k0 | (CHead _ k1 _) \Rightarrow k1])) (CHead e1 k0 u0) 
(CHead c3 (Bind b) u2) (clear_gen_bind b c3 (CHead e1 k0 u0) u2 H4)) in ((let 
H7 \def (f_equal C T (\lambda (e: C).(match e in C return (\lambda (_: C).T) 
with [(CSort _) \Rightarrow u0 | (CHead _ _ t) \Rightarrow t])) (CHead e1 k0 
u0) (CHead c3 (Bind b) u2) (clear_gen_bind b c3 (CHead e1 k0 u0) u2 H4)) in 
(\lambda (H8: (eq K k0 (Bind b))).(\lambda (H9: (eq C e1 c3)).(eq_ind_r K 
(Bind b) (\lambda (k1: K).(ex3_2 C T (\lambda (e2: C).(\lambda (u3: T).(getl 
O (CHead c0 (Bind b) u1) (CHead e2 k1 u3)))) (\lambda (e2: C).(\lambda (_: 
T).(wcpr0 e2 e1))) (\lambda (_: C).(\lambda (u3: T).(pr0 u3 u0))))) (eq_ind_r 
T u2 (\lambda (t: T).(ex3_2 C T (\lambda (e2: C).(\lambda (u3: T).(getl O 
(CHead c0 (Bind b) u1) (CHead e2 (Bind b) u3)))) (\lambda (e2: C).(\lambda 
(_: T).(wcpr0 e2 e1))) (\lambda (_: C).(\lambda (u3: T).(pr0 u3 t))))) 
(eq_ind_r C c3 (\lambda (c: C).(ex3_2 C T (\lambda (e2: C).(\lambda (u3: 
T).(getl O (CHead c0 (Bind b) u1) (CHead e2 (Bind b) u3)))) (\lambda (e2: 
C).(\lambda (_: T).(wcpr0 e2 c))) (\lambda (_: C).(\lambda (u3: T).(pr0 u3 
u2))))) (ex3_2_intro C T (\lambda (e2: C).(\lambda (u3: T).(getl O (CHead c0 
(Bind b) u1) (CHead e2 (Bind b) u3)))) (\lambda (e2: C).(\lambda (_: 
T).(wcpr0 e2 c3))) (\lambda (_: C).(\lambda (u3: T).(pr0 u3 u2))) c0 u1 
(getl_refl b c0 u1) H0 H2) e1 H9) u0 H7) k0 H8)))) H6)) H5)))) (\lambda (f: 
F).(\lambda (H4: (clear (CHead c3 (Flat f) u2) (CHead e1 k0 u0))).(let H5 
\def (H1 O e1 u0 k0 (getl_intro O c3 (CHead e1 k0 u0) c3 (drop_refl c3) 
(clear_gen_flat f c3 (CHead e1 k0 u0) u2 H4))) in (ex3_2_ind C T (\lambda 
(e2: C).(\lambda (u3: T).(getl O c0 (CHead e2 k0 u3)))) (\lambda (e2: 
C).(\lambda (_: T).(wcpr0 e2 e1))) (\lambda (_: C).(\lambda (u3: T).(pr0 u3 
u0))) (ex3_2 C T (\lambda (e2: C).(\lambda (u3: T).(getl O (CHead c0 (Flat f) 
u1) (CHead e2 k0 u3)))) (\lambda (e2: C).(\lambda (_: T).(wcpr0 e2 e1))) 
(\lambda (_: C).(\lambda (u3: T).(pr0 u3 u0)))) (\lambda (x0: C).(\lambda 
(x1: T).(\lambda (H6: (getl O c0 (CHead x0 k0 x1))).(\lambda (H7: (wcpr0 x0 
e1)).(\lambda (H8: (pr0 x1 u0)).(ex3_2_intro C T (\lambda (e2: C).(\lambda 
(u3: T).(getl O (CHead c0 (Flat f) u1) (CHead e2 k0 u3)))) (\lambda (e2: 
C).(\lambda (_: T).(wcpr0 e2 e1))) (\lambda (_: C).(\lambda (u3: T).(pr0 u3 
u0))) x0 x1 (getl_flat c0 (CHead x0 k0 x1) O H6 f u1) H7 H8)))))) H5)))) k 
(getl_gen_O (CHead c3 k u2) (CHead e1 k0 u0) H3)))))) (K_ind (\lambda (k0: 
K).(\forall (n: nat).(((\forall (e1: C).(\forall (u3: T).(\forall (k1: 
K).((getl n (CHead c3 k0 u2) (CHead e1 k1 u3)) \to (ex3_2 C T (\lambda (e2: 
C).(\lambda (u4: T).(getl n (CHead c0 k0 u1) (CHead e2 k1 u4)))) (\lambda 
(e2: C).(\lambda (_: T).(wcpr0 e2 e1))) (\lambda (_: C).(\lambda (u4: T).(pr0 
u4 u3))))))))) \to (\forall (e1: C).(\forall (u3: T).(\forall (k1: K).((getl 
(S n) (CHead c3 k0 u2) (CHead e1 k1 u3)) \to (ex3_2 C T (\lambda (e2: 
C).(\lambda (u4: T).(getl (S n) (CHead c0 k0 u1) (CHead e2 k1 u4)))) (\lambda 
(e2: C).(\lambda (_: T).(wcpr0 e2 e1))) (\lambda (_: C).(\lambda (u4: T).(pr0 
u4 u3))))))))))) (\lambda (b: B).(\lambda (n: nat).(\lambda (_: ((\forall 
(e1: C).(\forall (u3: T).(\forall (k0: K).((getl n (CHead c3 (Bind b) u2) 
(CHead e1 k0 u3)) \to (ex3_2 C T (\lambda (e2: C).(\lambda (u4: T).(getl n 
(CHead c0 (Bind b) u1) (CHead e2 k0 u4)))) (\lambda (e2: C).(\lambda (_: 
T).(wcpr0 e2 e1))) (\lambda (_: C).(\lambda (u4: T).(pr0 u4 
u3)))))))))).(\lambda (e1: C).(\lambda (u0: T).(\lambda (k0: K).(\lambda (H4: 
(getl (S n) (CHead c3 (Bind b) u2) (CHead e1 k0 u0))).(let H5 \def (H1 n e1 
u0 k0 (getl_gen_S (Bind b) c3 (CHead e1 k0 u0) u2 n H4)) in (ex3_2_ind C T 
(\lambda (e2: C).(\lambda (u3: T).(getl n c0 (CHead e2 k0 u3)))) (\lambda 
(e2: C).(\lambda (_: T).(wcpr0 e2 e1))) (\lambda (_: C).(\lambda (u3: T).(pr0 
u3 u0))) (ex3_2 C T (\lambda (e2: C).(\lambda (u3: T).(getl (S n) (CHead c0 
(Bind b) u1) (CHead e2 k0 u3)))) (\lambda (e2: C).(\lambda (_: T).(wcpr0 e2 
e1))) (\lambda (_: C).(\lambda (u3: T).(pr0 u3 u0)))) (\lambda (x0: 
C).(\lambda (x1: T).(\lambda (H6: (getl n c0 (CHead x0 k0 x1))).(\lambda (H7: 
(wcpr0 x0 e1)).(\lambda (H8: (pr0 x1 u0)).(ex3_2_intro C T (\lambda (e2: 
C).(\lambda (u3: T).(getl (S n) (CHead c0 (Bind b) u1) (CHead e2 k0 u3)))) 
(\lambda (e2: C).(\lambda (_: T).(wcpr0 e2 e1))) (\lambda (_: C).(\lambda 
(u3: T).(pr0 u3 u0))) x0 x1 (getl_head (Bind b) n c0 (CHead x0 k0 x1) H6 u1) 
H7 H8)))))) H5))))))))) (\lambda (f: F).(\lambda (n: nat).(\lambda (_: 
((\forall (e1: C).(\forall (u3: T).(\forall (k0: K).((getl n (CHead c3 (Flat 
f) u2) (CHead e1 k0 u3)) \to (ex3_2 C T (\lambda (e2: C).(\lambda (u4: 
T).(getl n (CHead c0 (Flat f) u1) (CHead e2 k0 u4)))) (\lambda (e2: 
C).(\lambda (_: T).(wcpr0 e2 e1))) (\lambda (_: C).(\lambda (u4: T).(pr0 u4 
u3)))))))))).(\lambda (e1: C).(\lambda (u0: T).(\lambda (k0: K).(\lambda (H4: 
(getl (S n) (CHead c3 (Flat f) u2) (CHead e1 k0 u0))).(let H5 \def (H1 (S n) 
e1 u0 k0 (getl_gen_S (Flat f) c3 (CHead e1 k0 u0) u2 n H4)) in (ex3_2_ind C T 
(\lambda (e2: C).(\lambda (u3: T).(getl (S n) c0 (CHead e2 k0 u3)))) (\lambda 
(e2: C).(\lambda (_: T).(wcpr0 e2 e1))) (\lambda (_: C).(\lambda (u3: T).(pr0 
u3 u0))) (ex3_2 C T (\lambda (e2: C).(\lambda (u3: T).(getl (S n) (CHead c0 
(Flat f) u1) (CHead e2 k0 u3)))) (\lambda (e2: C).(\lambda (_: T).(wcpr0 e2 
e1))) (\lambda (_: C).(\lambda (u3: T).(pr0 u3 u0)))) (\lambda (x0: 
C).(\lambda (x1: T).(\lambda (H6: (getl (S n) c0 (CHead x0 k0 x1))).(\lambda 
(H7: (wcpr0 x0 e1)).(\lambda (H8: (pr0 x1 u0)).(ex3_2_intro C T (\lambda (e2: 
C).(\lambda (u3: T).(getl (S n) (CHead c0 (Flat f) u1) (CHead e2 k0 u3)))) 
(\lambda (e2: C).(\lambda (_: T).(wcpr0 e2 e1))) (\lambda (_: C).(\lambda 
(u3: T).(pr0 u3 u0))) x0 x1 (getl_head (Flat f) n c0 (CHead x0 k0 x1) H6 u1) 
H7 H8)))))) H5))))))))) k) h)))))))))) c2 c1 H))).

