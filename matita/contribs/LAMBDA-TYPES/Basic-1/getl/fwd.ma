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

include "Basic-1/getl/defs.ma".

include "Basic-1/drop/fwd.ma".

include "Basic-1/clear/fwd.ma".

theorem getl_gen_all:
 \forall (c1: C).(\forall (c2: C).(\forall (i: nat).((getl i c1 c2) \to (ex2 
C (\lambda (e: C).(drop i O c1 e)) (\lambda (e: C).(clear e c2))))))
\def
 \lambda (c1: C).(\lambda (c2: C).(\lambda (i: nat).(\lambda (H: (getl i c1 
c2)).(getl_ind i c1 c2 (ex2 C (\lambda (e: C).(drop i O c1 e)) (\lambda (e: 
C).(clear e c2))) (\lambda (e: C).(\lambda (H0: (drop i O c1 e)).(\lambda 
(H1: (clear e c2)).(ex_intro2 C (\lambda (e0: C).(drop i O c1 e0)) (\lambda 
(e0: C).(clear e0 c2)) e H0 H1)))) H)))).
(* COMMENTS
Initial nodes: 95
END *)

theorem getl_gen_sort:
 \forall (n: nat).(\forall (h: nat).(\forall (x: C).((getl h (CSort n) x) \to 
(\forall (P: Prop).P))))
\def
 \lambda (n: nat).(\lambda (h: nat).(\lambda (x: C).(\lambda (H: (getl h 
(CSort n) x)).(\lambda (P: Prop).(let H0 \def (getl_gen_all (CSort n) x h H) 
in (ex2_ind C (\lambda (e: C).(drop h O (CSort n) e)) (\lambda (e: C).(clear 
e x)) P (\lambda (x0: C).(\lambda (H1: (drop h O (CSort n) x0)).(\lambda (H2: 
(clear x0 x)).(and3_ind (eq C x0 (CSort n)) (eq nat h O) (eq nat O O) P 
(\lambda (H3: (eq C x0 (CSort n))).(\lambda (_: (eq nat h O)).(\lambda (_: 
(eq nat O O)).(let H6 \def (eq_ind C x0 (\lambda (c: C).(clear c x)) H2 
(CSort n) H3) in (clear_gen_sort x n H6 P))))) (drop_gen_sort n h O x0 
H1))))) H0)))))).
(* COMMENTS
Initial nodes: 179
END *)

theorem getl_gen_O:
 \forall (e: C).(\forall (x: C).((getl O e x) \to (clear e x)))
\def
 \lambda (e: C).(\lambda (x: C).(\lambda (H: (getl O e x)).(let H0 \def 
(getl_gen_all e x O H) in (ex2_ind C (\lambda (e0: C).(drop O O e e0)) 
(\lambda (e0: C).(clear e0 x)) (clear e x) (\lambda (x0: C).(\lambda (H1: 
(drop O O e x0)).(\lambda (H2: (clear x0 x)).(let H3 \def (eq_ind_r C x0 
(\lambda (c: C).(clear c x)) H2 e (drop_gen_refl e x0 H1)) in H3)))) H0)))).
(* COMMENTS
Initial nodes: 99
END *)

theorem getl_gen_S:
 \forall (k: K).(\forall (c: C).(\forall (x: C).(\forall (u: T).(\forall (h: 
nat).((getl (S h) (CHead c k u) x) \to (getl (r k h) c x))))))
\def
 \lambda (k: K).(\lambda (c: C).(\lambda (x: C).(\lambda (u: T).(\lambda (h: 
nat).(\lambda (H: (getl (S h) (CHead c k u) x)).(let H0 \def (getl_gen_all 
(CHead c k u) x (S h) H) in (ex2_ind C (\lambda (e: C).(drop (S h) O (CHead c 
k u) e)) (\lambda (e: C).(clear e x)) (getl (r k h) c x) (\lambda (x0: 
C).(\lambda (H1: (drop (S h) O (CHead c k u) x0)).(\lambda (H2: (clear x0 
x)).(getl_intro (r k h) c x x0 (drop_gen_drop k c x0 u h H1) H2)))) H0))))))).
(* COMMENTS
Initial nodes: 145
END *)

theorem getl_gen_2:
 \forall (c1: C).(\forall (c2: C).(\forall (i: nat).((getl i c1 c2) \to (ex_3 
B C T (\lambda (b: B).(\lambda (c: C).(\lambda (v: T).(eq C c2 (CHead c (Bind 
b) v)))))))))
\def
 \lambda (c1: C).(\lambda (c2: C).(\lambda (i: nat).(\lambda (H: (getl i c1 
c2)).(let H0 \def (getl_gen_all c1 c2 i H) in (ex2_ind C (\lambda (e: 
C).(drop i O c1 e)) (\lambda (e: C).(clear e c2)) (ex_3 B C T (\lambda (b: 
B).(\lambda (c: C).(\lambda (v: T).(eq C c2 (CHead c (Bind b) v)))))) 
(\lambda (x: C).(\lambda (_: (drop i O c1 x)).(\lambda (H2: (clear x 
c2)).(let H3 \def (clear_gen_all x c2 H2) in (ex_3_ind B C T (\lambda (b: 
B).(\lambda (e: C).(\lambda (u: T).(eq C c2 (CHead e (Bind b) u))))) (ex_3 B 
C T (\lambda (b: B).(\lambda (c: C).(\lambda (v: T).(eq C c2 (CHead c (Bind 
b) v)))))) (\lambda (x0: B).(\lambda (x1: C).(\lambda (x2: T).(\lambda (H4: 
(eq C c2 (CHead x1 (Bind x0) x2))).(let H5 \def (eq_ind C c2 (\lambda (c: 
C).(clear x c)) H2 (CHead x1 (Bind x0) x2) H4) in (eq_ind_r C (CHead x1 (Bind 
x0) x2) (\lambda (c: C).(ex_3 B C T (\lambda (b: B).(\lambda (c0: C).(\lambda 
(v: T).(eq C c (CHead c0 (Bind b) v))))))) (ex_3_intro B C T (\lambda (b: 
B).(\lambda (c: C).(\lambda (v: T).(eq C (CHead x1 (Bind x0) x2) (CHead c 
(Bind b) v))))) x0 x1 x2 (refl_equal C (CHead x1 (Bind x0) x2))) c2 H4)))))) 
H3))))) H0))))).
(* COMMENTS
Initial nodes: 325
END *)

theorem getl_gen_flat:
 \forall (f: F).(\forall (e: C).(\forall (d: C).(\forall (v: T).(\forall (i: 
nat).((getl i (CHead e (Flat f) v) d) \to (getl i e d))))))
\def
 \lambda (f: F).(\lambda (e: C).(\lambda (d: C).(\lambda (v: T).(\lambda (i: 
nat).(nat_ind (\lambda (n: nat).((getl n (CHead e (Flat f) v) d) \to (getl n 
e d))) (\lambda (H: (getl O (CHead e (Flat f) v) d)).(getl_intro O e d e 
(drop_refl e) (clear_gen_flat f e d v (getl_gen_O (CHead e (Flat f) v) d 
H)))) (\lambda (n: nat).(\lambda (_: (((getl n (CHead e (Flat f) v) d) \to 
(getl n e d)))).(\lambda (H0: (getl (S n) (CHead e (Flat f) v) 
d)).(getl_gen_S (Flat f) e d v n H0)))) i))))).
(* COMMENTS
Initial nodes: 155
END *)

theorem getl_gen_bind:
 \forall (b: B).(\forall (e: C).(\forall (d: C).(\forall (v: T).(\forall (i: 
nat).((getl i (CHead e (Bind b) v) d) \to (or (land (eq nat i O) (eq C d 
(CHead e (Bind b) v))) (ex2 nat (\lambda (j: nat).(eq nat i (S j))) (\lambda 
(j: nat).(getl j e d)))))))))
\def
 \lambda (b: B).(\lambda (e: C).(\lambda (d: C).(\lambda (v: T).(\lambda (i: 
nat).(nat_ind (\lambda (n: nat).((getl n (CHead e (Bind b) v) d) \to (or 
(land (eq nat n O) (eq C d (CHead e (Bind b) v))) (ex2 nat (\lambda (j: 
nat).(eq nat n (S j))) (\lambda (j: nat).(getl j e d)))))) (\lambda (H: (getl 
O (CHead e (Bind b) v) d)).(eq_ind_r C (CHead e (Bind b) v) (\lambda (c: 
C).(or (land (eq nat O O) (eq C c (CHead e (Bind b) v))) (ex2 nat (\lambda 
(j: nat).(eq nat O (S j))) (\lambda (j: nat).(getl j e c))))) (or_introl 
(land (eq nat O O) (eq C (CHead e (Bind b) v) (CHead e (Bind b) v))) (ex2 nat 
(\lambda (j: nat).(eq nat O (S j))) (\lambda (j: nat).(getl j e (CHead e 
(Bind b) v)))) (conj (eq nat O O) (eq C (CHead e (Bind b) v) (CHead e (Bind 
b) v)) (refl_equal nat O) (refl_equal C (CHead e (Bind b) v)))) d 
(clear_gen_bind b e d v (getl_gen_O (CHead e (Bind b) v) d H)))) (\lambda (n: 
nat).(\lambda (_: (((getl n (CHead e (Bind b) v) d) \to (or (land (eq nat n 
O) (eq C d (CHead e (Bind b) v))) (ex2 nat (\lambda (j: nat).(eq nat n (S 
j))) (\lambda (j: nat).(getl j e d))))))).(\lambda (H0: (getl (S n) (CHead e 
(Bind b) v) d)).(or_intror (land (eq nat (S n) O) (eq C d (CHead e (Bind b) 
v))) (ex2 nat (\lambda (j: nat).(eq nat (S n) (S j))) (\lambda (j: nat).(getl 
j e d))) (ex_intro2 nat (\lambda (j: nat).(eq nat (S n) (S j))) (\lambda (j: 
nat).(getl j e d)) n (refl_equal nat (S n)) (getl_gen_S (Bind b) e d v n 
H0)))))) i))))).
(* COMMENTS
Initial nodes: 525
END *)

