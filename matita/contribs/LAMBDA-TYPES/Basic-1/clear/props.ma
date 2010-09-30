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

include "Basic-1/clear/fwd.ma".

theorem clear_clear:
 \forall (c1: C).(\forall (c2: C).((clear c1 c2) \to (clear c2 c2)))
\def
 \lambda (c1: C).(C_ind (\lambda (c: C).(\forall (c2: C).((clear c c2) \to 
(clear c2 c2)))) (\lambda (n: nat).(\lambda (c2: C).(\lambda (H: (clear 
(CSort n) c2)).(clear_gen_sort c2 n H (clear c2 c2))))) (\lambda (c: 
C).(\lambda (H: ((\forall (c2: C).((clear c c2) \to (clear c2 
c2))))).(\lambda (k: K).(\lambda (t: T).(\lambda (c2: C).(\lambda (H0: (clear 
(CHead c k t) c2)).(K_ind (\lambda (k0: K).((clear (CHead c k0 t) c2) \to 
(clear c2 c2))) (\lambda (b: B).(\lambda (H1: (clear (CHead c (Bind b) t) 
c2)).(eq_ind_r C (CHead c (Bind b) t) (\lambda (c0: C).(clear c0 c0)) 
(clear_bind b c t) c2 (clear_gen_bind b c c2 t H1)))) (\lambda (f: 
F).(\lambda (H1: (clear (CHead c (Flat f) t) c2)).(H c2 (clear_gen_flat f c 
c2 t H1)))) k H0))))))) c1).
(* COMMENTS
Initial nodes: 199
END *)

theorem clear_mono:
 \forall (c: C).(\forall (c1: C).((clear c c1) \to (\forall (c2: C).((clear c 
c2) \to (eq C c1 c2)))))
\def
 \lambda (c: C).(C_ind (\lambda (c0: C).(\forall (c1: C).((clear c0 c1) \to 
(\forall (c2: C).((clear c0 c2) \to (eq C c1 c2)))))) (\lambda (n: 
nat).(\lambda (c1: C).(\lambda (_: (clear (CSort n) c1)).(\lambda (c2: 
C).(\lambda (H0: (clear (CSort n) c2)).(clear_gen_sort c2 n H0 (eq C c1 
c2))))))) (\lambda (c0: C).(\lambda (H: ((\forall (c1: C).((clear c0 c1) \to 
(\forall (c2: C).((clear c0 c2) \to (eq C c1 c2))))))).(\lambda (k: 
K).(\lambda (t: T).(\lambda (c1: C).(\lambda (H0: (clear (CHead c0 k t) 
c1)).(\lambda (c2: C).(\lambda (H1: (clear (CHead c0 k t) c2)).(K_ind 
(\lambda (k0: K).((clear (CHead c0 k0 t) c1) \to ((clear (CHead c0 k0 t) c2) 
\to (eq C c1 c2)))) (\lambda (b: B).(\lambda (H2: (clear (CHead c0 (Bind b) 
t) c1)).(\lambda (H3: (clear (CHead c0 (Bind b) t) c2)).(eq_ind_r C (CHead c0 
(Bind b) t) (\lambda (c3: C).(eq C c1 c3)) (eq_ind_r C (CHead c0 (Bind b) t) 
(\lambda (c3: C).(eq C c3 (CHead c0 (Bind b) t))) (refl_equal C (CHead c0 
(Bind b) t)) c1 (clear_gen_bind b c0 c1 t H2)) c2 (clear_gen_bind b c0 c2 t 
H3))))) (\lambda (f: F).(\lambda (H2: (clear (CHead c0 (Flat f) t) 
c1)).(\lambda (H3: (clear (CHead c0 (Flat f) t) c2)).(H c1 (clear_gen_flat f 
c0 c1 t H2) c2 (clear_gen_flat f c0 c2 t H3))))) k H0 H1))))))))) c).
(* COMMENTS
Initial nodes: 357
END *)

theorem clear_trans:
 \forall (c1: C).(\forall (c: C).((clear c1 c) \to (\forall (c2: C).((clear c 
c2) \to (clear c1 c2)))))
\def
 \lambda (c1: C).(C_ind (\lambda (c: C).(\forall (c0: C).((clear c c0) \to 
(\forall (c2: C).((clear c0 c2) \to (clear c c2)))))) (\lambda (n: 
nat).(\lambda (c: C).(\lambda (H: (clear (CSort n) c)).(\lambda (c2: 
C).(\lambda (_: (clear c c2)).(clear_gen_sort c n H (clear (CSort n) 
c2))))))) (\lambda (c: C).(\lambda (H: ((\forall (c0: C).((clear c c0) \to 
(\forall (c2: C).((clear c0 c2) \to (clear c c2))))))).(\lambda (k: 
K).(\lambda (t: T).(\lambda (c0: C).(\lambda (H0: (clear (CHead c k t) 
c0)).(\lambda (c2: C).(\lambda (H1: (clear c0 c2)).(K_ind (\lambda (k0: 
K).((clear (CHead c k0 t) c0) \to (clear (CHead c k0 t) c2))) (\lambda (b: 
B).(\lambda (H2: (clear (CHead c (Bind b) t) c0)).(let H3 \def (eq_ind C c0 
(\lambda (c3: C).(clear c3 c2)) H1 (CHead c (Bind b) t) (clear_gen_bind b c 
c0 t H2)) in (eq_ind_r C (CHead c (Bind b) t) (\lambda (c3: C).(clear (CHead 
c (Bind b) t) c3)) (clear_bind b c t) c2 (clear_gen_bind b c c2 t H3))))) 
(\lambda (f: F).(\lambda (H2: (clear (CHead c (Flat f) t) c0)).(clear_flat c 
c2 (H c0 (clear_gen_flat f c c0 t H2) c2 H1) f t))) k H0))))))))) c1).
(* COMMENTS
Initial nodes: 299
END *)

theorem clear_ctail:
 \forall (b: B).(\forall (c1: C).(\forall (c2: C).(\forall (u2: T).((clear c1 
(CHead c2 (Bind b) u2)) \to (\forall (k: K).(\forall (u1: T).(clear (CTail k 
u1 c1) (CHead (CTail k u1 c2) (Bind b) u2))))))))
\def
 \lambda (b: B).(\lambda (c1: C).(C_ind (\lambda (c: C).(\forall (c2: 
C).(\forall (u2: T).((clear c (CHead c2 (Bind b) u2)) \to (\forall (k: 
K).(\forall (u1: T).(clear (CTail k u1 c) (CHead (CTail k u1 c2) (Bind b) 
u2)))))))) (\lambda (n: nat).(\lambda (c2: C).(\lambda (u2: T).(\lambda (H: 
(clear (CSort n) (CHead c2 (Bind b) u2))).(\lambda (k: K).(\lambda (u1: 
T).(K_ind (\lambda (k0: K).(clear (CHead (CSort n) k0 u1) (CHead (CTail k0 u1 
c2) (Bind b) u2))) (\lambda (b0: B).(clear_gen_sort (CHead c2 (Bind b) u2) n 
H (clear (CHead (CSort n) (Bind b0) u1) (CHead (CTail (Bind b0) u1 c2) (Bind 
b) u2)))) (\lambda (f: F).(clear_gen_sort (CHead c2 (Bind b) u2) n H (clear 
(CHead (CSort n) (Flat f) u1) (CHead (CTail (Flat f) u1 c2) (Bind b) u2)))) 
k))))))) (\lambda (c: C).(\lambda (H: ((\forall (c2: C).(\forall (u2: 
T).((clear c (CHead c2 (Bind b) u2)) \to (\forall (k: K).(\forall (u1: 
T).(clear (CTail k u1 c) (CHead (CTail k u1 c2) (Bind b) u2))))))))).(\lambda 
(k: K).(\lambda (t: T).(\lambda (c2: C).(\lambda (u2: T).(\lambda (H0: (clear 
(CHead c k t) (CHead c2 (Bind b) u2))).(\lambda (k0: K).(\lambda (u1: 
T).(K_ind (\lambda (k1: K).((clear (CHead c k1 t) (CHead c2 (Bind b) u2)) \to 
(clear (CHead (CTail k0 u1 c) k1 t) (CHead (CTail k0 u1 c2) (Bind b) u2)))) 
(\lambda (b0: B).(\lambda (H1: (clear (CHead c (Bind b0) t) (CHead c2 (Bind 
b) u2))).(let H2 \def (f_equal C C (\lambda (e: C).(match e in C return 
(\lambda (_: C).C) with [(CSort _) \Rightarrow c2 | (CHead c0 _ _) 
\Rightarrow c0])) (CHead c2 (Bind b) u2) (CHead c (Bind b0) t) 
(clear_gen_bind b0 c (CHead c2 (Bind b) u2) t H1)) in ((let H3 \def (f_equal 
C B (\lambda (e: C).(match e in C return (\lambda (_: C).B) with [(CSort _) 
\Rightarrow b | (CHead _ k1 _) \Rightarrow (match k1 in K return (\lambda (_: 
K).B) with [(Bind b1) \Rightarrow b1 | (Flat _) \Rightarrow b])])) (CHead c2 
(Bind b) u2) (CHead c (Bind b0) t) (clear_gen_bind b0 c (CHead c2 (Bind b) 
u2) t H1)) in ((let H4 \def (f_equal C T (\lambda (e: C).(match e in C return 
(\lambda (_: C).T) with [(CSort _) \Rightarrow u2 | (CHead _ _ t0) 
\Rightarrow t0])) (CHead c2 (Bind b) u2) (CHead c (Bind b0) t) 
(clear_gen_bind b0 c (CHead c2 (Bind b) u2) t H1)) in (\lambda (H5: (eq B b 
b0)).(\lambda (H6: (eq C c2 c)).(eq_ind_r T t (\lambda (t0: T).(clear (CHead 
(CTail k0 u1 c) (Bind b0) t) (CHead (CTail k0 u1 c2) (Bind b) t0))) (eq_ind_r 
C c (\lambda (c0: C).(clear (CHead (CTail k0 u1 c) (Bind b0) t) (CHead (CTail 
k0 u1 c0) (Bind b) t))) (eq_ind B b (\lambda (b1: B).(clear (CHead (CTail k0 
u1 c) (Bind b1) t) (CHead (CTail k0 u1 c) (Bind b) t))) (clear_bind b (CTail 
k0 u1 c) t) b0 H5) c2 H6) u2 H4)))) H3)) H2)))) (\lambda (f: F).(\lambda (H1: 
(clear (CHead c (Flat f) t) (CHead c2 (Bind b) u2))).(clear_flat (CTail k0 u1 
c) (CHead (CTail k0 u1 c2) (Bind b) u2) (H c2 u2 (clear_gen_flat f c (CHead 
c2 (Bind b) u2) t H1) k0 u1) f t))) k H0)))))))))) c1)).
(* COMMENTS
Initial nodes: 819
END *)

theorem clear_cle:
 \forall (c1: C).(\forall (c2: C).((clear c1 c2) \to (cle c2 c1)))
\def
 \lambda (c1: C).(C_ind (\lambda (c: C).(\forall (c2: C).((clear c c2) \to 
(le (cweight c2) (cweight c))))) (\lambda (n: nat).(\lambda (c2: C).(\lambda 
(H: (clear (CSort n) c2)).(clear_gen_sort c2 n H (le (cweight c2) O))))) 
(\lambda (c: C).(\lambda (H: ((\forall (c2: C).((clear c c2) \to (le (cweight 
c2) (cweight c)))))).(\lambda (k: K).(\lambda (t: T).(\lambda (c2: 
C).(\lambda (H0: (clear (CHead c k t) c2)).(K_ind (\lambda (k0: K).((clear 
(CHead c k0 t) c2) \to (le (cweight c2) (plus (cweight c) (tweight t))))) 
(\lambda (b: B).(\lambda (H1: (clear (CHead c (Bind b) t) c2)).(eq_ind_r C 
(CHead c (Bind b) t) (\lambda (c0: C).(le (cweight c0) (plus (cweight c) 
(tweight t)))) (le_n (plus (cweight c) (tweight t))) c2 (clear_gen_bind b c 
c2 t H1)))) (\lambda (f: F).(\lambda (H1: (clear (CHead c (Flat f) t) 
c2)).(le_plus_trans (cweight c2) (cweight c) (tweight t) (H c2 
(clear_gen_flat f c c2 t H1))))) k H0))))))) c1).
(* COMMENTS
Initial nodes: 247
END *)

