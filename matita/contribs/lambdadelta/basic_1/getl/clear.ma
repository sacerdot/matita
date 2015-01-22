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

include "Basic-1/getl/props.ma".

include "Basic-1/clear/drop.ma".

theorem clear_getl_trans:
 \forall (i: nat).(\forall (c2: C).(\forall (c3: C).((getl i c2 c3) \to 
(\forall (c1: C).((clear c1 c2) \to (getl i c1 c3))))))
\def
 \lambda (i: nat).(nat_ind (\lambda (n: nat).(\forall (c2: C).(\forall (c3: 
C).((getl n c2 c3) \to (\forall (c1: C).((clear c1 c2) \to (getl n c1 
c3))))))) (\lambda (c2: C).(\lambda (c3: C).(\lambda (H: (getl O c2 
c3)).(\lambda (c1: C).(\lambda (H0: (clear c1 c2)).(getl_intro O c1 c3 c1 
(drop_refl c1) (clear_trans c1 c2 H0 c3 (getl_gen_O c2 c3 H)))))))) (\lambda 
(n: nat).(\lambda (_: ((\forall (c2: C).(\forall (c3: C).((getl n c2 c3) \to 
(\forall (c1: C).((clear c1 c2) \to (getl n c1 c3)))))))).(\lambda (c2: 
C).(C_ind (\lambda (c: C).(\forall (c3: C).((getl (S n) c c3) \to (\forall 
(c1: C).((clear c1 c) \to (getl (S n) c1 c3)))))) (\lambda (n0: nat).(\lambda 
(c3: C).(\lambda (H0: (getl (S n) (CSort n0) c3)).(\lambda (c1: C).(\lambda 
(_: (clear c1 (CSort n0))).(getl_gen_sort n0 (S n) c3 H0 (getl (S n) c1 
c3))))))) (\lambda (c: C).(\lambda (_: ((\forall (c3: C).((getl (S n) c c3) 
\to (\forall (c1: C).((clear c1 c) \to (getl (S n) c1 c3))))))).(\lambda (k: 
K).(\lambda (t: T).(\lambda (c3: C).(\lambda (H1: (getl (S n) (CHead c k t) 
c3)).(\lambda (c1: C).(\lambda (H2: (clear c1 (CHead c k t))).(K_ind (\lambda 
(k0: K).((getl (S n) (CHead c k0 t) c3) \to ((clear c1 (CHead c k0 t)) \to 
(getl (S n) c1 c3)))) (\lambda (b: B).(\lambda (H3: (getl (S n) (CHead c 
(Bind b) t) c3)).(\lambda (H4: (clear c1 (CHead c (Bind b) t))).(let H5 \def 
(getl_gen_all c c3 (r (Bind b) n) (getl_gen_S (Bind b) c c3 t n H3)) in 
(ex2_ind C (\lambda (e: C).(drop n O c e)) (\lambda (e: C).(clear e c3)) 
(getl (S n) c1 c3) (\lambda (x: C).(\lambda (H6: (drop n O c x)).(\lambda 
(H7: (clear x c3)).(getl_intro (S n) c1 c3 x (drop_clear_O b c1 c t H4 x n 
H6) H7)))) H5))))) (\lambda (f: F).(\lambda (_: (getl (S n) (CHead c (Flat f) 
t) c3)).(\lambda (H4: (clear c1 (CHead c (Flat f) t))).(clear_gen_flat_r f c1 
c t H4 (getl (S n) c1 c3))))) k H1 H2))))))))) c2)))) i).
(* COMMENTS
Initial nodes: 525
END *)

theorem getl_clear_trans:
 \forall (i: nat).(\forall (c1: C).(\forall (c2: C).((getl i c1 c2) \to 
(\forall (c3: C).((clear c2 c3) \to (getl i c1 c3))))))
\def
 \lambda (i: nat).(\lambda (c1: C).(\lambda (c2: C).(\lambda (H: (getl i c1 
c2)).(\lambda (c3: C).(\lambda (H0: (clear c2 c3)).(let H1 \def (getl_gen_all 
c1 c2 i H) in (ex2_ind C (\lambda (e: C).(drop i O c1 e)) (\lambda (e: 
C).(clear e c2)) (getl i c1 c3) (\lambda (x: C).(\lambda (H2: (drop i O c1 
x)).(\lambda (H3: (clear x c2)).(let H4 \def (clear_gen_all x c2 H3) in 
(ex_3_ind B C T (\lambda (b: B).(\lambda (e: C).(\lambda (u: T).(eq C c2 
(CHead e (Bind b) u))))) (getl i c1 c3) (\lambda (x0: B).(\lambda (x1: 
C).(\lambda (x2: T).(\lambda (H5: (eq C c2 (CHead x1 (Bind x0) x2))).(let H6 
\def (eq_ind C c2 (\lambda (c: C).(clear x c)) H3 (CHead x1 (Bind x0) x2) H5) 
in (let H7 \def (eq_ind C c2 (\lambda (c: C).(clear c c3)) H0 (CHead x1 (Bind 
x0) x2) H5) in (eq_ind_r C (CHead x1 (Bind x0) x2) (\lambda (c: C).(getl i c1 
c)) (getl_intro i c1 (CHead x1 (Bind x0) x2) x H2 H6) c3 (clear_gen_bind x0 
x1 c3 x2 H7)))))))) H4))))) H1))))))).
(* COMMENTS
Initial nodes: 269
END *)

theorem getl_clear_bind:
 \forall (b: B).(\forall (c: C).(\forall (e1: C).(\forall (v: T).((clear c 
(CHead e1 (Bind b) v)) \to (\forall (e2: C).(\forall (n: nat).((getl n e1 e2) 
\to (getl (S n) c e2))))))))
\def
 \lambda (b: B).(\lambda (c: C).(C_ind (\lambda (c0: C).(\forall (e1: 
C).(\forall (v: T).((clear c0 (CHead e1 (Bind b) v)) \to (\forall (e2: 
C).(\forall (n: nat).((getl n e1 e2) \to (getl (S n) c0 e2)))))))) (\lambda 
(n: nat).(\lambda (e1: C).(\lambda (v: T).(\lambda (H: (clear (CSort n) 
(CHead e1 (Bind b) v))).(\lambda (e2: C).(\lambda (n0: nat).(\lambda (_: 
(getl n0 e1 e2)).(clear_gen_sort (CHead e1 (Bind b) v) n H (getl (S n0) 
(CSort n) e2))))))))) (\lambda (c0: C).(\lambda (H: ((\forall (e1: 
C).(\forall (v: T).((clear c0 (CHead e1 (Bind b) v)) \to (\forall (e2: 
C).(\forall (n: nat).((getl n e1 e2) \to (getl (S n) c0 e2))))))))).(\lambda 
(k: K).(\lambda (t: T).(\lambda (e1: C).(\lambda (v: T).(\lambda (H0: (clear 
(CHead c0 k t) (CHead e1 (Bind b) v))).(\lambda (e2: C).(\lambda (n: 
nat).(\lambda (H1: (getl n e1 e2)).(K_ind (\lambda (k0: K).((clear (CHead c0 
k0 t) (CHead e1 (Bind b) v)) \to (getl (S n) (CHead c0 k0 t) e2))) (\lambda 
(b0: B).(\lambda (H2: (clear (CHead c0 (Bind b0) t) (CHead e1 (Bind b) 
v))).(let H3 \def (f_equal C C (\lambda (e: C).(match e in C return (\lambda 
(_: C).C) with [(CSort _) \Rightarrow e1 | (CHead c1 _ _) \Rightarrow c1])) 
(CHead e1 (Bind b) v) (CHead c0 (Bind b0) t) (clear_gen_bind b0 c0 (CHead e1 
(Bind b) v) t H2)) in ((let H4 \def (f_equal C B (\lambda (e: C).(match e in 
C return (\lambda (_: C).B) with [(CSort _) \Rightarrow b | (CHead _ k0 _) 
\Rightarrow (match k0 in K return (\lambda (_: K).B) with [(Bind b1) 
\Rightarrow b1 | (Flat _) \Rightarrow b])])) (CHead e1 (Bind b) v) (CHead c0 
(Bind b0) t) (clear_gen_bind b0 c0 (CHead e1 (Bind b) v) t H2)) in ((let H5 
\def (f_equal C T (\lambda (e: C).(match e in C return (\lambda (_: C).T) 
with [(CSort _) \Rightarrow v | (CHead _ _ t0) \Rightarrow t0])) (CHead e1 
(Bind b) v) (CHead c0 (Bind b0) t) (clear_gen_bind b0 c0 (CHead e1 (Bind b) 
v) t H2)) in (\lambda (H6: (eq B b b0)).(\lambda (H7: (eq C e1 c0)).(let H8 
\def (eq_ind C e1 (\lambda (c1: C).(getl n c1 e2)) H1 c0 H7) in (eq_ind B b 
(\lambda (b1: B).(getl (S n) (CHead c0 (Bind b1) t) e2)) (getl_head (Bind b) 
n c0 e2 H8 t) b0 H6))))) H4)) H3)))) (\lambda (f: F).(\lambda (H2: (clear 
(CHead c0 (Flat f) t) (CHead e1 (Bind b) v))).(getl_flat c0 e2 (S n) (H e1 v 
(clear_gen_flat f c0 (CHead e1 (Bind b) v) t H2) e2 n H1) f t))) k 
H0))))))))))) c)).
(* COMMENTS
Initial nodes: 599
END *)

theorem getl_clear_conf:
 \forall (i: nat).(\forall (c1: C).(\forall (c3: C).((getl i c1 c3) \to 
(\forall (c2: C).((clear c1 c2) \to (getl i c2 c3))))))
\def
 \lambda (i: nat).(nat_ind (\lambda (n: nat).(\forall (c1: C).(\forall (c3: 
C).((getl n c1 c3) \to (\forall (c2: C).((clear c1 c2) \to (getl n c2 
c3))))))) (\lambda (c1: C).(\lambda (c3: C).(\lambda (H: (getl O c1 
c3)).(\lambda (c2: C).(\lambda (H0: (clear c1 c2)).(eq_ind C c3 (\lambda (c: 
C).(getl O c c3)) (let H1 \def (clear_gen_all c1 c3 (getl_gen_O c1 c3 H)) in 
(ex_3_ind B C T (\lambda (b: B).(\lambda (e: C).(\lambda (u: T).(eq C c3 
(CHead e (Bind b) u))))) (getl O c3 c3) (\lambda (x0: B).(\lambda (x1: 
C).(\lambda (x2: T).(\lambda (H2: (eq C c3 (CHead x1 (Bind x0) x2))).(let H3 
\def (eq_ind C c3 (\lambda (c: C).(clear c1 c)) (getl_gen_O c1 c3 H) (CHead 
x1 (Bind x0) x2) H2) in (eq_ind_r C (CHead x1 (Bind x0) x2) (\lambda (c: 
C).(getl O c c)) (getl_refl x0 x1 x2) c3 H2)))))) H1)) c2 (clear_mono c1 c3 
(getl_gen_O c1 c3 H) c2 H0))))))) (\lambda (n: nat).(\lambda (_: ((\forall 
(c1: C).(\forall (c3: C).((getl n c1 c3) \to (\forall (c2: C).((clear c1 c2) 
\to (getl n c2 c3)))))))).(\lambda (c1: C).(C_ind (\lambda (c: C).(\forall 
(c3: C).((getl (S n) c c3) \to (\forall (c2: C).((clear c c2) \to (getl (S n) 
c2 c3)))))) (\lambda (n0: nat).(\lambda (c3: C).(\lambda (H0: (getl (S n) 
(CSort n0) c3)).(\lambda (c2: C).(\lambda (_: (clear (CSort n0) 
c2)).(getl_gen_sort n0 (S n) c3 H0 (getl (S n) c2 c3))))))) (\lambda (c: 
C).(\lambda (H0: ((\forall (c3: C).((getl (S n) c c3) \to (\forall (c2: 
C).((clear c c2) \to (getl (S n) c2 c3))))))).(\lambda (k: K).(\lambda (t: 
T).(\lambda (c3: C).(\lambda (H1: (getl (S n) (CHead c k t) c3)).(\lambda 
(c2: C).(\lambda (H2: (clear (CHead c k t) c2)).(K_ind (\lambda (k0: 
K).((getl (S n) (CHead c k0 t) c3) \to ((clear (CHead c k0 t) c2) \to (getl 
(S n) c2 c3)))) (\lambda (b: B).(\lambda (H3: (getl (S n) (CHead c (Bind b) 
t) c3)).(\lambda (H4: (clear (CHead c (Bind b) t) c2)).(eq_ind_r C (CHead c 
(Bind b) t) (\lambda (c0: C).(getl (S n) c0 c3)) (getl_head (Bind b) n c c3 
(getl_gen_S (Bind b) c c3 t n H3) t) c2 (clear_gen_bind b c c2 t H4))))) 
(\lambda (f: F).(\lambda (H3: (getl (S n) (CHead c (Flat f) t) c3)).(\lambda 
(H4: (clear (CHead c (Flat f) t) c2)).(H0 c3 (getl_gen_S (Flat f) c c3 t n 
H3) c2 (clear_gen_flat f c c2 t H4))))) k H1 H2))))))))) c1)))) i).
(* COMMENTS
Initial nodes: 641
END *)

