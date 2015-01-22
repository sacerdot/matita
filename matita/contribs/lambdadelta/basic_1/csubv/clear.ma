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

include "Basic-1/csubv/defs.ma".

include "Basic-1/clear/fwd.ma".

theorem csubv_clear_conf:
 \forall (c1: C).(\forall (c2: C).((csubv c1 c2) \to (\forall (b1: 
B).(\forall (d1: C).(\forall (v1: T).((clear c1 (CHead d1 (Bind b1) v1)) \to 
(ex2_3 B C T (\lambda (_: B).(\lambda (d2: C).(\lambda (_: T).(csubv d1 
d2)))) (\lambda (b2: B).(\lambda (d2: C).(\lambda (v2: T).(clear c2 (CHead d2 
(Bind b2) v2))))))))))))
\def
 \lambda (c1: C).(\lambda (c2: C).(\lambda (H: (csubv c1 c2)).(csubv_ind 
(\lambda (c: C).(\lambda (c0: C).(\forall (b1: B).(\forall (d1: C).(\forall 
(v1: T).((clear c (CHead d1 (Bind b1) v1)) \to (ex2_3 B C T (\lambda (_: 
B).(\lambda (d2: C).(\lambda (_: T).(csubv d1 d2)))) (\lambda (b2: 
B).(\lambda (d2: C).(\lambda (v2: T).(clear c0 (CHead d2 (Bind b2) 
v2)))))))))))) (\lambda (n: nat).(\lambda (b1: B).(\lambda (d1: C).(\lambda 
(v1: T).(\lambda (H0: (clear (CSort n) (CHead d1 (Bind b1) 
v1))).(clear_gen_sort (CHead d1 (Bind b1) v1) n H0 (ex2_3 B C T (\lambda (_: 
B).(\lambda (d2: C).(\lambda (_: T).(csubv d1 d2)))) (\lambda (b2: 
B).(\lambda (d2: C).(\lambda (v2: T).(clear (CSort n) (CHead d2 (Bind b2) 
v2)))))))))))) (\lambda (c3: C).(\lambda (c4: C).(\lambda (H0: (csubv c3 
c4)).(\lambda (_: ((\forall (b1: B).(\forall (d1: C).(\forall (v1: T).((clear 
c3 (CHead d1 (Bind b1) v1)) \to (ex2_3 B C T (\lambda (_: B).(\lambda (d2: 
C).(\lambda (_: T).(csubv d1 d2)))) (\lambda (b2: B).(\lambda (d2: 
C).(\lambda (v2: T).(clear c4 (CHead d2 (Bind b2) v2)))))))))))).(\lambda 
(v1: T).(\lambda (v2: T).(\lambda (b1: B).(\lambda (d1: C).(\lambda (v0: 
T).(\lambda (H2: (clear (CHead c3 (Bind Void) v1) (CHead d1 (Bind b1) 
v0))).(let H3 \def (f_equal C C (\lambda (e: C).(match e in C return (\lambda 
(_: C).C) with [(CSort _) \Rightarrow d1 | (CHead c _ _) \Rightarrow c])) 
(CHead d1 (Bind b1) v0) (CHead c3 (Bind Void) v1) (clear_gen_bind Void c3 
(CHead d1 (Bind b1) v0) v1 H2)) in ((let H4 \def (f_equal C B (\lambda (e: 
C).(match e in C return (\lambda (_: C).B) with [(CSort _) \Rightarrow b1 | 
(CHead _ k _) \Rightarrow (match k in K return (\lambda (_: K).B) with [(Bind 
b) \Rightarrow b | (Flat _) \Rightarrow b1])])) (CHead d1 (Bind b1) v0) 
(CHead c3 (Bind Void) v1) (clear_gen_bind Void c3 (CHead d1 (Bind b1) v0) v1 
H2)) in ((let H5 \def (f_equal C T (\lambda (e: C).(match e in C return 
(\lambda (_: C).T) with [(CSort _) \Rightarrow v0 | (CHead _ _ t) \Rightarrow 
t])) (CHead d1 (Bind b1) v0) (CHead c3 (Bind Void) v1) (clear_gen_bind Void 
c3 (CHead d1 (Bind b1) v0) v1 H2)) in (\lambda (_: (eq B b1 Void)).(\lambda 
(H7: (eq C d1 c3)).(eq_ind_r C c3 (\lambda (c: C).(ex2_3 B C T (\lambda (_: 
B).(\lambda (d2: C).(\lambda (_: T).(csubv c d2)))) (\lambda (b2: B).(\lambda 
(d2: C).(\lambda (v3: T).(clear (CHead c4 (Bind Void) v2) (CHead d2 (Bind b2) 
v3))))))) (ex2_3_intro B C T (\lambda (_: B).(\lambda (d2: C).(\lambda (_: 
T).(csubv c3 d2)))) (\lambda (b2: B).(\lambda (d2: C).(\lambda (v3: T).(clear 
(CHead c4 (Bind Void) v2) (CHead d2 (Bind b2) v3))))) Void c4 v2 H0 
(clear_bind Void c4 v2)) d1 H7)))) H4)) H3)))))))))))) (\lambda (c3: 
C).(\lambda (c4: C).(\lambda (H0: (csubv c3 c4)).(\lambda (_: ((\forall (b1: 
B).(\forall (d1: C).(\forall (v1: T).((clear c3 (CHead d1 (Bind b1) v1)) \to 
(ex2_3 B C T (\lambda (_: B).(\lambda (d2: C).(\lambda (_: T).(csubv d1 
d2)))) (\lambda (b2: B).(\lambda (d2: C).(\lambda (v2: T).(clear c4 (CHead d2 
(Bind b2) v2)))))))))))).(\lambda (b1: B).(\lambda (_: (not (eq B b1 
Void))).(\lambda (b2: B).(\lambda (v1: T).(\lambda (v2: T).(\lambda (b0: 
B).(\lambda (d1: C).(\lambda (v0: T).(\lambda (H3: (clear (CHead c3 (Bind b1) 
v1) (CHead d1 (Bind b0) v0))).(let H4 \def (f_equal C C (\lambda (e: 
C).(match e in C return (\lambda (_: C).C) with [(CSort _) \Rightarrow d1 | 
(CHead c _ _) \Rightarrow c])) (CHead d1 (Bind b0) v0) (CHead c3 (Bind b1) 
v1) (clear_gen_bind b1 c3 (CHead d1 (Bind b0) v0) v1 H3)) in ((let H5 \def 
(f_equal C B (\lambda (e: C).(match e in C return (\lambda (_: C).B) with 
[(CSort _) \Rightarrow b0 | (CHead _ k _) \Rightarrow (match k in K return 
(\lambda (_: K).B) with [(Bind b) \Rightarrow b | (Flat _) \Rightarrow 
b0])])) (CHead d1 (Bind b0) v0) (CHead c3 (Bind b1) v1) (clear_gen_bind b1 c3 
(CHead d1 (Bind b0) v0) v1 H3)) in ((let H6 \def (f_equal C T (\lambda (e: 
C).(match e in C return (\lambda (_: C).T) with [(CSort _) \Rightarrow v0 | 
(CHead _ _ t) \Rightarrow t])) (CHead d1 (Bind b0) v0) (CHead c3 (Bind b1) 
v1) (clear_gen_bind b1 c3 (CHead d1 (Bind b0) v0) v1 H3)) in (\lambda (_: (eq 
B b0 b1)).(\lambda (H8: (eq C d1 c3)).(eq_ind_r C c3 (\lambda (c: C).(ex2_3 B 
C T (\lambda (_: B).(\lambda (d2: C).(\lambda (_: T).(csubv c d2)))) (\lambda 
(b3: B).(\lambda (d2: C).(\lambda (v3: T).(clear (CHead c4 (Bind b2) v2) 
(CHead d2 (Bind b3) v3))))))) (ex2_3_intro B C T (\lambda (_: B).(\lambda 
(d2: C).(\lambda (_: T).(csubv c3 d2)))) (\lambda (b3: B).(\lambda (d2: 
C).(\lambda (v3: T).(clear (CHead c4 (Bind b2) v2) (CHead d2 (Bind b3) 
v3))))) b2 c4 v2 H0 (clear_bind b2 c4 v2)) d1 H8)))) H5)) H4))))))))))))))) 
(\lambda (c3: C).(\lambda (c4: C).(\lambda (_: (csubv c3 c4)).(\lambda (H1: 
((\forall (b1: B).(\forall (d1: C).(\forall (v1: T).((clear c3 (CHead d1 
(Bind b1) v1)) \to (ex2_3 B C T (\lambda (_: B).(\lambda (d2: C).(\lambda (_: 
T).(csubv d1 d2)))) (\lambda (b2: B).(\lambda (d2: C).(\lambda (v2: T).(clear 
c4 (CHead d2 (Bind b2) v2)))))))))))).(\lambda (f1: F).(\lambda (f2: 
F).(\lambda (v1: T).(\lambda (v2: T).(\lambda (b1: B).(\lambda (d1: 
C).(\lambda (v0: T).(\lambda (H2: (clear (CHead c3 (Flat f1) v1) (CHead d1 
(Bind b1) v0))).(let H_x \def (H1 b1 d1 v0 (clear_gen_flat f1 c3 (CHead d1 
(Bind b1) v0) v1 H2)) in (let H3 \def H_x in (ex2_3_ind B C T (\lambda (_: 
B).(\lambda (d2: C).(\lambda (_: T).(csubv d1 d2)))) (\lambda (b2: 
B).(\lambda (d2: C).(\lambda (v3: T).(clear c4 (CHead d2 (Bind b2) v3))))) 
(ex2_3 B C T (\lambda (_: B).(\lambda (d2: C).(\lambda (_: T).(csubv d1 
d2)))) (\lambda (b2: B).(\lambda (d2: C).(\lambda (v3: T).(clear (CHead c4 
(Flat f2) v2) (CHead d2 (Bind b2) v3)))))) (\lambda (x0: B).(\lambda (x1: 
C).(\lambda (x2: T).(\lambda (H4: (csubv d1 x1)).(\lambda (H5: (clear c4 
(CHead x1 (Bind x0) x2))).(ex2_3_intro B C T (\lambda (_: B).(\lambda (d2: 
C).(\lambda (_: T).(csubv d1 d2)))) (\lambda (b2: B).(\lambda (d2: 
C).(\lambda (v3: T).(clear (CHead c4 (Flat f2) v2) (CHead d2 (Bind b2) 
v3))))) x0 x1 x2 H4 (clear_flat c4 (CHead x1 (Bind x0) x2) H5 f2 v2))))))) 
H3))))))))))))))) c1 c2 H))).
(* COMMENTS
Initial nodes: 1357
END *)

theorem csubv_clear_conf_void:
 \forall (c1: C).(\forall (c2: C).((csubv c1 c2) \to (\forall (d1: 
C).(\forall (v1: T).((clear c1 (CHead d1 (Bind Void) v1)) \to (ex2_2 C T 
(\lambda (d2: C).(\lambda (_: T).(csubv d1 d2))) (\lambda (d2: C).(\lambda 
(v2: T).(clear c2 (CHead d2 (Bind Void) v2))))))))))
\def
 \lambda (c1: C).(\lambda (c2: C).(\lambda (H: (csubv c1 c2)).(csubv_ind 
(\lambda (c: C).(\lambda (c0: C).(\forall (d1: C).(\forall (v1: T).((clear c 
(CHead d1 (Bind Void) v1)) \to (ex2_2 C T (\lambda (d2: C).(\lambda (_: 
T).(csubv d1 d2))) (\lambda (d2: C).(\lambda (v2: T).(clear c0 (CHead d2 
(Bind Void) v2)))))))))) (\lambda (n: nat).(\lambda (d1: C).(\lambda (v1: 
T).(\lambda (H0: (clear (CSort n) (CHead d1 (Bind Void) v1))).(clear_gen_sort 
(CHead d1 (Bind Void) v1) n H0 (ex2_2 C T (\lambda (d2: C).(\lambda (_: 
T).(csubv d1 d2))) (\lambda (d2: C).(\lambda (v2: T).(clear (CSort n) (CHead 
d2 (Bind Void) v2)))))))))) (\lambda (c3: C).(\lambda (c4: C).(\lambda (H0: 
(csubv c3 c4)).(\lambda (_: ((\forall (d1: C).(\forall (v1: T).((clear c3 
(CHead d1 (Bind Void) v1)) \to (ex2_2 C T (\lambda (d2: C).(\lambda (_: 
T).(csubv d1 d2))) (\lambda (d2: C).(\lambda (v2: T).(clear c4 (CHead d2 
(Bind Void) v2)))))))))).(\lambda (v1: T).(\lambda (v2: T).(\lambda (d1: 
C).(\lambda (v0: T).(\lambda (H2: (clear (CHead c3 (Bind Void) v1) (CHead d1 
(Bind Void) v0))).(let H3 \def (f_equal C C (\lambda (e: C).(match e in C 
return (\lambda (_: C).C) with [(CSort _) \Rightarrow d1 | (CHead c _ _) 
\Rightarrow c])) (CHead d1 (Bind Void) v0) (CHead c3 (Bind Void) v1) 
(clear_gen_bind Void c3 (CHead d1 (Bind Void) v0) v1 H2)) in ((let H4 \def 
(f_equal C T (\lambda (e: C).(match e in C return (\lambda (_: C).T) with 
[(CSort _) \Rightarrow v0 | (CHead _ _ t) \Rightarrow t])) (CHead d1 (Bind 
Void) v0) (CHead c3 (Bind Void) v1) (clear_gen_bind Void c3 (CHead d1 (Bind 
Void) v0) v1 H2)) in (\lambda (H5: (eq C d1 c3)).(eq_ind_r C c3 (\lambda (c: 
C).(ex2_2 C T (\lambda (d2: C).(\lambda (_: T).(csubv c d2))) (\lambda (d2: 
C).(\lambda (v3: T).(clear (CHead c4 (Bind Void) v2) (CHead d2 (Bind Void) 
v3)))))) (ex2_2_intro C T (\lambda (d2: C).(\lambda (_: T).(csubv c3 d2))) 
(\lambda (d2: C).(\lambda (v3: T).(clear (CHead c4 (Bind Void) v2) (CHead d2 
(Bind Void) v3)))) c4 v2 H0 (clear_bind Void c4 v2)) d1 H5))) H3))))))))))) 
(\lambda (c3: C).(\lambda (c4: C).(\lambda (_: (csubv c3 c4)).(\lambda (_: 
((\forall (d1: C).(\forall (v1: T).((clear c3 (CHead d1 (Bind Void) v1)) \to 
(ex2_2 C T (\lambda (d2: C).(\lambda (_: T).(csubv d1 d2))) (\lambda (d2: 
C).(\lambda (v2: T).(clear c4 (CHead d2 (Bind Void) v2)))))))))).(\lambda 
(b1: B).(\lambda (H2: (not (eq B b1 Void))).(\lambda (b2: B).(\lambda (v1: 
T).(\lambda (v2: T).(\lambda (d1: C).(\lambda (v0: T).(\lambda (H3: (clear 
(CHead c3 (Bind b1) v1) (CHead d1 (Bind Void) v0))).(let H4 \def (f_equal C C 
(\lambda (e: C).(match e in C return (\lambda (_: C).C) with [(CSort _) 
\Rightarrow d1 | (CHead c _ _) \Rightarrow c])) (CHead d1 (Bind Void) v0) 
(CHead c3 (Bind b1) v1) (clear_gen_bind b1 c3 (CHead d1 (Bind Void) v0) v1 
H3)) in ((let H5 \def (f_equal C B (\lambda (e: C).(match e in C return 
(\lambda (_: C).B) with [(CSort _) \Rightarrow Void | (CHead _ k _) 
\Rightarrow (match k in K return (\lambda (_: K).B) with [(Bind b) 
\Rightarrow b | (Flat _) \Rightarrow Void])])) (CHead d1 (Bind Void) v0) 
(CHead c3 (Bind b1) v1) (clear_gen_bind b1 c3 (CHead d1 (Bind Void) v0) v1 
H3)) in ((let H6 \def (f_equal C T (\lambda (e: C).(match e in C return 
(\lambda (_: C).T) with [(CSort _) \Rightarrow v0 | (CHead _ _ t) \Rightarrow 
t])) (CHead d1 (Bind Void) v0) (CHead c3 (Bind b1) v1) (clear_gen_bind b1 c3 
(CHead d1 (Bind Void) v0) v1 H3)) in (\lambda (H7: (eq B Void b1)).(\lambda 
(H8: (eq C d1 c3)).(eq_ind_r C c3 (\lambda (c: C).(ex2_2 C T (\lambda (d2: 
C).(\lambda (_: T).(csubv c d2))) (\lambda (d2: C).(\lambda (v3: T).(clear 
(CHead c4 (Bind b2) v2) (CHead d2 (Bind Void) v3)))))) (let H9 \def (eq_ind_r 
B b1 (\lambda (b: B).(not (eq B b Void))) H2 Void H7) in (let H10 \def (match 
(H9 (refl_equal B Void)) in False return (\lambda (_: False).(ex2_2 C T 
(\lambda (d2: C).(\lambda (_: T).(csubv c3 d2))) (\lambda (d2: C).(\lambda 
(v3: T).(clear (CHead c4 (Bind b2) v2) (CHead d2 (Bind Void) v3)))))) with 
[]) in H10)) d1 H8)))) H5)) H4)))))))))))))) (\lambda (c3: C).(\lambda (c4: 
C).(\lambda (_: (csubv c3 c4)).(\lambda (H1: ((\forall (d1: C).(\forall (v1: 
T).((clear c3 (CHead d1 (Bind Void) v1)) \to (ex2_2 C T (\lambda (d2: 
C).(\lambda (_: T).(csubv d1 d2))) (\lambda (d2: C).(\lambda (v2: T).(clear 
c4 (CHead d2 (Bind Void) v2)))))))))).(\lambda (f1: F).(\lambda (f2: 
F).(\lambda (v1: T).(\lambda (v2: T).(\lambda (d1: C).(\lambda (v0: 
T).(\lambda (H2: (clear (CHead c3 (Flat f1) v1) (CHead d1 (Bind Void) 
v0))).(let H_x \def (H1 d1 v0 (clear_gen_flat f1 c3 (CHead d1 (Bind Void) v0) 
v1 H2)) in (let H3 \def H_x in (ex2_2_ind C T (\lambda (d2: C).(\lambda (_: 
T).(csubv d1 d2))) (\lambda (d2: C).(\lambda (v3: T).(clear c4 (CHead d2 
(Bind Void) v3)))) (ex2_2 C T (\lambda (d2: C).(\lambda (_: T).(csubv d1 
d2))) (\lambda (d2: C).(\lambda (v3: T).(clear (CHead c4 (Flat f2) v2) (CHead 
d2 (Bind Void) v3))))) (\lambda (x0: C).(\lambda (x1: T).(\lambda (H4: (csubv 
d1 x0)).(\lambda (H5: (clear c4 (CHead x0 (Bind Void) x1))).(ex2_2_intro C T 
(\lambda (d2: C).(\lambda (_: T).(csubv d1 d2))) (\lambda (d2: C).(\lambda 
(v3: T).(clear (CHead c4 (Flat f2) v2) (CHead d2 (Bind Void) v3)))) x0 x1 H4 
(clear_flat c4 (CHead x0 (Bind Void) x1) H5 f2 v2)))))) H3)))))))))))))) c1 
c2 H))).
(* COMMENTS
Initial nodes: 1205
END *)

