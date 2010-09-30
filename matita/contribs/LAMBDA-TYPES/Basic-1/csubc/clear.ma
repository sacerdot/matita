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

include "Basic-1/csubc/fwd.ma".

theorem csubc_clear_conf:
 \forall (g: G).(\forall (c1: C).(\forall (e1: C).((clear c1 e1) \to (\forall 
(c2: C).((csubc g c1 c2) \to (ex2 C (\lambda (e2: C).(clear c2 e2)) (\lambda 
(e2: C).(csubc g e1 e2))))))))
\def
 \lambda (g: G).(\lambda (c1: C).(\lambda (e1: C).(\lambda (H: (clear c1 
e1)).(clear_ind (\lambda (c: C).(\lambda (c0: C).(\forall (c2: C).((csubc g c 
c2) \to (ex2 C (\lambda (e2: C).(clear c2 e2)) (\lambda (e2: C).(csubc g c0 
e2))))))) (\lambda (b: B).(\lambda (e: C).(\lambda (u: T).(\lambda (c2: 
C).(\lambda (H0: (csubc g (CHead e (Bind b) u) c2)).(let H_x \def 
(csubc_gen_head_l g e c2 u (Bind b) H0) in (let H1 \def H_x in (or3_ind (ex2 
C (\lambda (c3: C).(eq C c2 (CHead c3 (Bind b) u))) (\lambda (c3: C).(csubc g 
e c3))) (ex5_3 C T A (\lambda (_: C).(\lambda (_: T).(\lambda (_: A).(eq K 
(Bind b) (Bind Abst))))) (\lambda (c3: C).(\lambda (w: T).(\lambda (_: A).(eq 
C c2 (CHead c3 (Bind Abbr) w))))) (\lambda (c3: C).(\lambda (_: T).(\lambda 
(_: A).(csubc g e c3)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(sc3 
g (asucc g a) e u)))) (\lambda (c3: C).(\lambda (w: T).(\lambda (a: A).(sc3 g 
a c3 w))))) (ex4_3 B C T (\lambda (b0: B).(\lambda (c3: C).(\lambda (v2: 
T).(eq C c2 (CHead c3 (Bind b0) v2))))) (\lambda (_: B).(\lambda (_: 
C).(\lambda (_: T).(eq K (Bind b) (Bind Void))))) (\lambda (b0: B).(\lambda 
(_: C).(\lambda (_: T).(not (eq B b0 Void))))) (\lambda (_: B).(\lambda (c3: 
C).(\lambda (_: T).(csubc g e c3))))) (ex2 C (\lambda (e2: C).(clear c2 e2)) 
(\lambda (e2: C).(csubc g (CHead e (Bind b) u) e2))) (\lambda (H2: (ex2 C 
(\lambda (c3: C).(eq C c2 (CHead c3 (Bind b) u))) (\lambda (c3: C).(csubc g e 
c3)))).(ex2_ind C (\lambda (c3: C).(eq C c2 (CHead c3 (Bind b) u))) (\lambda 
(c3: C).(csubc g e c3)) (ex2 C (\lambda (e2: C).(clear c2 e2)) (\lambda (e2: 
C).(csubc g (CHead e (Bind b) u) e2))) (\lambda (x: C).(\lambda (H3: (eq C c2 
(CHead x (Bind b) u))).(\lambda (H4: (csubc g e x)).(eq_ind_r C (CHead x 
(Bind b) u) (\lambda (c: C).(ex2 C (\lambda (e2: C).(clear c e2)) (\lambda 
(e2: C).(csubc g (CHead e (Bind b) u) e2)))) (ex_intro2 C (\lambda (e2: 
C).(clear (CHead x (Bind b) u) e2)) (\lambda (e2: C).(csubc g (CHead e (Bind 
b) u) e2)) (CHead x (Bind b) u) (clear_bind b x u) (csubc_head g e x H4 (Bind 
b) u)) c2 H3)))) H2)) (\lambda (H2: (ex5_3 C T A (\lambda (_: C).(\lambda (_: 
T).(\lambda (_: A).(eq K (Bind b) (Bind Abst))))) (\lambda (c3: C).(\lambda 
(w: T).(\lambda (_: A).(eq C c2 (CHead c3 (Bind Abbr) w))))) (\lambda (c3: 
C).(\lambda (_: T).(\lambda (_: A).(csubc g e c3)))) (\lambda (_: C).(\lambda 
(_: T).(\lambda (a: A).(sc3 g (asucc g a) e u)))) (\lambda (c3: C).(\lambda 
(w: T).(\lambda (a: A).(sc3 g a c3 w)))))).(ex5_3_ind C T A (\lambda (_: 
C).(\lambda (_: T).(\lambda (_: A).(eq K (Bind b) (Bind Abst))))) (\lambda 
(c3: C).(\lambda (w: T).(\lambda (_: A).(eq C c2 (CHead c3 (Bind Abbr) w))))) 
(\lambda (c3: C).(\lambda (_: T).(\lambda (_: A).(csubc g e c3)))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(sc3 g (asucc g a) e u)))) (\lambda 
(c3: C).(\lambda (w: T).(\lambda (a: A).(sc3 g a c3 w)))) (ex2 C (\lambda 
(e2: C).(clear c2 e2)) (\lambda (e2: C).(csubc g (CHead e (Bind b) u) e2))) 
(\lambda (x0: C).(\lambda (x1: T).(\lambda (x2: A).(\lambda (H3: (eq K (Bind 
b) (Bind Abst))).(\lambda (H4: (eq C c2 (CHead x0 (Bind Abbr) x1))).(\lambda 
(H5: (csubc g e x0)).(\lambda (H6: (sc3 g (asucc g x2) e u)).(\lambda (H7: 
(sc3 g x2 x0 x1)).(eq_ind_r C (CHead x0 (Bind Abbr) x1) (\lambda (c: C).(ex2 
C (\lambda (e2: C).(clear c e2)) (\lambda (e2: C).(csubc g (CHead e (Bind b) 
u) e2)))) (let H8 \def (f_equal K B (\lambda (e0: K).(match e0 in K return 
(\lambda (_: K).B) with [(Bind b0) \Rightarrow b0 | (Flat _) \Rightarrow b])) 
(Bind b) (Bind Abst) H3) in (eq_ind_r B Abst (\lambda (b0: B).(ex2 C (\lambda 
(e2: C).(clear (CHead x0 (Bind Abbr) x1) e2)) (\lambda (e2: C).(csubc g 
(CHead e (Bind b0) u) e2)))) (ex_intro2 C (\lambda (e2: C).(clear (CHead x0 
(Bind Abbr) x1) e2)) (\lambda (e2: C).(csubc g (CHead e (Bind Abst) u) e2)) 
(CHead x0 (Bind Abbr) x1) (clear_bind Abbr x0 x1) (csubc_abst g e x0 H5 u x2 
H6 x1 H7)) b H8)) c2 H4))))))))) H2)) (\lambda (H2: (ex4_3 B C T (\lambda 
(b0: B).(\lambda (c3: C).(\lambda (v2: T).(eq C c2 (CHead c3 (Bind b0) 
v2))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: T).(eq K (Bind b) (Bind 
Void))))) (\lambda (b0: B).(\lambda (_: C).(\lambda (_: T).(not (eq B b0 
Void))))) (\lambda (_: B).(\lambda (c3: C).(\lambda (_: T).(csubc g e 
c3)))))).(ex4_3_ind B C T (\lambda (b0: B).(\lambda (c3: C).(\lambda (v2: 
T).(eq C c2 (CHead c3 (Bind b0) v2))))) (\lambda (_: B).(\lambda (_: 
C).(\lambda (_: T).(eq K (Bind b) (Bind Void))))) (\lambda (b0: B).(\lambda 
(_: C).(\lambda (_: T).(not (eq B b0 Void))))) (\lambda (_: B).(\lambda (c3: 
C).(\lambda (_: T).(csubc g e c3)))) (ex2 C (\lambda (e2: C).(clear c2 e2)) 
(\lambda (e2: C).(csubc g (CHead e (Bind b) u) e2))) (\lambda (x0: 
B).(\lambda (x1: C).(\lambda (x2: T).(\lambda (H3: (eq C c2 (CHead x1 (Bind 
x0) x2))).(\lambda (H4: (eq K (Bind b) (Bind Void))).(\lambda (H5: (not (eq B 
x0 Void))).(\lambda (H6: (csubc g e x1)).(eq_ind_r C (CHead x1 (Bind x0) x2) 
(\lambda (c: C).(ex2 C (\lambda (e2: C).(clear c e2)) (\lambda (e2: C).(csubc 
g (CHead e (Bind b) u) e2)))) (let H7 \def (f_equal K B (\lambda (e0: 
K).(match e0 in K return (\lambda (_: K).B) with [(Bind b0) \Rightarrow b0 | 
(Flat _) \Rightarrow b])) (Bind b) (Bind Void) H4) in (eq_ind_r B Void 
(\lambda (b0: B).(ex2 C (\lambda (e2: C).(clear (CHead x1 (Bind x0) x2) e2)) 
(\lambda (e2: C).(csubc g (CHead e (Bind b0) u) e2)))) (ex_intro2 C (\lambda 
(e2: C).(clear (CHead x1 (Bind x0) x2) e2)) (\lambda (e2: C).(csubc g (CHead 
e (Bind Void) u) e2)) (CHead x1 (Bind x0) x2) (clear_bind x0 x1 x2) 
(csubc_void g e x1 H6 x0 H5 u x2)) b H7)) c2 H3)))))))) H2)) H1)))))))) 
(\lambda (e: C).(\lambda (c: C).(\lambda (_: (clear e c)).(\lambda (H1: 
((\forall (c2: C).((csubc g e c2) \to (ex2 C (\lambda (e2: C).(clear c2 e2)) 
(\lambda (e2: C).(csubc g c e2))))))).(\lambda (f: F).(\lambda (u: 
T).(\lambda (c2: C).(\lambda (H2: (csubc g (CHead e (Flat f) u) c2)).(let H_x 
\def (csubc_gen_head_l g e c2 u (Flat f) H2) in (let H3 \def H_x in (or3_ind 
(ex2 C (\lambda (c3: C).(eq C c2 (CHead c3 (Flat f) u))) (\lambda (c3: 
C).(csubc g e c3))) (ex5_3 C T A (\lambda (_: C).(\lambda (_: T).(\lambda (_: 
A).(eq K (Flat f) (Bind Abst))))) (\lambda (c3: C).(\lambda (w: T).(\lambda 
(_: A).(eq C c2 (CHead c3 (Bind Abbr) w))))) (\lambda (c3: C).(\lambda (_: 
T).(\lambda (_: A).(csubc g e c3)))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(sc3 g (asucc g a) e u)))) (\lambda (c3: C).(\lambda (w: T).(\lambda 
(a: A).(sc3 g a c3 w))))) (ex4_3 B C T (\lambda (b: B).(\lambda (c3: 
C).(\lambda (v2: T).(eq C c2 (CHead c3 (Bind b) v2))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (_: T).(eq K (Flat f) (Bind Void))))) (\lambda 
(b: B).(\lambda (_: C).(\lambda (_: T).(not (eq B b Void))))) (\lambda (_: 
B).(\lambda (c3: C).(\lambda (_: T).(csubc g e c3))))) (ex2 C (\lambda (e2: 
C).(clear c2 e2)) (\lambda (e2: C).(csubc g c e2))) (\lambda (H4: (ex2 C 
(\lambda (c3: C).(eq C c2 (CHead c3 (Flat f) u))) (\lambda (c3: C).(csubc g e 
c3)))).(ex2_ind C (\lambda (c3: C).(eq C c2 (CHead c3 (Flat f) u))) (\lambda 
(c3: C).(csubc g e c3)) (ex2 C (\lambda (e2: C).(clear c2 e2)) (\lambda (e2: 
C).(csubc g c e2))) (\lambda (x: C).(\lambda (H5: (eq C c2 (CHead x (Flat f) 
u))).(\lambda (H6: (csubc g e x)).(eq_ind_r C (CHead x (Flat f) u) (\lambda 
(c0: C).(ex2 C (\lambda (e2: C).(clear c0 e2)) (\lambda (e2: C).(csubc g c 
e2)))) (let H_x0 \def (H1 x H6) in (let H7 \def H_x0 in (ex2_ind C (\lambda 
(e2: C).(clear x e2)) (\lambda (e2: C).(csubc g c e2)) (ex2 C (\lambda (e2: 
C).(clear (CHead x (Flat f) u) e2)) (\lambda (e2: C).(csubc g c e2))) 
(\lambda (x0: C).(\lambda (H8: (clear x x0)).(\lambda (H9: (csubc g c 
x0)).(ex_intro2 C (\lambda (e2: C).(clear (CHead x (Flat f) u) e2)) (\lambda 
(e2: C).(csubc g c e2)) x0 (clear_flat x x0 H8 f u) H9)))) H7))) c2 H5)))) 
H4)) (\lambda (H4: (ex5_3 C T A (\lambda (_: C).(\lambda (_: T).(\lambda (_: 
A).(eq K (Flat f) (Bind Abst))))) (\lambda (c3: C).(\lambda (w: T).(\lambda 
(_: A).(eq C c2 (CHead c3 (Bind Abbr) w))))) (\lambda (c3: C).(\lambda (_: 
T).(\lambda (_: A).(csubc g e c3)))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(sc3 g (asucc g a) e u)))) (\lambda (c3: C).(\lambda (w: T).(\lambda 
(a: A).(sc3 g a c3 w)))))).(ex5_3_ind C T A (\lambda (_: C).(\lambda (_: 
T).(\lambda (_: A).(eq K (Flat f) (Bind Abst))))) (\lambda (c3: C).(\lambda 
(w: T).(\lambda (_: A).(eq C c2 (CHead c3 (Bind Abbr) w))))) (\lambda (c3: 
C).(\lambda (_: T).(\lambda (_: A).(csubc g e c3)))) (\lambda (_: C).(\lambda 
(_: T).(\lambda (a: A).(sc3 g (asucc g a) e u)))) (\lambda (c3: C).(\lambda 
(w: T).(\lambda (a: A).(sc3 g a c3 w)))) (ex2 C (\lambda (e2: C).(clear c2 
e2)) (\lambda (e2: C).(csubc g c e2))) (\lambda (x0: C).(\lambda (x1: 
T).(\lambda (x2: A).(\lambda (H5: (eq K (Flat f) (Bind Abst))).(\lambda (H6: 
(eq C c2 (CHead x0 (Bind Abbr) x1))).(\lambda (_: (csubc g e x0)).(\lambda 
(_: (sc3 g (asucc g x2) e u)).(\lambda (_: (sc3 g x2 x0 x1)).(eq_ind_r C 
(CHead x0 (Bind Abbr) x1) (\lambda (c0: C).(ex2 C (\lambda (e2: C).(clear c0 
e2)) (\lambda (e2: C).(csubc g c e2)))) (let H10 \def (eq_ind K (Flat f) 
(\lambda (ee: K).(match ee in K return (\lambda (_: K).Prop) with [(Bind _) 
\Rightarrow False | (Flat _) \Rightarrow True])) I (Bind Abst) H5) in 
(False_ind (ex2 C (\lambda (e2: C).(clear (CHead x0 (Bind Abbr) x1) e2)) 
(\lambda (e2: C).(csubc g c e2))) H10)) c2 H6))))))))) H4)) (\lambda (H4: 
(ex4_3 B C T (\lambda (b: B).(\lambda (c3: C).(\lambda (v2: T).(eq C c2 
(CHead c3 (Bind b) v2))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: 
T).(eq K (Flat f) (Bind Void))))) (\lambda (b: B).(\lambda (_: C).(\lambda 
(_: T).(not (eq B b Void))))) (\lambda (_: B).(\lambda (c3: C).(\lambda (_: 
T).(csubc g e c3)))))).(ex4_3_ind B C T (\lambda (b: B).(\lambda (c3: 
C).(\lambda (v2: T).(eq C c2 (CHead c3 (Bind b) v2))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (_: T).(eq K (Flat f) (Bind Void))))) (\lambda 
(b: B).(\lambda (_: C).(\lambda (_: T).(not (eq B b Void))))) (\lambda (_: 
B).(\lambda (c3: C).(\lambda (_: T).(csubc g e c3)))) (ex2 C (\lambda (e2: 
C).(clear c2 e2)) (\lambda (e2: C).(csubc g c e2))) (\lambda (x0: B).(\lambda 
(x1: C).(\lambda (x2: T).(\lambda (H5: (eq C c2 (CHead x1 (Bind x0) 
x2))).(\lambda (H6: (eq K (Flat f) (Bind Void))).(\lambda (_: (not (eq B x0 
Void))).(\lambda (_: (csubc g e x1)).(eq_ind_r C (CHead x1 (Bind x0) x2) 
(\lambda (c0: C).(ex2 C (\lambda (e2: C).(clear c0 e2)) (\lambda (e2: 
C).(csubc g c e2)))) (let H9 \def (eq_ind K (Flat f) (\lambda (ee: K).(match 
ee in K return (\lambda (_: K).Prop) with [(Bind _) \Rightarrow False | (Flat 
_) \Rightarrow True])) I (Bind Void) H6) in (False_ind (ex2 C (\lambda (e2: 
C).(clear (CHead x1 (Bind x0) x2) e2)) (\lambda (e2: C).(csubc g c e2))) H9)) 
c2 H5)))))))) H4)) H3))))))))))) c1 e1 H)))).
(* COMMENTS
Initial nodes: 2837
END *)

