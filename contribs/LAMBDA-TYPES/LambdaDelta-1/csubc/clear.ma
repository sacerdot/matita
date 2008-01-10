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



include "csubc/defs.ma".

theorem csubc_clear_conf:
 \forall (g: G).(\forall (c1: C).(\forall (e1: C).((clear c1 e1) \to (\forall 
(c2: C).((csubc g c1 c2) \to (ex2 C (\lambda (e2: C).(clear c2 e2)) (\lambda 
(e2: C).(csubc g e1 e2))))))))
\def
 \lambda (g: G).(\lambda (c1: C).(\lambda (e1: C).(\lambda (H: (clear c1 
e1)).(clear_ind (\lambda (c: C).(\lambda (c0: C).(\forall (c2: C).((csubc g c 
c2) \to (ex2 C (\lambda (e2: C).(clear c2 e2)) (\lambda (e2: C).(csubc g c0 
e2))))))) (\lambda (b: B).(\lambda (e: C).(\lambda (u: T).(\lambda (c2: 
C).(\lambda (H0: (csubc g (CHead e (Bind b) u) c2)).(let H1 \def (match H0 in 
csubc return (\lambda (c: C).(\lambda (c0: C).(\lambda (_: (csubc ? c 
c0)).((eq C c (CHead e (Bind b) u)) \to ((eq C c0 c2) \to (ex2 C (\lambda 
(e2: C).(clear c2 e2)) (\lambda (e2: C).(csubc g (CHead e (Bind b) u) 
e2)))))))) with [(csubc_sort n) \Rightarrow (\lambda (H1: (eq C (CSort n) 
(CHead e (Bind b) u))).(\lambda (H2: (eq C (CSort n) c2)).((let H3 \def 
(eq_ind C (CSort n) (\lambda (e0: C).(match e0 in C return (\lambda (_: 
C).Prop) with [(CSort _) \Rightarrow True | (CHead _ _ _) \Rightarrow 
False])) I (CHead e (Bind b) u) H1) in (False_ind ((eq C (CSort n) c2) \to 
(ex2 C (\lambda (e2: C).(clear c2 e2)) (\lambda (e2: C).(csubc g (CHead e 
(Bind b) u) e2)))) H3)) H2))) | (csubc_head c0 c3 H1 k v) \Rightarrow 
(\lambda (H2: (eq C (CHead c0 k v) (CHead e (Bind b) u))).(\lambda (H3: (eq C 
(CHead c3 k v) c2)).((let H4 \def (f_equal C T (\lambda (e0: C).(match e0 in 
C return (\lambda (_: C).T) with [(CSort _) \Rightarrow v | (CHead _ _ t) 
\Rightarrow t])) (CHead c0 k v) (CHead e (Bind b) u) H2) in ((let H5 \def 
(f_equal C K (\lambda (e0: C).(match e0 in C return (\lambda (_: C).K) with 
[(CSort _) \Rightarrow k | (CHead _ k0 _) \Rightarrow k0])) (CHead c0 k v) 
(CHead e (Bind b) u) H2) in ((let H6 \def (f_equal C C (\lambda (e0: 
C).(match e0 in C return (\lambda (_: C).C) with [(CSort _) \Rightarrow c0 | 
(CHead c _ _) \Rightarrow c])) (CHead c0 k v) (CHead e (Bind b) u) H2) in 
(eq_ind C e (\lambda (c: C).((eq K k (Bind b)) \to ((eq T v u) \to ((eq C 
(CHead c3 k v) c2) \to ((csubc g c c3) \to (ex2 C (\lambda (e2: C).(clear c2 
e2)) (\lambda (e2: C).(csubc g (CHead e (Bind b) u) e2)))))))) (\lambda (H7: 
(eq K k (Bind b))).(eq_ind K (Bind b) (\lambda (k0: K).((eq T v u) \to ((eq C 
(CHead c3 k0 v) c2) \to ((csubc g e c3) \to (ex2 C (\lambda (e2: C).(clear c2 
e2)) (\lambda (e2: C).(csubc g (CHead e (Bind b) u) e2))))))) (\lambda (H8: 
(eq T v u)).(eq_ind T u (\lambda (t: T).((eq C (CHead c3 (Bind b) t) c2) \to 
((csubc g e c3) \to (ex2 C (\lambda (e2: C).(clear c2 e2)) (\lambda (e2: 
C).(csubc g (CHead e (Bind b) u) e2)))))) (\lambda (H9: (eq C (CHead c3 (Bind 
b) u) c2)).(eq_ind C (CHead c3 (Bind b) u) (\lambda (c: C).((csubc g e c3) 
\to (ex2 C (\lambda (e2: C).(clear c e2)) (\lambda (e2: C).(csubc g (CHead e 
(Bind b) u) e2))))) (\lambda (H10: (csubc g e c3)).(ex_intro2 C (\lambda (e2: 
C).(clear (CHead c3 (Bind b) u) e2)) (\lambda (e2: C).(csubc g (CHead e (Bind 
b) u) e2)) (CHead c3 (Bind b) u) (clear_bind b c3 u) (csubc_head g e c3 H10 
(Bind b) u))) c2 H9)) v (sym_eq T v u H8))) k (sym_eq K k (Bind b) H7))) c0 
(sym_eq C c0 e H6))) H5)) H4)) H3 H1))) | (csubc_abst c0 c3 H1 v a H2 w H3) 
\Rightarrow (\lambda (H4: (eq C (CHead c0 (Bind Abst) v) (CHead e (Bind b) 
u))).(\lambda (H5: (eq C (CHead c3 (Bind Abbr) w) c2)).((let H6 \def (f_equal 
C T (\lambda (e0: C).(match e0 in C return (\lambda (_: C).T) with [(CSort _) 
\Rightarrow v | (CHead _ _ t) \Rightarrow t])) (CHead c0 (Bind Abst) v) 
(CHead e (Bind b) u) H4) in ((let H7 \def (f_equal C B (\lambda (e0: 
C).(match e0 in C return (\lambda (_: C).B) with [(CSort _) \Rightarrow Abst 
| (CHead _ k _) \Rightarrow (match k in K return (\lambda (_: K).B) with 
[(Bind b0) \Rightarrow b0 | (Flat _) \Rightarrow Abst])])) (CHead c0 (Bind 
Abst) v) (CHead e (Bind b) u) H4) in ((let H8 \def (f_equal C C (\lambda (e0: 
C).(match e0 in C return (\lambda (_: C).C) with [(CSort _) \Rightarrow c0 | 
(CHead c _ _) \Rightarrow c])) (CHead c0 (Bind Abst) v) (CHead e (Bind b) u) 
H4) in (eq_ind C e (\lambda (c: C).((eq B Abst b) \to ((eq T v u) \to ((eq C 
(CHead c3 (Bind Abbr) w) c2) \to ((csubc g c c3) \to ((sc3 g (asucc g a) c v) 
\to ((sc3 g a c3 w) \to (ex2 C (\lambda (e2: C).(clear c2 e2)) (\lambda (e2: 
C).(csubc g (CHead e (Bind b) u) e2)))))))))) (\lambda (H9: (eq B Abst 
b)).(eq_ind B Abst (\lambda (b0: B).((eq T v u) \to ((eq C (CHead c3 (Bind 
Abbr) w) c2) \to ((csubc g e c3) \to ((sc3 g (asucc g a) e v) \to ((sc3 g a 
c3 w) \to (ex2 C (\lambda (e2: C).(clear c2 e2)) (\lambda (e2: C).(csubc g 
(CHead e (Bind b0) u) e2))))))))) (\lambda (H10: (eq T v u)).(eq_ind T u 
(\lambda (t: T).((eq C (CHead c3 (Bind Abbr) w) c2) \to ((csubc g e c3) \to 
((sc3 g (asucc g a) e t) \to ((sc3 g a c3 w) \to (ex2 C (\lambda (e2: 
C).(clear c2 e2)) (\lambda (e2: C).(csubc g (CHead e (Bind Abst) u) 
e2)))))))) (\lambda (H11: (eq C (CHead c3 (Bind Abbr) w) c2)).(eq_ind C 
(CHead c3 (Bind Abbr) w) (\lambda (c: C).((csubc g e c3) \to ((sc3 g (asucc g 
a) e u) \to ((sc3 g a c3 w) \to (ex2 C (\lambda (e2: C).(clear c e2)) 
(\lambda (e2: C).(csubc g (CHead e (Bind Abst) u) e2))))))) (\lambda (H12: 
(csubc g e c3)).(\lambda (H13: (sc3 g (asucc g a) e u)).(\lambda (H14: (sc3 g 
a c3 w)).(ex_intro2 C (\lambda (e2: C).(clear (CHead c3 (Bind Abbr) w) e2)) 
(\lambda (e2: C).(csubc g (CHead e (Bind Abst) u) e2)) (CHead c3 (Bind Abbr) 
w) (clear_bind Abbr c3 w) (csubc_abst g e c3 H12 u a H13 w H14))))) c2 H11)) 
v (sym_eq T v u H10))) b H9)) c0 (sym_eq C c0 e H8))) H7)) H6)) H5 H1 H2 
H3)))]) in (H1 (refl_equal C (CHead e (Bind b) u)) (refl_equal C c2)))))))) 
(\lambda (e: C).(\lambda (c: C).(\lambda (_: (clear e c)).(\lambda (H1: 
((\forall (c2: C).((csubc g e c2) \to (ex2 C (\lambda (e2: C).(clear c2 e2)) 
(\lambda (e2: C).(csubc g c e2))))))).(\lambda (f: F).(\lambda (u: 
T).(\lambda (c2: C).(\lambda (H2: (csubc g (CHead e (Flat f) u) c2)).(let H3 
\def (match H2 in csubc return (\lambda (c0: C).(\lambda (c3: C).(\lambda (_: 
(csubc ? c0 c3)).((eq C c0 (CHead e (Flat f) u)) \to ((eq C c3 c2) \to (ex2 C 
(\lambda (e2: C).(clear c2 e2)) (\lambda (e2: C).(csubc g c e2)))))))) with 
[(csubc_sort n) \Rightarrow (\lambda (H3: (eq C (CSort n) (CHead e (Flat f) 
u))).(\lambda (H4: (eq C (CSort n) c2)).((let H5 \def (eq_ind C (CSort n) 
(\lambda (e0: C).(match e0 in C return (\lambda (_: C).Prop) with [(CSort _) 
\Rightarrow True | (CHead _ _ _) \Rightarrow False])) I (CHead e (Flat f) u) 
H3) in (False_ind ((eq C (CSort n) c2) \to (ex2 C (\lambda (e2: C).(clear c2 
e2)) (\lambda (e2: C).(csubc g c e2)))) H5)) H4))) | (csubc_head c0 c3 H3 k 
v) \Rightarrow (\lambda (H4: (eq C (CHead c0 k v) (CHead e (Flat f) 
u))).(\lambda (H5: (eq C (CHead c3 k v) c2)).((let H6 \def (f_equal C T 
(\lambda (e0: C).(match e0 in C return (\lambda (_: C).T) with [(CSort _) 
\Rightarrow v | (CHead _ _ t) \Rightarrow t])) (CHead c0 k v) (CHead e (Flat 
f) u) H4) in ((let H7 \def (f_equal C K (\lambda (e0: C).(match e0 in C 
return (\lambda (_: C).K) with [(CSort _) \Rightarrow k | (CHead _ k0 _) 
\Rightarrow k0])) (CHead c0 k v) (CHead e (Flat f) u) H4) in ((let H8 \def 
(f_equal C C (\lambda (e0: C).(match e0 in C return (\lambda (_: C).C) with 
[(CSort _) \Rightarrow c0 | (CHead c4 _ _) \Rightarrow c4])) (CHead c0 k v) 
(CHead e (Flat f) u) H4) in (eq_ind C e (\lambda (c4: C).((eq K k (Flat f)) 
\to ((eq T v u) \to ((eq C (CHead c3 k v) c2) \to ((csubc g c4 c3) \to (ex2 C 
(\lambda (e2: C).(clear c2 e2)) (\lambda (e2: C).(csubc g c e2)))))))) 
(\lambda (H9: (eq K k (Flat f))).(eq_ind K (Flat f) (\lambda (k0: K).((eq T v 
u) \to ((eq C (CHead c3 k0 v) c2) \to ((csubc g e c3) \to (ex2 C (\lambda 
(e2: C).(clear c2 e2)) (\lambda (e2: C).(csubc g c e2))))))) (\lambda (H10: 
(eq T v u)).(eq_ind T u (\lambda (t: T).((eq C (CHead c3 (Flat f) t) c2) \to 
((csubc g e c3) \to (ex2 C (\lambda (e2: C).(clear c2 e2)) (\lambda (e2: 
C).(csubc g c e2)))))) (\lambda (H11: (eq C (CHead c3 (Flat f) u) 
c2)).(eq_ind C (CHead c3 (Flat f) u) (\lambda (c4: C).((csubc g e c3) \to 
(ex2 C (\lambda (e2: C).(clear c4 e2)) (\lambda (e2: C).(csubc g c e2))))) 
(\lambda (H12: (csubc g e c3)).(let H_x \def (H1 c3 H12) in (let H13 \def H_x 
in (ex2_ind C (\lambda (e2: C).(clear c3 e2)) (\lambda (e2: C).(csubc g c 
e2)) (ex2 C (\lambda (e2: C).(clear (CHead c3 (Flat f) u) e2)) (\lambda (e2: 
C).(csubc g c e2))) (\lambda (x: C).(\lambda (H14: (clear c3 x)).(\lambda 
(H15: (csubc g c x)).(ex_intro2 C (\lambda (e2: C).(clear (CHead c3 (Flat f) 
u) e2)) (\lambda (e2: C).(csubc g c e2)) x (clear_flat c3 x H14 f u) H15)))) 
H13)))) c2 H11)) v (sym_eq T v u H10))) k (sym_eq K k (Flat f) H9))) c0 
(sym_eq C c0 e H8))) H7)) H6)) H5 H3))) | (csubc_abst c0 c3 H3 v a H4 w H5) 
\Rightarrow (\lambda (H6: (eq C (CHead c0 (Bind Abst) v) (CHead e (Flat f) 
u))).(\lambda (H7: (eq C (CHead c3 (Bind Abbr) w) c2)).((let H8 \def (eq_ind 
C (CHead c0 (Bind Abst) v) (\lambda (e0: C).(match e0 in C return (\lambda 
(_: C).Prop) with [(CSort _) \Rightarrow False | (CHead _ k _) \Rightarrow 
(match k in K return (\lambda (_: K).Prop) with [(Bind _) \Rightarrow True | 
(Flat _) \Rightarrow False])])) I (CHead e (Flat f) u) H6) in (False_ind ((eq 
C (CHead c3 (Bind Abbr) w) c2) \to ((csubc g c0 c3) \to ((sc3 g (asucc g a) 
c0 v) \to ((sc3 g a c3 w) \to (ex2 C (\lambda (e2: C).(clear c2 e2)) (\lambda 
(e2: C).(csubc g c e2))))))) H8)) H7 H3 H4 H5)))]) in (H3 (refl_equal C 
(CHead e (Flat f) u)) (refl_equal C c2))))))))))) c1 e1 H)))).

