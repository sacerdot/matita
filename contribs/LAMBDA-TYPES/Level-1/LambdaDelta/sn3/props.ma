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

set "baseuri" "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/sn3/props".

include "sn3/nf2.ma".

include "sn3/fwd.ma".

include "nf2/iso.ma".

include "pr3/iso.ma".

include "iso/props.ma".

theorem sn3_pr3_trans:
 \forall (c: C).(\forall (t1: T).((sn3 c t1) \to (\forall (t2: T).((pr3 c t1 
t2) \to (sn3 c t2)))))
\def
 \lambda (c: C).(\lambda (t1: T).(\lambda (H: (sn3 c t1)).(sn3_ind c (\lambda 
(t: T).(\forall (t2: T).((pr3 c t t2) \to (sn3 c t2)))) (\lambda (t2: 
T).(\lambda (H0: ((\forall (t3: T).((((eq T t2 t3) \to (\forall (P: 
Prop).P))) \to ((pr3 c t2 t3) \to (sn3 c t3)))))).(\lambda (H1: ((\forall 
(t3: T).((((eq T t2 t3) \to (\forall (P: Prop).P))) \to ((pr3 c t2 t3) \to 
(\forall (t4: T).((pr3 c t3 t4) \to (sn3 c t4)))))))).(\lambda (t3: 
T).(\lambda (H2: (pr3 c t2 t3)).(sn3_sing c t3 (\lambda (t0: T).(\lambda (H3: 
(((eq T t3 t0) \to (\forall (P: Prop).P)))).(\lambda (H4: (pr3 c t3 t0)).(let 
H_x \def (term_dec t2 t3) in (let H5 \def H_x in (or_ind (eq T t2 t3) ((eq T 
t2 t3) \to (\forall (P: Prop).P)) (sn3 c t0) (\lambda (H6: (eq T t2 t3)).(let 
H7 \def (eq_ind_r T t3 (\lambda (t: T).(pr3 c t t0)) H4 t2 H6) in (let H8 
\def (eq_ind_r T t3 (\lambda (t: T).((eq T t t0) \to (\forall (P: Prop).P))) 
H3 t2 H6) in (let H9 \def (eq_ind_r T t3 (\lambda (t: T).(pr3 c t2 t)) H2 t2 
H6) in (H0 t0 H8 H7))))) (\lambda (H6: (((eq T t2 t3) \to (\forall (P: 
Prop).P)))).(H1 t3 H6 H2 t0 H4)) H5)))))))))))) t1 H))).

theorem sn3_pr2_intro:
 \forall (c: C).(\forall (t1: T).(((\forall (t2: T).((((eq T t1 t2) \to 
(\forall (P: Prop).P))) \to ((pr2 c t1 t2) \to (sn3 c t2))))) \to (sn3 c t1)))
\def
 \lambda (c: C).(\lambda (t1: T).(\lambda (H: ((\forall (t2: T).((((eq T t1 
t2) \to (\forall (P: Prop).P))) \to ((pr2 c t1 t2) \to (sn3 c 
t2)))))).(sn3_sing c t1 (\lambda (t2: T).(\lambda (H0: (((eq T t1 t2) \to 
(\forall (P: Prop).P)))).(\lambda (H1: (pr3 c t1 t2)).(let H2 \def H0 in 
((let H3 \def H in (pr3_ind c (\lambda (t: T).(\lambda (t0: T).(((\forall 
(t3: T).((((eq T t t3) \to (\forall (P: Prop).P))) \to ((pr2 c t t3) \to (sn3 
c t3))))) \to ((((eq T t t0) \to (\forall (P: Prop).P))) \to (sn3 c t0))))) 
(\lambda (t: T).(\lambda (H4: ((\forall (t3: T).((((eq T t t3) \to (\forall 
(P: Prop).P))) \to ((pr2 c t t3) \to (sn3 c t3)))))).(\lambda (H5: (((eq T t 
t) \to (\forall (P: Prop).P)))).(H4 t H5 (pr2_free c t t (pr0_refl t)))))) 
(\lambda (t3: T).(\lambda (t4: T).(\lambda (H4: (pr2 c t4 t3)).(\lambda (t5: 
T).(\lambda (H5: (pr3 c t3 t5)).(\lambda (H6: ((((\forall (t6: T).((((eq T t3 
t6) \to (\forall (P: Prop).P))) \to ((pr2 c t3 t6) \to (sn3 c t6))))) \to 
((((eq T t3 t5) \to (\forall (P: Prop).P))) \to (sn3 c t5))))).(\lambda (H7: 
((\forall (t6: T).((((eq T t4 t6) \to (\forall (P: Prop).P))) \to ((pr2 c t4 
t6) \to (sn3 c t6)))))).(\lambda (H8: (((eq T t4 t5) \to (\forall (P: 
Prop).P)))).(let H_x \def (term_dec t4 t3) in (let H9 \def H_x in (or_ind (eq 
T t4 t3) ((eq T t4 t3) \to (\forall (P: Prop).P)) (sn3 c t5) (\lambda (H10: 
(eq T t4 t3)).(let H11 \def (eq_ind T t4 (\lambda (t: T).((eq T t t5) \to 
(\forall (P: Prop).P))) H8 t3 H10) in (let H12 \def (eq_ind T t4 (\lambda (t: 
T).(\forall (t6: T).((((eq T t t6) \to (\forall (P: Prop).P))) \to ((pr2 c t 
t6) \to (sn3 c t6))))) H7 t3 H10) in (let H13 \def (eq_ind T t4 (\lambda (t: 
T).(pr2 c t t3)) H4 t3 H10) in (H6 H12 H11))))) (\lambda (H10: (((eq T t4 t3) 
\to (\forall (P: Prop).P)))).(sn3_pr3_trans c t3 (H7 t3 H10 H4) t5 H5)) 
H9))))))))))) t1 t2 H1 H3)) H2)))))))).

theorem sn3_cast:
 \forall (c: C).(\forall (u: T).((sn3 c u) \to (\forall (t: T).((sn3 c t) \to 
(sn3 c (THead (Flat Cast) u t))))))
\def
 \lambda (c: C).(\lambda (u: T).(\lambda (H: (sn3 c u)).(sn3_ind c (\lambda 
(t: T).(\forall (t0: T).((sn3 c t0) \to (sn3 c (THead (Flat Cast) t t0))))) 
(\lambda (t1: T).(\lambda (_: ((\forall (t2: T).((((eq T t1 t2) \to (\forall 
(P: Prop).P))) \to ((pr3 c t1 t2) \to (sn3 c t2)))))).(\lambda (H1: ((\forall 
(t2: T).((((eq T t1 t2) \to (\forall (P: Prop).P))) \to ((pr3 c t1 t2) \to 
(\forall (t: T).((sn3 c t) \to (sn3 c (THead (Flat Cast) t2 
t))))))))).(\lambda (t: T).(\lambda (H2: (sn3 c t)).(sn3_ind c (\lambda (t0: 
T).(sn3 c (THead (Flat Cast) t1 t0))) (\lambda (t0: T).(\lambda (H3: 
((\forall (t2: T).((((eq T t0 t2) \to (\forall (P: Prop).P))) \to ((pr3 c t0 
t2) \to (sn3 c t2)))))).(\lambda (H4: ((\forall (t2: T).((((eq T t0 t2) \to 
(\forall (P: Prop).P))) \to ((pr3 c t0 t2) \to (sn3 c (THead (Flat Cast) t1 
t2))))))).(sn3_pr2_intro c (THead (Flat Cast) t1 t0) (\lambda (t2: 
T).(\lambda (H5: (((eq T (THead (Flat Cast) t1 t0) t2) \to (\forall (P: 
Prop).P)))).(\lambda (H6: (pr2 c (THead (Flat Cast) t1 t0) t2)).(let H7 \def 
(pr2_gen_cast c t1 t0 t2 H6) in (or_ind (ex3_2 T T (\lambda (u2: T).(\lambda 
(t3: T).(eq T t2 (THead (Flat Cast) u2 t3)))) (\lambda (u2: T).(\lambda (_: 
T).(pr2 c t1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c t0 t3)))) (pr2 c 
t0 t2) (sn3 c t2) (\lambda (H8: (ex3_2 T T (\lambda (u2: T).(\lambda (t3: 
T).(eq T t2 (THead (Flat Cast) u2 t3)))) (\lambda (u2: T).(\lambda (_: 
T).(pr2 c t1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c t0 
t3))))).(ex3_2_ind T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead 
(Flat Cast) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c t1 u2))) 
(\lambda (_: T).(\lambda (t3: T).(pr2 c t0 t3))) (sn3 c t2) (\lambda (x0: 
T).(\lambda (x1: T).(\lambda (H9: (eq T t2 (THead (Flat Cast) x0 
x1))).(\lambda (H10: (pr2 c t1 x0)).(\lambda (H11: (pr2 c t0 x1)).(let H12 
\def (eq_ind T t2 (\lambda (t3: T).((eq T (THead (Flat Cast) t1 t0) t3) \to 
(\forall (P: Prop).P))) H5 (THead (Flat Cast) x0 x1) H9) in (eq_ind_r T 
(THead (Flat Cast) x0 x1) (\lambda (t3: T).(sn3 c t3)) (let H_x \def 
(term_dec x0 t1) in (let H13 \def H_x in (or_ind (eq T x0 t1) ((eq T x0 t1) 
\to (\forall (P: Prop).P)) (sn3 c (THead (Flat Cast) x0 x1)) (\lambda (H14: 
(eq T x0 t1)).(let H15 \def (eq_ind T x0 (\lambda (t3: T).((eq T (THead (Flat 
Cast) t1 t0) (THead (Flat Cast) t3 x1)) \to (\forall (P: Prop).P))) H12 t1 
H14) in (let H16 \def (eq_ind T x0 (\lambda (t3: T).(pr2 c t1 t3)) H10 t1 
H14) in (eq_ind_r T t1 (\lambda (t3: T).(sn3 c (THead (Flat Cast) t3 x1))) 
(let H_x0 \def (term_dec t0 x1) in (let H17 \def H_x0 in (or_ind (eq T t0 x1) 
((eq T t0 x1) \to (\forall (P: Prop).P)) (sn3 c (THead (Flat Cast) t1 x1)) 
(\lambda (H18: (eq T t0 x1)).(let H19 \def (eq_ind_r T x1 (\lambda (t3: 
T).((eq T (THead (Flat Cast) t1 t0) (THead (Flat Cast) t1 t3)) \to (\forall 
(P: Prop).P))) H15 t0 H18) in (let H20 \def (eq_ind_r T x1 (\lambda (t3: 
T).(pr2 c t0 t3)) H11 t0 H18) in (eq_ind T t0 (\lambda (t3: T).(sn3 c (THead 
(Flat Cast) t1 t3))) (H19 (refl_equal T (THead (Flat Cast) t1 t0)) (sn3 c 
(THead (Flat Cast) t1 t0))) x1 H18)))) (\lambda (H18: (((eq T t0 x1) \to 
(\forall (P: Prop).P)))).(H4 x1 H18 (pr3_pr2 c t0 x1 H11))) H17))) x0 H14)))) 
(\lambda (H14: (((eq T x0 t1) \to (\forall (P: Prop).P)))).(H1 x0 (\lambda 
(H15: (eq T t1 x0)).(\lambda (P: Prop).(let H16 \def (eq_ind_r T x0 (\lambda 
(t3: T).((eq T t3 t1) \to (\forall (P0: Prop).P0))) H14 t1 H15) in (let H17 
\def (eq_ind_r T x0 (\lambda (t3: T).((eq T (THead (Flat Cast) t1 t0) (THead 
(Flat Cast) t3 x1)) \to (\forall (P0: Prop).P0))) H12 t1 H15) in (let H18 
\def (eq_ind_r T x0 (\lambda (t3: T).(pr2 c t1 t3)) H10 t1 H15) in (H16 
(refl_equal T t1) P)))))) (pr3_pr2 c t1 x0 H10) x1 (let H_x0 \def (term_dec 
t0 x1) in (let H15 \def H_x0 in (or_ind (eq T t0 x1) ((eq T t0 x1) \to 
(\forall (P: Prop).P)) (sn3 c x1) (\lambda (H16: (eq T t0 x1)).(let H17 \def 
(eq_ind_r T x1 (\lambda (t3: T).((eq T (THead (Flat Cast) t1 t0) (THead (Flat 
Cast) x0 t3)) \to (\forall (P: Prop).P))) H12 t0 H16) in (let H18 \def 
(eq_ind_r T x1 (\lambda (t3: T).(pr2 c t0 t3)) H11 t0 H16) in (eq_ind T t0 
(\lambda (t3: T).(sn3 c t3)) (sn3_sing c t0 H3) x1 H16)))) (\lambda (H16: 
(((eq T t0 x1) \to (\forall (P: Prop).P)))).(H3 x1 H16 (pr3_pr2 c t0 x1 
H11))) H15))))) H13))) t2 H9))))))) H8)) (\lambda (H8: (pr2 c t0 
t2)).(sn3_pr3_trans c t0 (sn3_sing c t0 H3) t2 (pr3_pr2 c t0 t2 H8))) 
H7))))))))) t H2)))))) u H))).

theorem sn3_appl_lref:
 \forall (c: C).(\forall (i: nat).((nf2 c (TLRef i)) \to (\forall (v: 
T).((sn3 c v) \to (sn3 c (THead (Flat Appl) v (TLRef i)))))))
\def
 \lambda (c: C).(\lambda (i: nat).(\lambda (H: (nf2 c (TLRef i))).(\lambda 
(v: T).(\lambda (H0: (sn3 c v)).(sn3_ind c (\lambda (t: T).(sn3 c (THead 
(Flat Appl) t (TLRef i)))) (\lambda (t1: T).(\lambda (_: ((\forall (t2: 
T).((((eq T t1 t2) \to (\forall (P: Prop).P))) \to ((pr3 c t1 t2) \to (sn3 c 
t2)))))).(\lambda (H2: ((\forall (t2: T).((((eq T t1 t2) \to (\forall (P: 
Prop).P))) \to ((pr3 c t1 t2) \to (sn3 c (THead (Flat Appl) t2 (TLRef 
i)))))))).(sn3_pr2_intro c (THead (Flat Appl) t1 (TLRef i)) (\lambda (t2: 
T).(\lambda (H3: (((eq T (THead (Flat Appl) t1 (TLRef i)) t2) \to (\forall 
(P: Prop).P)))).(\lambda (H4: (pr2 c (THead (Flat Appl) t1 (TLRef i)) 
t2)).(let H5 \def (pr2_gen_appl c t1 (TLRef i) t2 H4) in (or3_ind (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Flat Appl) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c t1 u2))) (\lambda (_: T).(\lambda 
(t3: T).(pr2 c (TLRef i) t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (TLRef i) (THead (Bind Abst) y1 
z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: 
T).(eq T t2 (THead (Bind Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c t1 u2))))) (\lambda (_: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall 
(u: T).(pr2 (CHead c (Bind b) u) z1 t3)))))))) (ex6_6 B T T T T T (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T 
(TLRef i) (THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T 
t2 (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) 
(\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr2 c t1 u2))))))) (\lambda (_: B).(\lambda (y1: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 
y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b) y2) z1 z2)))))))) 
(sn3 c t2) (\lambda (H6: (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T 
t2 (THead (Flat Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c t1 
u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c (TLRef i) t3))))).(ex3_2_ind T 
T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Flat Appl) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c t1 u2))) (\lambda (_: T).(\lambda 
(t3: T).(pr2 c (TLRef i) t3))) (sn3 c t2) (\lambda (x0: T).(\lambda (x1: 
T).(\lambda (H7: (eq T t2 (THead (Flat Appl) x0 x1))).(\lambda (H8: (pr2 c t1 
x0)).(\lambda (H9: (pr2 c (TLRef i) x1)).(let H10 \def (eq_ind T t2 (\lambda 
(t: T).((eq T (THead (Flat Appl) t1 (TLRef i)) t) \to (\forall (P: Prop).P))) 
H3 (THead (Flat Appl) x0 x1) H7) in (eq_ind_r T (THead (Flat Appl) x0 x1) 
(\lambda (t: T).(sn3 c t)) (let H11 \def (eq_ind_r T x1 (\lambda (t: T).((eq 
T (THead (Flat Appl) t1 (TLRef i)) (THead (Flat Appl) x0 t)) \to (\forall (P: 
Prop).P))) H10 (TLRef i) (H x1 H9)) in (let H12 \def (eq_ind_r T x1 (\lambda 
(t: T).(pr2 c (TLRef i) t)) H9 (TLRef i) (H x1 H9)) in (eq_ind T (TLRef i) 
(\lambda (t: T).(sn3 c (THead (Flat Appl) x0 t))) (let H_x \def (term_dec t1 
x0) in (let H13 \def H_x in (or_ind (eq T t1 x0) ((eq T t1 x0) \to (\forall 
(P: Prop).P)) (sn3 c (THead (Flat Appl) x0 (TLRef i))) (\lambda (H14: (eq T 
t1 x0)).(let H15 \def (eq_ind_r T x0 (\lambda (t: T).((eq T (THead (Flat 
Appl) t1 (TLRef i)) (THead (Flat Appl) t (TLRef i))) \to (\forall (P: 
Prop).P))) H11 t1 H14) in (let H16 \def (eq_ind_r T x0 (\lambda (t: T).(pr2 c 
t1 t)) H8 t1 H14) in (eq_ind T t1 (\lambda (t: T).(sn3 c (THead (Flat Appl) t 
(TLRef i)))) (H15 (refl_equal T (THead (Flat Appl) t1 (TLRef i))) (sn3 c 
(THead (Flat Appl) t1 (TLRef i)))) x0 H14)))) (\lambda (H14: (((eq T t1 x0) 
\to (\forall (P: Prop).P)))).(H2 x0 H14 (pr3_pr2 c t1 x0 H8))) H13))) x1 (H 
x1 H9)))) t2 H7))))))) H6)) (\lambda (H6: (ex4_4 T T T T (\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T (TLRef i) (THead 
(Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (t3: T).(eq T t2 (THead (Bind Abbr) u2 t3)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c t1 u2))))) 
(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: T).(\forall 
(b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) z1 t3))))))))).(ex4_4_ind T 
T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T 
(TLRef i) (THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind Abbr) u2 t3)))))) 
(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c t1 
u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: 
T).(\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) z1 t3))))))) 
(sn3 c t2) (\lambda (x0: T).(\lambda (x1: T).(\lambda (x2: T).(\lambda (x3: 
T).(\lambda (H7: (eq T (TLRef i) (THead (Bind Abst) x0 x1))).(\lambda (H8: 
(eq T t2 (THead (Bind Abbr) x2 x3))).(\lambda (_: (pr2 c t1 x2)).(\lambda (_: 
((\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) x1 x3))))).(let 
H11 \def (eq_ind T t2 (\lambda (t: T).((eq T (THead (Flat Appl) t1 (TLRef i)) 
t) \to (\forall (P: Prop).P))) H3 (THead (Bind Abbr) x2 x3) H8) in (eq_ind_r 
T (THead (Bind Abbr) x2 x3) (\lambda (t: T).(sn3 c t)) (let H12 \def (eq_ind 
T (TLRef i) (\lambda (ee: T).(match ee in T return (\lambda (_: T).Prop) with 
[(TSort _) \Rightarrow False | (TLRef _) \Rightarrow True | (THead _ _ _) 
\Rightarrow False])) I (THead (Bind Abst) x0 x1) H7) in (False_ind (sn3 c 
(THead (Bind Abbr) x2 x3)) H12)) t2 H8)))))))))) H6)) (\lambda (H6: (ex6_6 B 
T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(eq T (TLRef i) (THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda 
(_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq 
T t2 (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) 
(\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr2 c t1 u2))))))) (\lambda (_: B).(\lambda (y1: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 
y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b) y2) z1 
z2))))))))).(ex6_6_ind B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b 
Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (TLRef i) (THead (Bind b) y1 
z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: 
T).(\lambda (u2: T).(\lambda (y2: T).(eq T t2 (THead (Bind b) y2 (THead (Flat 
Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c t1 u2))))))) 
(\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (y2: T).(pr2 c y1 y2))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 
(CHead c (Bind b) y2) z1 z2))))))) (sn3 c t2) (\lambda (x0: B).(\lambda (x1: 
T).(\lambda (x2: T).(\lambda (x3: T).(\lambda (x4: T).(\lambda (x5: 
T).(\lambda (_: (not (eq B x0 Abst))).(\lambda (H8: (eq T (TLRef i) (THead 
(Bind x0) x1 x2))).(\lambda (H9: (eq T t2 (THead (Bind x0) x5 (THead (Flat 
Appl) (lift (S O) O x4) x3)))).(\lambda (_: (pr2 c t1 x4)).(\lambda (_: (pr2 
c x1 x5)).(\lambda (_: (pr2 (CHead c (Bind x0) x5) x2 x3)).(let H13 \def 
(eq_ind T t2 (\lambda (t: T).((eq T (THead (Flat Appl) t1 (TLRef i)) t) \to 
(\forall (P: Prop).P))) H3 (THead (Bind x0) x5 (THead (Flat Appl) (lift (S O) 
O x4) x3)) H9) in (eq_ind_r T (THead (Bind x0) x5 (THead (Flat Appl) (lift (S 
O) O x4) x3)) (\lambda (t: T).(sn3 c t)) (let H14 \def (eq_ind T (TLRef i) 
(\lambda (ee: T).(match ee in T return (\lambda (_: T).Prop) with [(TSort _) 
\Rightarrow False | (TLRef _) \Rightarrow True | (THead _ _ _) \Rightarrow 
False])) I (THead (Bind x0) x1 x2) H8) in (False_ind (sn3 c (THead (Bind x0) 
x5 (THead (Flat Appl) (lift (S O) O x4) x3))) H14)) t2 H9)))))))))))))) H6)) 
H5))))))))) v H0))))).

theorem sn3_appl_cast:
 \forall (c: C).(\forall (v: T).(\forall (u: T).((sn3 c (THead (Flat Appl) v 
u)) \to (\forall (t: T).((sn3 c (THead (Flat Appl) v t)) \to (sn3 c (THead 
(Flat Appl) v (THead (Flat Cast) u t))))))))
\def
 \lambda (c: C).(\lambda (v: T).(\lambda (u: T).(\lambda (H: (sn3 c (THead 
(Flat Appl) v u))).(insert_eq T (THead (Flat Appl) v u) (\lambda (t: T).(sn3 
c t)) (\forall (t: T).((sn3 c (THead (Flat Appl) v t)) \to (sn3 c (THead 
(Flat Appl) v (THead (Flat Cast) u t))))) (\lambda (y: T).(\lambda (H0: (sn3 
c y)).(unintro T u (\lambda (t: T).((eq T y (THead (Flat Appl) v t)) \to 
(\forall (t0: T).((sn3 c (THead (Flat Appl) v t0)) \to (sn3 c (THead (Flat 
Appl) v (THead (Flat Cast) t t0))))))) (unintro T v (\lambda (t: T).(\forall 
(x: T).((eq T y (THead (Flat Appl) t x)) \to (\forall (t0: T).((sn3 c (THead 
(Flat Appl) t t0)) \to (sn3 c (THead (Flat Appl) t (THead (Flat Cast) x 
t0)))))))) (sn3_ind c (\lambda (t: T).(\forall (x: T).(\forall (x0: T).((eq T 
t (THead (Flat Appl) x x0)) \to (\forall (t0: T).((sn3 c (THead (Flat Appl) x 
t0)) \to (sn3 c (THead (Flat Appl) x (THead (Flat Cast) x0 t0))))))))) 
(\lambda (t1: T).(\lambda (H1: ((\forall (t2: T).((((eq T t1 t2) \to (\forall 
(P: Prop).P))) \to ((pr3 c t1 t2) \to (sn3 c t2)))))).(\lambda (H2: ((\forall 
(t2: T).((((eq T t1 t2) \to (\forall (P: Prop).P))) \to ((pr3 c t1 t2) \to 
(\forall (x: T).(\forall (x0: T).((eq T t2 (THead (Flat Appl) x x0)) \to 
(\forall (t: T).((sn3 c (THead (Flat Appl) x t)) \to (sn3 c (THead (Flat 
Appl) x (THead (Flat Cast) x0 t))))))))))))).(\lambda (x: T).(\lambda (x0: 
T).(\lambda (H3: (eq T t1 (THead (Flat Appl) x x0))).(\lambda (t: T).(\lambda 
(H4: (sn3 c (THead (Flat Appl) x t))).(insert_eq T (THead (Flat Appl) x t) 
(\lambda (t0: T).(sn3 c t0)) (sn3 c (THead (Flat Appl) x (THead (Flat Cast) 
x0 t))) (\lambda (y0: T).(\lambda (H5: (sn3 c y0)).(unintro T t (\lambda (t0: 
T).((eq T y0 (THead (Flat Appl) x t0)) \to (sn3 c (THead (Flat Appl) x (THead 
(Flat Cast) x0 t0))))) (sn3_ind c (\lambda (t0: T).(\forall (x1: T).((eq T t0 
(THead (Flat Appl) x x1)) \to (sn3 c (THead (Flat Appl) x (THead (Flat Cast) 
x0 x1)))))) (\lambda (t0: T).(\lambda (H6: ((\forall (t2: T).((((eq T t0 t2) 
\to (\forall (P: Prop).P))) \to ((pr3 c t0 t2) \to (sn3 c t2)))))).(\lambda 
(H7: ((\forall (t2: T).((((eq T t0 t2) \to (\forall (P: Prop).P))) \to ((pr3 
c t0 t2) \to (\forall (x1: T).((eq T t2 (THead (Flat Appl) x x1)) \to (sn3 c 
(THead (Flat Appl) x (THead (Flat Cast) x0 x1)))))))))).(\lambda (x1: 
T).(\lambda (H8: (eq T t0 (THead (Flat Appl) x x1))).(let H9 \def (eq_ind T 
t0 (\lambda (t2: T).(\forall (t3: T).((((eq T t2 t3) \to (\forall (P: 
Prop).P))) \to ((pr3 c t2 t3) \to (\forall (x2: T).((eq T t3 (THead (Flat 
Appl) x x2)) \to (sn3 c (THead (Flat Appl) x (THead (Flat Cast) x0 
x2))))))))) H7 (THead (Flat Appl) x x1) H8) in (let H10 \def (eq_ind T t0 
(\lambda (t2: T).(\forall (t3: T).((((eq T t2 t3) \to (\forall (P: Prop).P))) 
\to ((pr3 c t2 t3) \to (sn3 c t3))))) H6 (THead (Flat Appl) x x1) H8) in (let 
H11 \def (eq_ind T t1 (\lambda (t2: T).(\forall (t3: T).((((eq T t2 t3) \to 
(\forall (P: Prop).P))) \to ((pr3 c t2 t3) \to (\forall (x2: T).(\forall (x3: 
T).((eq T t3 (THead (Flat Appl) x2 x3)) \to (\forall (t4: T).((sn3 c (THead 
(Flat Appl) x2 t4)) \to (sn3 c (THead (Flat Appl) x2 (THead (Flat Cast) x3 
t4)))))))))))) H2 (THead (Flat Appl) x x0) H3) in (let H12 \def (eq_ind T t1 
(\lambda (t2: T).(\forall (t3: T).((((eq T t2 t3) \to (\forall (P: Prop).P))) 
\to ((pr3 c t2 t3) \to (sn3 c t3))))) H1 (THead (Flat Appl) x x0) H3) in 
(sn3_pr2_intro c (THead (Flat Appl) x (THead (Flat Cast) x0 x1)) (\lambda 
(t2: T).(\lambda (H13: (((eq T (THead (Flat Appl) x (THead (Flat Cast) x0 
x1)) t2) \to (\forall (P: Prop).P)))).(\lambda (H14: (pr2 c (THead (Flat 
Appl) x (THead (Flat Cast) x0 x1)) t2)).(let H15 \def (pr2_gen_appl c x 
(THead (Flat Cast) x0 x1) t2 H14) in (or3_ind (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T t2 (THead (Flat Appl) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c x u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c 
(THead (Flat Cast) x0 x1) t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Flat Cast) x0 x1) 
(THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (t3: T).(eq T t2 (THead (Bind Abbr) u2 t3)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c x u2))))) (\lambda 
(_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: T).(\forall (b: 
B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) z1 t3)))))))) (ex6_6 B T T T T 
T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda 
(y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq 
T (THead (Flat Cast) x0 x1) (THead (Bind b) y1 z1)))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda 
(y2: T).(eq T t2 (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) 
z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c x u2))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 c y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b) 
y2) z1 z2)))))))) (sn3 c t2) (\lambda (H16: (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T t2 (THead (Flat Appl) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c x u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c 
(THead (Flat Cast) x0 x1) t3))))).(ex3_2_ind T T (\lambda (u2: T).(\lambda 
(t3: T).(eq T t2 (THead (Flat Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: 
T).(pr2 c x u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c (THead (Flat Cast) 
x0 x1) t3))) (sn3 c t2) (\lambda (x2: T).(\lambda (x3: T).(\lambda (H17: (eq 
T t2 (THead (Flat Appl) x2 x3))).(\lambda (H18: (pr2 c x x2)).(\lambda (H19: 
(pr2 c (THead (Flat Cast) x0 x1) x3)).(let H20 \def (eq_ind T t2 (\lambda 
(t3: T).((eq T (THead (Flat Appl) x (THead (Flat Cast) x0 x1)) t3) \to 
(\forall (P: Prop).P))) H13 (THead (Flat Appl) x2 x3) H17) in (eq_ind_r T 
(THead (Flat Appl) x2 x3) (\lambda (t3: T).(sn3 c t3)) (let H21 \def 
(pr2_gen_cast c x0 x1 x3 H19) in (or_ind (ex3_2 T T (\lambda (u2: T).(\lambda 
(t3: T).(eq T x3 (THead (Flat Cast) u2 t3)))) (\lambda (u2: T).(\lambda (_: 
T).(pr2 c x0 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c x1 t3)))) (pr2 c 
x1 x3) (sn3 c (THead (Flat Appl) x2 x3)) (\lambda (H22: (ex3_2 T T (\lambda 
(u2: T).(\lambda (t3: T).(eq T x3 (THead (Flat Cast) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c x0 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c x1 
t3))))).(ex3_2_ind T T (\lambda (u2: T).(\lambda (t3: T).(eq T x3 (THead 
(Flat Cast) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c x0 u2))) 
(\lambda (_: T).(\lambda (t3: T).(pr2 c x1 t3))) (sn3 c (THead (Flat Appl) x2 
x3)) (\lambda (x4: T).(\lambda (x5: T).(\lambda (H23: (eq T x3 (THead (Flat 
Cast) x4 x5))).(\lambda (H24: (pr2 c x0 x4)).(\lambda (H25: (pr2 c x1 
x5)).(let H26 \def (eq_ind T x3 (\lambda (t3: T).((eq T (THead (Flat Appl) x 
(THead (Flat Cast) x0 x1)) (THead (Flat Appl) x2 t3)) \to (\forall (P: 
Prop).P))) H20 (THead (Flat Cast) x4 x5) H23) in (eq_ind_r T (THead (Flat 
Cast) x4 x5) (\lambda (t3: T).(sn3 c (THead (Flat Appl) x2 t3))) (let H_x 
\def (term_dec (THead (Flat Appl) x x0) (THead (Flat Appl) x2 x4)) in (let 
H27 \def H_x in (or_ind (eq T (THead (Flat Appl) x x0) (THead (Flat Appl) x2 
x4)) ((eq T (THead (Flat Appl) x x0) (THead (Flat Appl) x2 x4)) \to (\forall 
(P: Prop).P)) (sn3 c (THead (Flat Appl) x2 (THead (Flat Cast) x4 x5))) 
(\lambda (H28: (eq T (THead (Flat Appl) x x0) (THead (Flat Appl) x2 
x4))).(let H29 \def (f_equal T T (\lambda (e: T).(match e in T return 
(\lambda (_: T).T) with [(TSort _) \Rightarrow x | (TLRef _) \Rightarrow x | 
(THead _ t3 _) \Rightarrow t3])) (THead (Flat Appl) x x0) (THead (Flat Appl) 
x2 x4) H28) in ((let H30 \def (f_equal T T (\lambda (e: T).(match e in T 
return (\lambda (_: T).T) with [(TSort _) \Rightarrow x0 | (TLRef _) 
\Rightarrow x0 | (THead _ _ t3) \Rightarrow t3])) (THead (Flat Appl) x x0) 
(THead (Flat Appl) x2 x4) H28) in (\lambda (H31: (eq T x x2)).(let H32 \def 
(eq_ind_r T x4 (\lambda (t3: T).((eq T (THead (Flat Appl) x (THead (Flat 
Cast) x0 x1)) (THead (Flat Appl) x2 (THead (Flat Cast) t3 x5))) \to (\forall 
(P: Prop).P))) H26 x0 H30) in (let H33 \def (eq_ind_r T x4 (\lambda (t3: 
T).(pr2 c x0 t3)) H24 x0 H30) in (eq_ind T x0 (\lambda (t3: T).(sn3 c (THead 
(Flat Appl) x2 (THead (Flat Cast) t3 x5)))) (let H34 \def (eq_ind_r T x2 
(\lambda (t3: T).((eq T (THead (Flat Appl) x (THead (Flat Cast) x0 x1)) 
(THead (Flat Appl) t3 (THead (Flat Cast) x0 x5))) \to (\forall (P: Prop).P))) 
H32 x H31) in (let H35 \def (eq_ind_r T x2 (\lambda (t3: T).(pr2 c x t3)) H18 
x H31) in (eq_ind T x (\lambda (t3: T).(sn3 c (THead (Flat Appl) t3 (THead 
(Flat Cast) x0 x5)))) (let H_x0 \def (term_dec (THead (Flat Appl) x x1) 
(THead (Flat Appl) x x5)) in (let H36 \def H_x0 in (or_ind (eq T (THead (Flat 
Appl) x x1) (THead (Flat Appl) x x5)) ((eq T (THead (Flat Appl) x x1) (THead 
(Flat Appl) x x5)) \to (\forall (P: Prop).P)) (sn3 c (THead (Flat Appl) x 
(THead (Flat Cast) x0 x5))) (\lambda (H37: (eq T (THead (Flat Appl) x x1) 
(THead (Flat Appl) x x5))).(let H38 \def (f_equal T T (\lambda (e: T).(match 
e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow x1 | (TLRef _) 
\Rightarrow x1 | (THead _ _ t3) \Rightarrow t3])) (THead (Flat Appl) x x1) 
(THead (Flat Appl) x x5) H37) in (let H39 \def (eq_ind_r T x5 (\lambda (t3: 
T).((eq T (THead (Flat Appl) x (THead (Flat Cast) x0 x1)) (THead (Flat Appl) 
x (THead (Flat Cast) x0 t3))) \to (\forall (P: Prop).P))) H34 x1 H38) in (let 
H40 \def (eq_ind_r T x5 (\lambda (t3: T).(pr2 c x1 t3)) H25 x1 H38) in 
(eq_ind T x1 (\lambda (t3: T).(sn3 c (THead (Flat Appl) x (THead (Flat Cast) 
x0 t3)))) (H39 (refl_equal T (THead (Flat Appl) x (THead (Flat Cast) x0 x1))) 
(sn3 c (THead (Flat Appl) x (THead (Flat Cast) x0 x1)))) x5 H38))))) (\lambda 
(H37: (((eq T (THead (Flat Appl) x x1) (THead (Flat Appl) x x5)) \to (\forall 
(P: Prop).P)))).(H9 (THead (Flat Appl) x x5) H37 (pr3_pr2 c (THead (Flat 
Appl) x x1) (THead (Flat Appl) x x5) (pr2_thin_dx c x1 x5 H25 x Appl)) x5 
(refl_equal T (THead (Flat Appl) x x5)))) H36))) x2 H31))) x4 H30))))) H29))) 
(\lambda (H28: (((eq T (THead (Flat Appl) x x0) (THead (Flat Appl) x2 x4)) 
\to (\forall (P: Prop).P)))).(let H_x0 \def (term_dec (THead (Flat Appl) x 
x1) (THead (Flat Appl) x2 x5)) in (let H29 \def H_x0 in (or_ind (eq T (THead 
(Flat Appl) x x1) (THead (Flat Appl) x2 x5)) ((eq T (THead (Flat Appl) x x1) 
(THead (Flat Appl) x2 x5)) \to (\forall (P: Prop).P)) (sn3 c (THead (Flat 
Appl) x2 (THead (Flat Cast) x4 x5))) (\lambda (H30: (eq T (THead (Flat Appl) 
x x1) (THead (Flat Appl) x2 x5))).(let H31 \def (f_equal T T (\lambda (e: 
T).(match e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow x | 
(TLRef _) \Rightarrow x | (THead _ t3 _) \Rightarrow t3])) (THead (Flat Appl) 
x x1) (THead (Flat Appl) x2 x5) H30) in ((let H32 \def (f_equal T T (\lambda 
(e: T).(match e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow x1 
| (TLRef _) \Rightarrow x1 | (THead _ _ t3) \Rightarrow t3])) (THead (Flat 
Appl) x x1) (THead (Flat Appl) x2 x5) H30) in (\lambda (H33: (eq T x 
x2)).(let H34 \def (eq_ind_r T x5 (\lambda (t3: T).(pr2 c x1 t3)) H25 x1 H32) 
in (eq_ind T x1 (\lambda (t3: T).(sn3 c (THead (Flat Appl) x2 (THead (Flat 
Cast) x4 t3)))) (let H35 \def (eq_ind_r T x2 (\lambda (t3: T).((eq T (THead 
(Flat Appl) x x0) (THead (Flat Appl) t3 x4)) \to (\forall (P: Prop).P))) H28 
x H33) in (let H36 \def (eq_ind_r T x2 (\lambda (t3: T).(pr2 c x t3)) H18 x 
H33) in (eq_ind T x (\lambda (t3: T).(sn3 c (THead (Flat Appl) t3 (THead 
(Flat Cast) x4 x1)))) (H11 (THead (Flat Appl) x x4) H35 (pr3_pr2 c (THead 
(Flat Appl) x x0) (THead (Flat Appl) x x4) (pr2_thin_dx c x0 x4 H24 x Appl)) 
x x4 (refl_equal T (THead (Flat Appl) x x4)) x1 (sn3_sing c (THead (Flat 
Appl) x x1) H10)) x2 H33))) x5 H32)))) H31))) (\lambda (H30: (((eq T (THead 
(Flat Appl) x x1) (THead (Flat Appl) x2 x5)) \to (\forall (P: 
Prop).P)))).(H11 (THead (Flat Appl) x2 x4) H28 (pr3_flat c x x2 (pr3_pr2 c x 
x2 H18) x0 x4 (pr3_pr2 c x0 x4 H24) Appl) x2 x4 (refl_equal T (THead (Flat 
Appl) x2 x4)) x5 (H10 (THead (Flat Appl) x2 x5) H30 (pr3_flat c x x2 (pr3_pr2 
c x x2 H18) x1 x5 (pr3_pr2 c x1 x5 H25) Appl)))) H29)))) H27))) x3 H23))))))) 
H22)) (\lambda (H22: (pr2 c x1 x3)).(let H_x \def (term_dec (THead (Flat 
Appl) x x1) (THead (Flat Appl) x2 x3)) in (let H23 \def H_x in (or_ind (eq T 
(THead (Flat Appl) x x1) (THead (Flat Appl) x2 x3)) ((eq T (THead (Flat Appl) 
x x1) (THead (Flat Appl) x2 x3)) \to (\forall (P: Prop).P)) (sn3 c (THead 
(Flat Appl) x2 x3)) (\lambda (H24: (eq T (THead (Flat Appl) x x1) (THead 
(Flat Appl) x2 x3))).(let H25 \def (f_equal T T (\lambda (e: T).(match e in T 
return (\lambda (_: T).T) with [(TSort _) \Rightarrow x | (TLRef _) 
\Rightarrow x | (THead _ t3 _) \Rightarrow t3])) (THead (Flat Appl) x x1) 
(THead (Flat Appl) x2 x3) H24) in ((let H26 \def (f_equal T T (\lambda (e: 
T).(match e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow x1 | 
(TLRef _) \Rightarrow x1 | (THead _ _ t3) \Rightarrow t3])) (THead (Flat 
Appl) x x1) (THead (Flat Appl) x2 x3) H24) in (\lambda (H27: (eq T x 
x2)).(let H28 \def (eq_ind_r T x3 (\lambda (t3: T).(pr2 c x1 t3)) H22 x1 H26) 
in (let H29 \def (eq_ind_r T x3 (\lambda (t3: T).((eq T (THead (Flat Appl) x 
(THead (Flat Cast) x0 x1)) (THead (Flat Appl) x2 t3)) \to (\forall (P: 
Prop).P))) H20 x1 H26) in (eq_ind T x1 (\lambda (t3: T).(sn3 c (THead (Flat 
Appl) x2 t3))) (let H30 \def (eq_ind_r T x2 (\lambda (t3: T).((eq T (THead 
(Flat Appl) x (THead (Flat Cast) x0 x1)) (THead (Flat Appl) t3 x1)) \to 
(\forall (P: Prop).P))) H29 x H27) in (let H31 \def (eq_ind_r T x2 (\lambda 
(t3: T).(pr2 c x t3)) H18 x H27) in (eq_ind T x (\lambda (t3: T).(sn3 c 
(THead (Flat Appl) t3 x1))) (sn3_sing c (THead (Flat Appl) x x1) H10) x2 
H27))) x3 H26))))) H25))) (\lambda (H24: (((eq T (THead (Flat Appl) x x1) 
(THead (Flat Appl) x2 x3)) \to (\forall (P: Prop).P)))).(H10 (THead (Flat 
Appl) x2 x3) H24 (pr3_flat c x x2 (pr3_pr2 c x x2 H18) x1 x3 (pr3_pr2 c x1 x3 
H22) Appl))) H23)))) H21)) t2 H17))))))) H16)) (\lambda (H16: (ex4_4 T T T T 
(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T 
(THead (Flat Cast) x0 x1) (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind 
Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr2 c x u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t3: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) 
u0) z1 t3))))))))).(ex4_4_ind T T T T (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Flat Cast) x0 x1) (THead 
(Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (t3: T).(eq T t2 (THead (Bind Abbr) u2 t3)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c x u2))))) (\lambda 
(_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: T).(\forall (b: 
B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) z1 t3))))))) (sn3 c t2) 
(\lambda (x2: T).(\lambda (x3: T).(\lambda (x4: T).(\lambda (x5: T).(\lambda 
(H17: (eq T (THead (Flat Cast) x0 x1) (THead (Bind Abst) x2 x3))).(\lambda 
(H18: (eq T t2 (THead (Bind Abbr) x4 x5))).(\lambda (_: (pr2 c x 
x4)).(\lambda (_: ((\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) 
u0) x3 x5))))).(let H21 \def (eq_ind T t2 (\lambda (t3: T).((eq T (THead 
(Flat Appl) x (THead (Flat Cast) x0 x1)) t3) \to (\forall (P: Prop).P))) H13 
(THead (Bind Abbr) x4 x5) H18) in (eq_ind_r T (THead (Bind Abbr) x4 x5) 
(\lambda (t3: T).(sn3 c t3)) (let H22 \def (eq_ind T (THead (Flat Cast) x0 
x1) (\lambda (ee: T).(match ee in T return (\lambda (_: T).Prop) with [(TSort 
_) \Rightarrow False | (TLRef _) \Rightarrow False | (THead k _ _) 
\Rightarrow (match k in K return (\lambda (_: K).Prop) with [(Bind _) 
\Rightarrow False | (Flat _) \Rightarrow True])])) I (THead (Bind Abst) x2 
x3) H17) in (False_ind (sn3 c (THead (Bind Abbr) x4 x5)) H22)) t2 
H18)))))))))) H16)) (\lambda (H16: (ex6_6 B T T T T T (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Flat 
Cast) x0 x1) (THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T 
t2 (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) 
(\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr2 c x u2))))))) (\lambda (_: B).(\lambda (y1: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 
y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b) y2) z1 
z2))))))))).(ex6_6_ind B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b 
Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Flat Cast) x0 x1) (THead 
(Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T t2 (THead (Bind 
b) y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr2 c x u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 y2))))))) 
(\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda 
(_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b) y2) z1 z2))))))) (sn3 c t2) 
(\lambda (x2: B).(\lambda (x3: T).(\lambda (x4: T).(\lambda (x5: T).(\lambda 
(x6: T).(\lambda (x7: T).(\lambda (_: (not (eq B x2 Abst))).(\lambda (H18: 
(eq T (THead (Flat Cast) x0 x1) (THead (Bind x2) x3 x4))).(\lambda (H19: (eq 
T t2 (THead (Bind x2) x7 (THead (Flat Appl) (lift (S O) O x6) x5)))).(\lambda 
(_: (pr2 c x x6)).(\lambda (_: (pr2 c x3 x7)).(\lambda (_: (pr2 (CHead c 
(Bind x2) x7) x4 x5)).(let H23 \def (eq_ind T t2 (\lambda (t3: T).((eq T 
(THead (Flat Appl) x (THead (Flat Cast) x0 x1)) t3) \to (\forall (P: 
Prop).P))) H13 (THead (Bind x2) x7 (THead (Flat Appl) (lift (S O) O x6) x5)) 
H19) in (eq_ind_r T (THead (Bind x2) x7 (THead (Flat Appl) (lift (S O) O x6) 
x5)) (\lambda (t3: T).(sn3 c t3)) (let H24 \def (eq_ind T (THead (Flat Cast) 
x0 x1) (\lambda (ee: T).(match ee in T return (\lambda (_: T).Prop) with 
[(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | (THead k _ _) 
\Rightarrow (match k in K return (\lambda (_: K).Prop) with [(Bind _) 
\Rightarrow False | (Flat _) \Rightarrow True])])) I (THead (Bind x2) x3 x4) 
H18) in (False_ind (sn3 c (THead (Bind x2) x7 (THead (Flat Appl) (lift (S O) 
O x6) x5))) H24)) t2 H19)))))))))))))) H16)) H15))))))))))))))) y0 H5)))) 
H4))))))))) y H0))))) H)))).

theorem sn3_appl_appl:
 \forall (v1: T).(\forall (t1: T).(let u1 \def (THead (Flat Appl) v1 t1) in 
(\forall (c: C).((sn3 c u1) \to (\forall (v2: T).((sn3 c v2) \to (((\forall 
(u2: T).((pr3 c u1 u2) \to ((((iso u1 u2) \to (\forall (P: Prop).P))) \to 
(sn3 c (THead (Flat Appl) v2 u2)))))) \to (sn3 c (THead (Flat Appl) v2 
u1)))))))))
\def
 \lambda (v1: T).(\lambda (t1: T).(let u1 \def (THead (Flat Appl) v1 t1) in 
(\lambda (c: C).(\lambda (H: (sn3 c (THead (Flat Appl) v1 t1))).(insert_eq T 
(THead (Flat Appl) v1 t1) (\lambda (t: T).(sn3 c t)) (\forall (v2: T).((sn3 c 
v2) \to (((\forall (u2: T).((pr3 c (THead (Flat Appl) v1 t1) u2) \to ((((iso 
(THead (Flat Appl) v1 t1) u2) \to (\forall (P: Prop).P))) \to (sn3 c (THead 
(Flat Appl) v2 u2)))))) \to (sn3 c (THead (Flat Appl) v2 (THead (Flat Appl) 
v1 t1)))))) (\lambda (y: T).(\lambda (H0: (sn3 c y)).(unintro T t1 (\lambda 
(t: T).((eq T y (THead (Flat Appl) v1 t)) \to (\forall (v2: T).((sn3 c v2) 
\to (((\forall (u2: T).((pr3 c (THead (Flat Appl) v1 t) u2) \to ((((iso 
(THead (Flat Appl) v1 t) u2) \to (\forall (P: Prop).P))) \to (sn3 c (THead 
(Flat Appl) v2 u2)))))) \to (sn3 c (THead (Flat Appl) v2 (THead (Flat Appl) 
v1 t)))))))) (unintro T v1 (\lambda (t: T).(\forall (x: T).((eq T y (THead 
(Flat Appl) t x)) \to (\forall (v2: T).((sn3 c v2) \to (((\forall (u2: 
T).((pr3 c (THead (Flat Appl) t x) u2) \to ((((iso (THead (Flat Appl) t x) 
u2) \to (\forall (P: Prop).P))) \to (sn3 c (THead (Flat Appl) v2 u2)))))) \to 
(sn3 c (THead (Flat Appl) v2 (THead (Flat Appl) t x))))))))) (sn3_ind c 
(\lambda (t: T).(\forall (x: T).(\forall (x0: T).((eq T t (THead (Flat Appl) 
x x0)) \to (\forall (v2: T).((sn3 c v2) \to (((\forall (u2: T).((pr3 c (THead 
(Flat Appl) x x0) u2) \to ((((iso (THead (Flat Appl) x x0) u2) \to (\forall 
(P: Prop).P))) \to (sn3 c (THead (Flat Appl) v2 u2)))))) \to (sn3 c (THead 
(Flat Appl) v2 (THead (Flat Appl) x x0)))))))))) (\lambda (t2: T).(\lambda 
(H1: ((\forall (t3: T).((((eq T t2 t3) \to (\forall (P: Prop).P))) \to ((pr3 
c t2 t3) \to (sn3 c t3)))))).(\lambda (H2: ((\forall (t3: T).((((eq T t2 t3) 
\to (\forall (P: Prop).P))) \to ((pr3 c t2 t3) \to (\forall (x: T).(\forall 
(x0: T).((eq T t3 (THead (Flat Appl) x x0)) \to (\forall (v2: T).((sn3 c v2) 
\to (((\forall (u2: T).((pr3 c (THead (Flat Appl) x x0) u2) \to ((((iso 
(THead (Flat Appl) x x0) u2) \to (\forall (P: Prop).P))) \to (sn3 c (THead 
(Flat Appl) v2 u2)))))) \to (sn3 c (THead (Flat Appl) v2 (THead (Flat Appl) x 
x0)))))))))))))).(\lambda (x: T).(\lambda (x0: T).(\lambda (H3: (eq T t2 
(THead (Flat Appl) x x0))).(\lambda (v2: T).(\lambda (H4: (sn3 c 
v2)).(sn3_ind c (\lambda (t: T).(((\forall (u2: T).((pr3 c (THead (Flat Appl) 
x x0) u2) \to ((((iso (THead (Flat Appl) x x0) u2) \to (\forall (P: 
Prop).P))) \to (sn3 c (THead (Flat Appl) t u2)))))) \to (sn3 c (THead (Flat 
Appl) t (THead (Flat Appl) x x0))))) (\lambda (t0: T).(\lambda (H5: ((\forall 
(t3: T).((((eq T t0 t3) \to (\forall (P: Prop).P))) \to ((pr3 c t0 t3) \to 
(sn3 c t3)))))).(\lambda (H6: ((\forall (t3: T).((((eq T t0 t3) \to (\forall 
(P: Prop).P))) \to ((pr3 c t0 t3) \to (((\forall (u2: T).((pr3 c (THead (Flat 
Appl) x x0) u2) \to ((((iso (THead (Flat Appl) x x0) u2) \to (\forall (P: 
Prop).P))) \to (sn3 c (THead (Flat Appl) t3 u2)))))) \to (sn3 c (THead (Flat 
Appl) t3 (THead (Flat Appl) x x0))))))))).(\lambda (H7: ((\forall (u2: 
T).((pr3 c (THead (Flat Appl) x x0) u2) \to ((((iso (THead (Flat Appl) x x0) 
u2) \to (\forall (P: Prop).P))) \to (sn3 c (THead (Flat Appl) t0 
u2))))))).(let H8 \def (eq_ind T t2 (\lambda (t: T).(\forall (t3: T).((((eq T 
t t3) \to (\forall (P: Prop).P))) \to ((pr3 c t t3) \to (\forall (x1: 
T).(\forall (x2: T).((eq T t3 (THead (Flat Appl) x1 x2)) \to (\forall (v3: 
T).((sn3 c v3) \to (((\forall (u2: T).((pr3 c (THead (Flat Appl) x1 x2) u2) 
\to ((((iso (THead (Flat Appl) x1 x2) u2) \to (\forall (P: Prop).P))) \to 
(sn3 c (THead (Flat Appl) v3 u2)))))) \to (sn3 c (THead (Flat Appl) v3 (THead 
(Flat Appl) x1 x2))))))))))))) H2 (THead (Flat Appl) x x0) H3) in (let H9 
\def (eq_ind T t2 (\lambda (t: T).(\forall (t3: T).((((eq T t t3) \to 
(\forall (P: Prop).P))) \to ((pr3 c t t3) \to (sn3 c t3))))) H1 (THead (Flat 
Appl) x x0) H3) in (sn3_pr2_intro c (THead (Flat Appl) t0 (THead (Flat Appl) 
x x0)) (\lambda (t3: T).(\lambda (H10: (((eq T (THead (Flat Appl) t0 (THead 
(Flat Appl) x x0)) t3) \to (\forall (P: Prop).P)))).(\lambda (H11: (pr2 c 
(THead (Flat Appl) t0 (THead (Flat Appl) x x0)) t3)).(let H12 \def 
(pr2_gen_appl c t0 (THead (Flat Appl) x x0) t3 H11) in (or3_ind (ex3_2 T T 
(\lambda (u2: T).(\lambda (t4: T).(eq T t3 (THead (Flat Appl) u2 t4)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c t0 u2))) (\lambda (_: T).(\lambda 
(t4: T).(pr2 c (THead (Flat Appl) x x0) t4)))) (ex4_4 T T T T (\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Flat Appl) 
x x0) (THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda 
(u2: T).(\lambda (t4: T).(eq T t3 (THead (Bind Abbr) u2 t4)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c t0 u2))))) 
(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t4: T).(\forall 
(b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) z1 t4)))))))) (ex6_6 B T T T 
T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda 
(y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq 
T (THead (Flat Appl) x x0) (THead (Bind b) y1 z1)))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda 
(y2: T).(eq T t3 (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) 
z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c t0 u2))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 c y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b) 
y2) z1 z2)))))))) (sn3 c t3) (\lambda (H13: (ex3_2 T T (\lambda (u2: 
T).(\lambda (t4: T).(eq T t3 (THead (Flat Appl) u2 t4)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c t0 u2))) (\lambda (_: T).(\lambda (t4: T).(pr2 c 
(THead (Flat Appl) x x0) t4))))).(ex3_2_ind T T (\lambda (u2: T).(\lambda 
(t4: T).(eq T t3 (THead (Flat Appl) u2 t4)))) (\lambda (u2: T).(\lambda (_: 
T).(pr2 c t0 u2))) (\lambda (_: T).(\lambda (t4: T).(pr2 c (THead (Flat Appl) 
x x0) t4))) (sn3 c t3) (\lambda (x1: T).(\lambda (x2: T).(\lambda (H14: (eq T 
t3 (THead (Flat Appl) x1 x2))).(\lambda (H15: (pr2 c t0 x1)).(\lambda (H16: 
(pr2 c (THead (Flat Appl) x x0) x2)).(let H17 \def (eq_ind T t3 (\lambda (t: 
T).((eq T (THead (Flat Appl) t0 (THead (Flat Appl) x x0)) t) \to (\forall (P: 
Prop).P))) H10 (THead (Flat Appl) x1 x2) H14) in (eq_ind_r T (THead (Flat 
Appl) x1 x2) (\lambda (t: T).(sn3 c t)) (let H18 \def (pr2_gen_appl c x x0 x2 
H16) in (or3_ind (ex3_2 T T (\lambda (u2: T).(\lambda (t4: T).(eq T x2 (THead 
(Flat Appl) u2 t4)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c x u2))) 
(\lambda (_: T).(\lambda (t4: T).(pr2 c x0 t4)))) (ex4_4 T T T T (\lambda 
(y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T x0 (THead 
(Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (t4: T).(eq T x2 (THead (Bind Abbr) u2 t4)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c x u2))))) (\lambda 
(_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t4: T).(\forall (b: 
B).(\forall (u: T).(pr2 (CHead c (Bind b) u) z1 t4)))))))) (ex6_6 B T T T T T 
(\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T x0 
(THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T x2 (THead (Bind 
b) y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr2 c x u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 y2))))))) 
(\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda 
(_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b) y2) z1 z2)))))))) (sn3 c 
(THead (Flat Appl) x1 x2)) (\lambda (H19: (ex3_2 T T (\lambda (u2: 
T).(\lambda (t4: T).(eq T x2 (THead (Flat Appl) u2 t4)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c x u2))) (\lambda (_: T).(\lambda (t4: T).(pr2 c x0 
t4))))).(ex3_2_ind T T (\lambda (u2: T).(\lambda (t4: T).(eq T x2 (THead 
(Flat Appl) u2 t4)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c x u2))) 
(\lambda (_: T).(\lambda (t4: T).(pr2 c x0 t4))) (sn3 c (THead (Flat Appl) x1 
x2)) (\lambda (x3: T).(\lambda (x4: T).(\lambda (H20: (eq T x2 (THead (Flat 
Appl) x3 x4))).(\lambda (H21: (pr2 c x x3)).(\lambda (H22: (pr2 c x0 
x4)).(let H23 \def (eq_ind T x2 (\lambda (t: T).((eq T (THead (Flat Appl) t0 
(THead (Flat Appl) x x0)) (THead (Flat Appl) x1 t)) \to (\forall (P: 
Prop).P))) H17 (THead (Flat Appl) x3 x4) H20) in (eq_ind_r T (THead (Flat 
Appl) x3 x4) (\lambda (t: T).(sn3 c (THead (Flat Appl) x1 t))) (let H_x \def 
(term_dec (THead (Flat Appl) x x0) (THead (Flat Appl) x3 x4)) in (let H24 
\def H_x in (or_ind (eq T (THead (Flat Appl) x x0) (THead (Flat Appl) x3 x4)) 
((eq T (THead (Flat Appl) x x0) (THead (Flat Appl) x3 x4)) \to (\forall (P: 
Prop).P)) (sn3 c (THead (Flat Appl) x1 (THead (Flat Appl) x3 x4))) (\lambda 
(H25: (eq T (THead (Flat Appl) x x0) (THead (Flat Appl) x3 x4))).(let H26 
\def (f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) 
with [(TSort _) \Rightarrow x | (TLRef _) \Rightarrow x | (THead _ t _) 
\Rightarrow t])) (THead (Flat Appl) x x0) (THead (Flat Appl) x3 x4) H25) in 
((let H27 \def (f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: 
T).T) with [(TSort _) \Rightarrow x0 | (TLRef _) \Rightarrow x0 | (THead _ _ 
t) \Rightarrow t])) (THead (Flat Appl) x x0) (THead (Flat Appl) x3 x4) H25) 
in (\lambda (H28: (eq T x x3)).(let H29 \def (eq_ind_r T x4 (\lambda (t: 
T).((eq T (THead (Flat Appl) t0 (THead (Flat Appl) x x0)) (THead (Flat Appl) 
x1 (THead (Flat Appl) x3 t))) \to (\forall (P: Prop).P))) H23 x0 H27) in (let 
H30 \def (eq_ind_r T x4 (\lambda (t: T).(pr2 c x0 t)) H22 x0 H27) in (eq_ind 
T x0 (\lambda (t: T).(sn3 c (THead (Flat Appl) x1 (THead (Flat Appl) x3 t)))) 
(let H31 \def (eq_ind_r T x3 (\lambda (t: T).((eq T (THead (Flat Appl) t0 
(THead (Flat Appl) x x0)) (THead (Flat Appl) x1 (THead (Flat Appl) t x0))) 
\to (\forall (P: Prop).P))) H29 x H28) in (let H32 \def (eq_ind_r T x3 
(\lambda (t: T).(pr2 c x t)) H21 x H28) in (eq_ind T x (\lambda (t: T).(sn3 c 
(THead (Flat Appl) x1 (THead (Flat Appl) t x0)))) (let H_x0 \def (term_dec t0 
x1) in (let H33 \def H_x0 in (or_ind (eq T t0 x1) ((eq T t0 x1) \to (\forall 
(P: Prop).P)) (sn3 c (THead (Flat Appl) x1 (THead (Flat Appl) x x0))) 
(\lambda (H34: (eq T t0 x1)).(let H35 \def (eq_ind_r T x1 (\lambda (t: 
T).((eq T (THead (Flat Appl) t0 (THead (Flat Appl) x x0)) (THead (Flat Appl) 
t (THead (Flat Appl) x x0))) \to (\forall (P: Prop).P))) H31 t0 H34) in (let 
H36 \def (eq_ind_r T x1 (\lambda (t: T).(pr2 c t0 t)) H15 t0 H34) in (eq_ind 
T t0 (\lambda (t: T).(sn3 c (THead (Flat Appl) t (THead (Flat Appl) x x0)))) 
(H35 (refl_equal T (THead (Flat Appl) t0 (THead (Flat Appl) x x0))) (sn3 c 
(THead (Flat Appl) t0 (THead (Flat Appl) x x0)))) x1 H34)))) (\lambda (H34: 
(((eq T t0 x1) \to (\forall (P: Prop).P)))).(H6 x1 H34 (pr3_pr2 c t0 x1 H15) 
(\lambda (u2: T).(\lambda (H35: (pr3 c (THead (Flat Appl) x x0) u2)).(\lambda 
(H36: (((iso (THead (Flat Appl) x x0) u2) \to (\forall (P: 
Prop).P)))).(sn3_pr3_trans c (THead (Flat Appl) t0 u2) (H7 u2 H35 H36) (THead 
(Flat Appl) x1 u2) (pr3_pr2 c (THead (Flat Appl) t0 u2) (THead (Flat Appl) x1 
u2) (pr2_head_1 c t0 x1 H15 (Flat Appl) u2)))))))) H33))) x3 H28))) x4 
H27))))) H26))) (\lambda (H25: (((eq T (THead (Flat Appl) x x0) (THead (Flat 
Appl) x3 x4)) \to (\forall (P: Prop).P)))).(H8 (THead (Flat Appl) x3 x4) H25 
(pr3_flat c x x3 (pr3_pr2 c x x3 H21) x0 x4 (pr3_pr2 c x0 x4 H22) Appl) x3 x4 
(refl_equal T (THead (Flat Appl) x3 x4)) x1 (sn3_pr3_trans c t0 (sn3_sing c 
t0 H5) x1 (pr3_pr2 c t0 x1 H15)) (\lambda (u2: T).(\lambda (H26: (pr3 c 
(THead (Flat Appl) x3 x4) u2)).(\lambda (H27: (((iso (THead (Flat Appl) x3 
x4) u2) \to (\forall (P: Prop).P)))).(sn3_pr3_trans c (THead (Flat Appl) t0 
u2) (H7 u2 (pr3_sing c (THead (Flat Appl) x x4) (THead (Flat Appl) x x0) 
(pr2_thin_dx c x0 x4 H22 x Appl) u2 (pr3_sing c (THead (Flat Appl) x3 x4) 
(THead (Flat Appl) x x4) (pr2_head_1 c x x3 H21 (Flat Appl) x4) u2 H26)) 
(\lambda (H28: (iso (THead (Flat Appl) x x0) u2)).(\lambda (P: Prop).(H27 
(iso_trans (THead (Flat Appl) x3 x4) (THead (Flat Appl) x x0) (iso_head x3 x 
x4 x0 (Flat Appl)) u2 H28) P)))) (THead (Flat Appl) x1 u2) (pr3_pr2 c (THead 
(Flat Appl) t0 u2) (THead (Flat Appl) x1 u2) (pr2_head_1 c t0 x1 H15 (Flat 
Appl) u2)))))))) H24))) x2 H20))))))) H19)) (\lambda (H19: (ex4_4 T T T T 
(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T x0 
(THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (t4: T).(eq T x2 (THead (Bind Abbr) u2 t4)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c x u2))))) (\lambda 
(_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t4: T).(\forall (b: 
B).(\forall (u: T).(pr2 (CHead c (Bind b) u) z1 t4))))))))).(ex4_4_ind T T T 
T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T x0 
(THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (t4: T).(eq T x2 (THead (Bind Abbr) u2 t4)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c x u2))))) (\lambda 
(_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t4: T).(\forall (b: 
B).(\forall (u: T).(pr2 (CHead c (Bind b) u) z1 t4))))))) (sn3 c (THead (Flat 
Appl) x1 x2)) (\lambda (x3: T).(\lambda (x4: T).(\lambda (x5: T).(\lambda 
(x6: T).(\lambda (H20: (eq T x0 (THead (Bind Abst) x3 x4))).(\lambda (H21: 
(eq T x2 (THead (Bind Abbr) x5 x6))).(\lambda (H22: (pr2 c x x5)).(\lambda 
(H23: ((\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) x4 
x6))))).(let H24 \def (eq_ind T x2 (\lambda (t: T).((eq T (THead (Flat Appl) 
t0 (THead (Flat Appl) x x0)) (THead (Flat Appl) x1 t)) \to (\forall (P: 
Prop).P))) H17 (THead (Bind Abbr) x5 x6) H21) in (eq_ind_r T (THead (Bind 
Abbr) x5 x6) (\lambda (t: T).(sn3 c (THead (Flat Appl) x1 t))) (let H25 \def 
(eq_ind T x0 (\lambda (t: T).((eq T (THead (Flat Appl) t0 (THead (Flat Appl) 
x t)) (THead (Flat Appl) x1 (THead (Bind Abbr) x5 x6))) \to (\forall (P: 
Prop).P))) H24 (THead (Bind Abst) x3 x4) H20) in (let H26 \def (eq_ind T x0 
(\lambda (t: T).(\forall (t4: T).((((eq T (THead (Flat Appl) x t) t4) \to 
(\forall (P: Prop).P))) \to ((pr3 c (THead (Flat Appl) x t) t4) \to (sn3 c 
t4))))) H9 (THead (Bind Abst) x3 x4) H20) in (let H27 \def (eq_ind T x0 
(\lambda (t: T).(\forall (t4: T).((((eq T (THead (Flat Appl) x t) t4) \to 
(\forall (P: Prop).P))) \to ((pr3 c (THead (Flat Appl) x t) t4) \to (\forall 
(x7: T).(\forall (x8: T).((eq T t4 (THead (Flat Appl) x7 x8)) \to (\forall 
(v3: T).((sn3 c v3) \to (((\forall (u2: T).((pr3 c (THead (Flat Appl) x7 x8) 
u2) \to ((((iso (THead (Flat Appl) x7 x8) u2) \to (\forall (P: Prop).P))) \to 
(sn3 c (THead (Flat Appl) v3 u2)))))) \to (sn3 c (THead (Flat Appl) v3 (THead 
(Flat Appl) x7 x8))))))))))))) H8 (THead (Bind Abst) x3 x4) H20) in (let H28 
\def (eq_ind T x0 (\lambda (t: T).(\forall (u2: T).((pr3 c (THead (Flat Appl) 
x t) u2) \to ((((iso (THead (Flat Appl) x t) u2) \to (\forall (P: Prop).P))) 
\to (sn3 c (THead (Flat Appl) t0 u2)))))) H7 (THead (Bind Abst) x3 x4) H20) 
in (let H29 \def (eq_ind T x0 (\lambda (t: T).(\forall (t4: T).((((eq T t0 
t4) \to (\forall (P: Prop).P))) \to ((pr3 c t0 t4) \to (((\forall (u2: 
T).((pr3 c (THead (Flat Appl) x t) u2) \to ((((iso (THead (Flat Appl) x t) 
u2) \to (\forall (P: Prop).P))) \to (sn3 c (THead (Flat Appl) t4 u2)))))) \to 
(sn3 c (THead (Flat Appl) t4 (THead (Flat Appl) x t)))))))) H6 (THead (Bind 
Abst) x3 x4) H20) in (sn3_pr3_trans c (THead (Flat Appl) t0 (THead (Bind 
Abbr) x5 x6)) (H28 (THead (Bind Abbr) x5 x6) (pr3_sing c (THead (Bind Abbr) x 
x4) (THead (Flat Appl) x (THead (Bind Abst) x3 x4)) (pr2_free c (THead (Flat 
Appl) x (THead (Bind Abst) x3 x4)) (THead (Bind Abbr) x x4) (pr0_beta x3 x x 
(pr0_refl x) x4 x4 (pr0_refl x4))) (THead (Bind Abbr) x5 x6) (pr3_head_12 c x 
x5 (pr3_pr2 c x x5 H22) (Bind Abbr) x4 x6 (pr3_pr2 (CHead c (Bind Abbr) x5) 
x4 x6 (H23 Abbr x5)))) (\lambda (H30: (iso (THead (Flat Appl) x (THead (Bind 
Abst) x3 x4)) (THead (Bind Abbr) x5 x6))).(\lambda (P: Prop).(let H31 \def 
(match H30 in iso return (\lambda (t: T).(\lambda (t4: T).(\lambda (_: (iso t 
t4)).((eq T t (THead (Flat Appl) x (THead (Bind Abst) x3 x4))) \to ((eq T t4 
(THead (Bind Abbr) x5 x6)) \to P))))) with [(iso_sort n1 n2) \Rightarrow 
(\lambda (H31: (eq T (TSort n1) (THead (Flat Appl) x (THead (Bind Abst) x3 
x4)))).(\lambda (H32: (eq T (TSort n2) (THead (Bind Abbr) x5 x6))).((let H33 
\def (eq_ind T (TSort n1) (\lambda (e: T).(match e in T return (\lambda (_: 
T).Prop) with [(TSort _) \Rightarrow True | (TLRef _) \Rightarrow False | 
(THead _ _ _) \Rightarrow False])) I (THead (Flat Appl) x (THead (Bind Abst) 
x3 x4)) H31) in (False_ind ((eq T (TSort n2) (THead (Bind Abbr) x5 x6)) \to 
P) H33)) H32))) | (iso_lref i1 i2) \Rightarrow (\lambda (H31: (eq T (TLRef 
i1) (THead (Flat Appl) x (THead (Bind Abst) x3 x4)))).(\lambda (H32: (eq T 
(TLRef i2) (THead (Bind Abbr) x5 x6))).((let H33 \def (eq_ind T (TLRef i1) 
(\lambda (e: T).(match e in T return (\lambda (_: T).Prop) with [(TSort _) 
\Rightarrow False | (TLRef _) \Rightarrow True | (THead _ _ _) \Rightarrow 
False])) I (THead (Flat Appl) x (THead (Bind Abst) x3 x4)) H31) in (False_ind 
((eq T (TLRef i2) (THead (Bind Abbr) x5 x6)) \to P) H33)) H32))) | (iso_head 
v4 v5 t4 t5 k) \Rightarrow (\lambda (H31: (eq T (THead k v4 t4) (THead (Flat 
Appl) x (THead (Bind Abst) x3 x4)))).(\lambda (H32: (eq T (THead k v5 t5) 
(THead (Bind Abbr) x5 x6))).((let H33 \def (f_equal T T (\lambda (e: 
T).(match e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow t4 | 
(TLRef _) \Rightarrow t4 | (THead _ _ t) \Rightarrow t])) (THead k v4 t4) 
(THead (Flat Appl) x (THead (Bind Abst) x3 x4)) H31) in ((let H34 \def 
(f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) with 
[(TSort _) \Rightarrow v4 | (TLRef _) \Rightarrow v4 | (THead _ t _) 
\Rightarrow t])) (THead k v4 t4) (THead (Flat Appl) x (THead (Bind Abst) x3 
x4)) H31) in ((let H35 \def (f_equal T K (\lambda (e: T).(match e in T return 
(\lambda (_: T).K) with [(TSort _) \Rightarrow k | (TLRef _) \Rightarrow k | 
(THead k0 _ _) \Rightarrow k0])) (THead k v4 t4) (THead (Flat Appl) x (THead 
(Bind Abst) x3 x4)) H31) in (eq_ind K (Flat Appl) (\lambda (k0: K).((eq T v4 
x) \to ((eq T t4 (THead (Bind Abst) x3 x4)) \to ((eq T (THead k0 v5 t5) 
(THead (Bind Abbr) x5 x6)) \to P)))) (\lambda (H36: (eq T v4 x)).(eq_ind T x 
(\lambda (_: T).((eq T t4 (THead (Bind Abst) x3 x4)) \to ((eq T (THead (Flat 
Appl) v5 t5) (THead (Bind Abbr) x5 x6)) \to P))) (\lambda (H37: (eq T t4 
(THead (Bind Abst) x3 x4))).(eq_ind T (THead (Bind Abst) x3 x4) (\lambda (_: 
T).((eq T (THead (Flat Appl) v5 t5) (THead (Bind Abbr) x5 x6)) \to P)) 
(\lambda (H38: (eq T (THead (Flat Appl) v5 t5) (THead (Bind Abbr) x5 
x6))).(let H39 \def (eq_ind T (THead (Flat Appl) v5 t5) (\lambda (e: 
T).(match e in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow 
False | (TLRef _) \Rightarrow False | (THead k0 _ _) \Rightarrow (match k0 in 
K return (\lambda (_: K).Prop) with [(Bind _) \Rightarrow False | (Flat _) 
\Rightarrow True])])) I (THead (Bind Abbr) x5 x6) H38) in (False_ind P H39))) 
t4 (sym_eq T t4 (THead (Bind Abst) x3 x4) H37))) v4 (sym_eq T v4 x H36))) k 
(sym_eq K k (Flat Appl) H35))) H34)) H33)) H32)))]) in (H31 (refl_equal T 
(THead (Flat Appl) x (THead (Bind Abst) x3 x4))) (refl_equal T (THead (Bind 
Abbr) x5 x6))))))) (THead (Flat Appl) x1 (THead (Bind Abbr) x5 x6)) (pr3_pr2 
c (THead (Flat Appl) t0 (THead (Bind Abbr) x5 x6)) (THead (Flat Appl) x1 
(THead (Bind Abbr) x5 x6)) (pr2_head_1 c t0 x1 H15 (Flat Appl) (THead (Bind 
Abbr) x5 x6))))))))) x2 H21)))))))))) H19)) (\lambda (H19: (ex6_6 B T T T T T 
(\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T x0 
(THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T x2 (THead (Bind 
b) y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr2 c x u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 y2))))))) 
(\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda 
(_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b) y2) z1 z2))))))))).(ex6_6_ind 
B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(eq T x0 (THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T 
x2 (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) 
(\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr2 c x u2))))))) (\lambda (_: B).(\lambda (y1: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 
y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b) y2) z1 z2))))))) 
(sn3 c (THead (Flat Appl) x1 x2)) (\lambda (x3: B).(\lambda (x4: T).(\lambda 
(x5: T).(\lambda (x6: T).(\lambda (x7: T).(\lambda (x8: T).(\lambda (H20: 
(not (eq B x3 Abst))).(\lambda (H21: (eq T x0 (THead (Bind x3) x4 
x5))).(\lambda (H22: (eq T x2 (THead (Bind x3) x8 (THead (Flat Appl) (lift (S 
O) O x7) x6)))).(\lambda (H23: (pr2 c x x7)).(\lambda (H24: (pr2 c x4 
x8)).(\lambda (H25: (pr2 (CHead c (Bind x3) x8) x5 x6)).(let H26 \def (eq_ind 
T x2 (\lambda (t: T).((eq T (THead (Flat Appl) t0 (THead (Flat Appl) x x0)) 
(THead (Flat Appl) x1 t)) \to (\forall (P: Prop).P))) H17 (THead (Bind x3) x8 
(THead (Flat Appl) (lift (S O) O x7) x6)) H22) in (eq_ind_r T (THead (Bind 
x3) x8 (THead (Flat Appl) (lift (S O) O x7) x6)) (\lambda (t: T).(sn3 c 
(THead (Flat Appl) x1 t))) (let H27 \def (eq_ind T x0 (\lambda (t: T).((eq T 
(THead (Flat Appl) t0 (THead (Flat Appl) x t)) (THead (Flat Appl) x1 (THead 
(Bind x3) x8 (THead (Flat Appl) (lift (S O) O x7) x6)))) \to (\forall (P: 
Prop).P))) H26 (THead (Bind x3) x4 x5) H21) in (let H28 \def (eq_ind T x0 
(\lambda (t: T).(\forall (t4: T).((((eq T (THead (Flat Appl) x t) t4) \to 
(\forall (P: Prop).P))) \to ((pr3 c (THead (Flat Appl) x t) t4) \to (sn3 c 
t4))))) H9 (THead (Bind x3) x4 x5) H21) in (let H29 \def (eq_ind T x0 
(\lambda (t: T).(\forall (t4: T).((((eq T (THead (Flat Appl) x t) t4) \to 
(\forall (P: Prop).P))) \to ((pr3 c (THead (Flat Appl) x t) t4) \to (\forall 
(x9: T).(\forall (x10: T).((eq T t4 (THead (Flat Appl) x9 x10)) \to (\forall 
(v3: T).((sn3 c v3) \to (((\forall (u2: T).((pr3 c (THead (Flat Appl) x9 x10) 
u2) \to ((((iso (THead (Flat Appl) x9 x10) u2) \to (\forall (P: Prop).P))) 
\to (sn3 c (THead (Flat Appl) v3 u2)))))) \to (sn3 c (THead (Flat Appl) v3 
(THead (Flat Appl) x9 x10))))))))))))) H8 (THead (Bind x3) x4 x5) H21) in 
(let H30 \def (eq_ind T x0 (\lambda (t: T).(\forall (u2: T).((pr3 c (THead 
(Flat Appl) x t) u2) \to ((((iso (THead (Flat Appl) x t) u2) \to (\forall (P: 
Prop).P))) \to (sn3 c (THead (Flat Appl) t0 u2)))))) H7 (THead (Bind x3) x4 
x5) H21) in (let H31 \def (eq_ind T x0 (\lambda (t: T).(\forall (t4: 
T).((((eq T t0 t4) \to (\forall (P: Prop).P))) \to ((pr3 c t0 t4) \to 
(((\forall (u2: T).((pr3 c (THead (Flat Appl) x t) u2) \to ((((iso (THead 
(Flat Appl) x t) u2) \to (\forall (P: Prop).P))) \to (sn3 c (THead (Flat 
Appl) t4 u2)))))) \to (sn3 c (THead (Flat Appl) t4 (THead (Flat Appl) x 
t)))))))) H6 (THead (Bind x3) x4 x5) H21) in (sn3_pr3_trans c (THead (Flat 
Appl) t0 (THead (Bind x3) x8 (THead (Flat Appl) (lift (S O) O x7) x6))) (H30 
(THead (Bind x3) x8 (THead (Flat Appl) (lift (S O) O x7) x6)) (pr3_sing c 
(THead (Bind x3) x4 (THead (Flat Appl) (lift (S O) O x) x5)) (THead (Flat 
Appl) x (THead (Bind x3) x4 x5)) (pr2_free c (THead (Flat Appl) x (THead 
(Bind x3) x4 x5)) (THead (Bind x3) x4 (THead (Flat Appl) (lift (S O) O x) 
x5)) (pr0_upsilon x3 H20 x x (pr0_refl x) x4 x4 (pr0_refl x4) x5 x5 (pr0_refl 
x5))) (THead (Bind x3) x8 (THead (Flat Appl) (lift (S O) O x7) x6)) 
(pr3_head_12 c x4 x8 (pr3_pr2 c x4 x8 H24) (Bind x3) (THead (Flat Appl) (lift 
(S O) O x) x5) (THead (Flat Appl) (lift (S O) O x7) x6) (pr3_head_12 (CHead c 
(Bind x3) x8) (lift (S O) O x) (lift (S O) O x7) (pr3_lift (CHead c (Bind x3) 
x8) c (S O) O (drop_drop (Bind x3) O c c (drop_refl c) x8) x x7 (pr3_pr2 c x 
x7 H23)) (Flat Appl) x5 x6 (pr3_pr2 (CHead (CHead c (Bind x3) x8) (Flat Appl) 
(lift (S O) O x7)) x5 x6 (pr2_cflat (CHead c (Bind x3) x8) x5 x6 H25 Appl 
(lift (S O) O x7)))))) (\lambda (H32: (iso (THead (Flat Appl) x (THead (Bind 
x3) x4 x5)) (THead (Bind x3) x8 (THead (Flat Appl) (lift (S O) O x7) 
x6)))).(\lambda (P: Prop).(let H33 \def (match H32 in iso return (\lambda (t: 
T).(\lambda (t4: T).(\lambda (_: (iso t t4)).((eq T t (THead (Flat Appl) x 
(THead (Bind x3) x4 x5))) \to ((eq T t4 (THead (Bind x3) x8 (THead (Flat 
Appl) (lift (S O) O x7) x6))) \to P))))) with [(iso_sort n1 n2) \Rightarrow 
(\lambda (H33: (eq T (TSort n1) (THead (Flat Appl) x (THead (Bind x3) x4 
x5)))).(\lambda (H34: (eq T (TSort n2) (THead (Bind x3) x8 (THead (Flat Appl) 
(lift (S O) O x7) x6)))).((let H35 \def (eq_ind T (TSort n1) (\lambda (e: 
T).(match e in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow 
True | (TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow False])) I 
(THead (Flat Appl) x (THead (Bind x3) x4 x5)) H33) in (False_ind ((eq T 
(TSort n2) (THead (Bind x3) x8 (THead (Flat Appl) (lift (S O) O x7) x6))) \to 
P) H35)) H34))) | (iso_lref i1 i2) \Rightarrow (\lambda (H33: (eq T (TLRef 
i1) (THead (Flat Appl) x (THead (Bind x3) x4 x5)))).(\lambda (H34: (eq T 
(TLRef i2) (THead (Bind x3) x8 (THead (Flat Appl) (lift (S O) O x7) 
x6)))).((let H35 \def (eq_ind T (TLRef i1) (\lambda (e: T).(match e in T 
return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow True | (THead _ _ _) \Rightarrow False])) I (THead (Flat Appl) x 
(THead (Bind x3) x4 x5)) H33) in (False_ind ((eq T (TLRef i2) (THead (Bind 
x3) x8 (THead (Flat Appl) (lift (S O) O x7) x6))) \to P) H35)) H34))) | 
(iso_head v4 v5 t4 t5 k) \Rightarrow (\lambda (H33: (eq T (THead k v4 t4) 
(THead (Flat Appl) x (THead (Bind x3) x4 x5)))).(\lambda (H34: (eq T (THead k 
v5 t5) (THead (Bind x3) x8 (THead (Flat Appl) (lift (S O) O x7) x6)))).((let 
H35 \def (f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) 
with [(TSort _) \Rightarrow t4 | (TLRef _) \Rightarrow t4 | (THead _ _ t) 
\Rightarrow t])) (THead k v4 t4) (THead (Flat Appl) x (THead (Bind x3) x4 
x5)) H33) in ((let H36 \def (f_equal T T (\lambda (e: T).(match e in T return 
(\lambda (_: T).T) with [(TSort _) \Rightarrow v4 | (TLRef _) \Rightarrow v4 
| (THead _ t _) \Rightarrow t])) (THead k v4 t4) (THead (Flat Appl) x (THead 
(Bind x3) x4 x5)) H33) in ((let H37 \def (f_equal T K (\lambda (e: T).(match 
e in T return (\lambda (_: T).K) with [(TSort _) \Rightarrow k | (TLRef _) 
\Rightarrow k | (THead k0 _ _) \Rightarrow k0])) (THead k v4 t4) (THead (Flat 
Appl) x (THead (Bind x3) x4 x5)) H33) in (eq_ind K (Flat Appl) (\lambda (k0: 
K).((eq T v4 x) \to ((eq T t4 (THead (Bind x3) x4 x5)) \to ((eq T (THead k0 
v5 t5) (THead (Bind x3) x8 (THead (Flat Appl) (lift (S O) O x7) x6))) \to 
P)))) (\lambda (H38: (eq T v4 x)).(eq_ind T x (\lambda (_: T).((eq T t4 
(THead (Bind x3) x4 x5)) \to ((eq T (THead (Flat Appl) v5 t5) (THead (Bind 
x3) x8 (THead (Flat Appl) (lift (S O) O x7) x6))) \to P))) (\lambda (H39: (eq 
T t4 (THead (Bind x3) x4 x5))).(eq_ind T (THead (Bind x3) x4 x5) (\lambda (_: 
T).((eq T (THead (Flat Appl) v5 t5) (THead (Bind x3) x8 (THead (Flat Appl) 
(lift (S O) O x7) x6))) \to P)) (\lambda (H40: (eq T (THead (Flat Appl) v5 
t5) (THead (Bind x3) x8 (THead (Flat Appl) (lift (S O) O x7) x6)))).(let H41 
\def (eq_ind T (THead (Flat Appl) v5 t5) (\lambda (e: T).(match e in T return 
(\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow False | (THead k0 _ _) \Rightarrow (match k0 in K return (\lambda 
(_: K).Prop) with [(Bind _) \Rightarrow False | (Flat _) \Rightarrow 
True])])) I (THead (Bind x3) x8 (THead (Flat Appl) (lift (S O) O x7) x6)) 
H40) in (False_ind P H41))) t4 (sym_eq T t4 (THead (Bind x3) x4 x5) H39))) v4 
(sym_eq T v4 x H38))) k (sym_eq K k (Flat Appl) H37))) H36)) H35)) H34)))]) 
in (H33 (refl_equal T (THead (Flat Appl) x (THead (Bind x3) x4 x5))) 
(refl_equal T (THead (Bind x3) x8 (THead (Flat Appl) (lift (S O) O x7) 
x6)))))))) (THead (Flat Appl) x1 (THead (Bind x3) x8 (THead (Flat Appl) (lift 
(S O) O x7) x6))) (pr3_pr2 c (THead (Flat Appl) t0 (THead (Bind x3) x8 (THead 
(Flat Appl) (lift (S O) O x7) x6))) (THead (Flat Appl) x1 (THead (Bind x3) x8 
(THead (Flat Appl) (lift (S O) O x7) x6))) (pr2_head_1 c t0 x1 H15 (Flat 
Appl) (THead (Bind x3) x8 (THead (Flat Appl) (lift (S O) O x7) x6)))))))))) 
x2 H22)))))))))))))) H19)) H18)) t3 H14))))))) H13)) (\lambda (H13: (ex4_4 T 
T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T 
(THead (Flat Appl) x x0) (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t4: T).(eq T t3 (THead (Bind 
Abbr) u2 t4)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr2 c t0 u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t4: T).(\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) 
z1 t4))))))))).(ex4_4_ind T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda 
(_: T).(\lambda (_: T).(eq T (THead (Flat Appl) x x0) (THead (Bind Abst) y1 
z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t4: 
T).(eq T t3 (THead (Bind Abbr) u2 t4)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c t0 u2))))) (\lambda (_: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t4: T).(\forall (b: B).(\forall 
(u: T).(pr2 (CHead c (Bind b) u) z1 t4))))))) (sn3 c t3) (\lambda (x1: 
T).(\lambda (x2: T).(\lambda (x3: T).(\lambda (x4: T).(\lambda (H14: (eq T 
(THead (Flat Appl) x x0) (THead (Bind Abst) x1 x2))).(\lambda (H15: (eq T t3 
(THead (Bind Abbr) x3 x4))).(\lambda (_: (pr2 c t0 x3)).(\lambda (_: 
((\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) x2 x4))))).(let 
H18 \def (eq_ind T t3 (\lambda (t: T).((eq T (THead (Flat Appl) t0 (THead 
(Flat Appl) x x0)) t) \to (\forall (P: Prop).P))) H10 (THead (Bind Abbr) x3 
x4) H15) in (eq_ind_r T (THead (Bind Abbr) x3 x4) (\lambda (t: T).(sn3 c t)) 
(let H19 \def (eq_ind T (THead (Flat Appl) x x0) (\lambda (ee: T).(match ee 
in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef 
_) \Rightarrow False | (THead k _ _) \Rightarrow (match k in K return 
(\lambda (_: K).Prop) with [(Bind _) \Rightarrow False | (Flat _) \Rightarrow 
True])])) I (THead (Bind Abst) x1 x2) H14) in (False_ind (sn3 c (THead (Bind 
Abbr) x3 x4)) H19)) t3 H15)))))))))) H13)) (\lambda (H13: (ex6_6 B T T T T T 
(\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T 
(THead (Flat Appl) x x0) (THead (Bind b) y1 z1)))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda 
(y2: T).(eq T t3 (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) 
z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c t0 u2))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 c y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b) 
y2) z1 z2))))))))).(ex6_6_ind B T T T T T (\lambda (b: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B 
b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Flat Appl) x x0) (THead 
(Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T t3 (THead (Bind 
b) y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr2 c t0 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 y2))))))) 
(\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda 
(_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b) y2) z1 z2))))))) (sn3 c t3) 
(\lambda (x1: B).(\lambda (x2: T).(\lambda (x3: T).(\lambda (x4: T).(\lambda 
(x5: T).(\lambda (x6: T).(\lambda (_: (not (eq B x1 Abst))).(\lambda (H15: 
(eq T (THead (Flat Appl) x x0) (THead (Bind x1) x2 x3))).(\lambda (H16: (eq T 
t3 (THead (Bind x1) x6 (THead (Flat Appl) (lift (S O) O x5) x4)))).(\lambda 
(_: (pr2 c t0 x5)).(\lambda (_: (pr2 c x2 x6)).(\lambda (_: (pr2 (CHead c 
(Bind x1) x6) x3 x4)).(let H20 \def (eq_ind T t3 (\lambda (t: T).((eq T 
(THead (Flat Appl) t0 (THead (Flat Appl) x x0)) t) \to (\forall (P: 
Prop).P))) H10 (THead (Bind x1) x6 (THead (Flat Appl) (lift (S O) O x5) x4)) 
H16) in (eq_ind_r T (THead (Bind x1) x6 (THead (Flat Appl) (lift (S O) O x5) 
x4)) (\lambda (t: T).(sn3 c t)) (let H21 \def (eq_ind T (THead (Flat Appl) x 
x0) (\lambda (ee: T).(match ee in T return (\lambda (_: T).Prop) with [(TSort 
_) \Rightarrow False | (TLRef _) \Rightarrow False | (THead k _ _) 
\Rightarrow (match k in K return (\lambda (_: K).Prop) with [(Bind _) 
\Rightarrow False | (Flat _) \Rightarrow True])])) I (THead (Bind x1) x2 x3) 
H15) in (False_ind (sn3 c (THead (Bind x1) x6 (THead (Flat Appl) (lift (S O) 
O x5) x4))) H21)) t3 H16)))))))))))))) H13)) H12)))))))))))) v2 H4))))))))) y 
H0))))) H))))).

theorem sn3_appl_appls:
 \forall (v1: T).(\forall (t1: T).(\forall (vs: TList).(let u1 \def (THeads 
(Flat Appl) (TCons v1 vs) t1) in (\forall (c: C).((sn3 c u1) \to (\forall 
(v2: T).((sn3 c v2) \to (((\forall (u2: T).((pr3 c u1 u2) \to ((((iso u1 u2) 
\to (\forall (P: Prop).P))) \to (sn3 c (THead (Flat Appl) v2 u2)))))) \to 
(sn3 c (THead (Flat Appl) v2 u1))))))))))
\def
 \lambda (v1: T).(\lambda (t1: T).(\lambda (vs: TList).(let u1 \def (THeads 
(Flat Appl) (TCons v1 vs) t1) in (\lambda (c: C).(\lambda (H: (sn3 c (THead 
(Flat Appl) v1 (THeads (Flat Appl) vs t1)))).(\lambda (v2: T).(\lambda (H0: 
(sn3 c v2)).(\lambda (H1: ((\forall (u2: T).((pr3 c (THead (Flat Appl) v1 
(THeads (Flat Appl) vs t1)) u2) \to ((((iso (THead (Flat Appl) v1 (THeads 
(Flat Appl) vs t1)) u2) \to (\forall (P: Prop).P))) \to (sn3 c (THead (Flat 
Appl) v2 u2))))))).(sn3_appl_appl v1 (THeads (Flat Appl) vs t1) c H v2 H0 
H1))))))))).

theorem sn3_appls_lref:
 \forall (c: C).(\forall (i: nat).((nf2 c (TLRef i)) \to (\forall (us: 
TList).((sns3 c us) \to (sn3 c (THeads (Flat Appl) us (TLRef i)))))))
\def
 \lambda (c: C).(\lambda (i: nat).(\lambda (H: (nf2 c (TLRef i))).(\lambda 
(us: TList).(TList_ind (\lambda (t: TList).((sns3 c t) \to (sn3 c (THeads 
(Flat Appl) t (TLRef i))))) (\lambda (_: True).(sn3_nf2 c (TLRef i) H)) 
(\lambda (t: T).(\lambda (t0: TList).(TList_ind (\lambda (t1: TList).((((sns3 
c t1) \to (sn3 c (THeads (Flat Appl) t1 (TLRef i))))) \to ((land (sn3 c t) 
(sns3 c t1)) \to (sn3 c (THead (Flat Appl) t (THeads (Flat Appl) t1 (TLRef 
i))))))) (\lambda (_: (((sns3 c TNil) \to (sn3 c (THeads (Flat Appl) TNil 
(TLRef i)))))).(\lambda (H1: (land (sn3 c t) (sns3 c TNil))).(let H2 \def H1 
in (and_ind (sn3 c t) True (sn3 c (THead (Flat Appl) t (THeads (Flat Appl) 
TNil (TLRef i)))) (\lambda (H3: (sn3 c t)).(\lambda (_: True).(sn3_appl_lref 
c i H t H3))) H2)))) (\lambda (t1: T).(\lambda (t2: TList).(\lambda (_: 
(((((sns3 c t2) \to (sn3 c (THeads (Flat Appl) t2 (TLRef i))))) \to ((land 
(sn3 c t) (sns3 c t2)) \to (sn3 c (THead (Flat Appl) t (THeads (Flat Appl) t2 
(TLRef i)))))))).(\lambda (H1: (((sns3 c (TCons t1 t2)) \to (sn3 c (THeads 
(Flat Appl) (TCons t1 t2) (TLRef i)))))).(\lambda (H2: (land (sn3 c t) (sns3 
c (TCons t1 t2)))).(let H3 \def H2 in (and_ind (sn3 c t) (land (sn3 c t1) 
(sns3 c t2)) (sn3 c (THead (Flat Appl) t (THeads (Flat Appl) (TCons t1 t2) 
(TLRef i)))) (\lambda (H4: (sn3 c t)).(\lambda (H5: (land (sn3 c t1) (sns3 c 
t2))).(and_ind (sn3 c t1) (sns3 c t2) (sn3 c (THead (Flat Appl) t (THeads 
(Flat Appl) (TCons t1 t2) (TLRef i)))) (\lambda (H6: (sn3 c t1)).(\lambda 
(H7: (sns3 c t2)).(sn3_appl_appls t1 (TLRef i) t2 c (H1 (conj (sn3 c t1) 
(sns3 c t2) H6 H7)) t H4 (\lambda (u2: T).(\lambda (H8: (pr3 c (THeads (Flat 
Appl) (TCons t1 t2) (TLRef i)) u2)).(\lambda (H9: (((iso (THeads (Flat Appl) 
(TCons t1 t2) (TLRef i)) u2) \to (\forall (P: Prop).P)))).(H9 
(nf2_iso_appls_lref c i H (TCons t1 t2) u2 H8) (sn3 c (THead (Flat Appl) t 
u2))))))))) H5))) H3))))))) t0))) us)))).

theorem sn3_appls_cast:
 \forall (c: C).(\forall (vs: TList).(\forall (u: T).((sn3 c (THeads (Flat 
Appl) vs u)) \to (\forall (t: T).((sn3 c (THeads (Flat Appl) vs t)) \to (sn3 
c (THeads (Flat Appl) vs (THead (Flat Cast) u t))))))))
\def
 \lambda (c: C).(\lambda (vs: TList).(TList_ind (\lambda (t: TList).(\forall 
(u: T).((sn3 c (THeads (Flat Appl) t u)) \to (\forall (t0: T).((sn3 c (THeads 
(Flat Appl) t t0)) \to (sn3 c (THeads (Flat Appl) t (THead (Flat Cast) u 
t0)))))))) (\lambda (u: T).(\lambda (H: (sn3 c u)).(\lambda (t: T).(\lambda 
(H0: (sn3 c t)).(sn3_cast c u H t H0))))) (\lambda (t: T).(\lambda (t0: 
TList).(TList_ind (\lambda (t1: TList).(((\forall (u: T).((sn3 c (THeads 
(Flat Appl) t1 u)) \to (\forall (t2: T).((sn3 c (THeads (Flat Appl) t1 t2)) 
\to (sn3 c (THeads (Flat Appl) t1 (THead (Flat Cast) u t2)))))))) \to 
(\forall (u: T).((sn3 c (THead (Flat Appl) t (THeads (Flat Appl) t1 u))) \to 
(\forall (t2: T).((sn3 c (THead (Flat Appl) t (THeads (Flat Appl) t1 t2))) 
\to (sn3 c (THead (Flat Appl) t (THeads (Flat Appl) t1 (THead (Flat Cast) u 
t2)))))))))) (\lambda (_: ((\forall (u: T).((sn3 c (THeads (Flat Appl) TNil 
u)) \to (\forall (t1: T).((sn3 c (THeads (Flat Appl) TNil t1)) \to (sn3 c 
(THeads (Flat Appl) TNil (THead (Flat Cast) u t1))))))))).(\lambda (u: 
T).(\lambda (H0: (sn3 c (THead (Flat Appl) t (THeads (Flat Appl) TNil 
u)))).(\lambda (t1: T).(\lambda (H1: (sn3 c (THead (Flat Appl) t (THeads 
(Flat Appl) TNil t1)))).(sn3_appl_cast c t u H0 t1 H1)))))) (\lambda (t1: 
T).(\lambda (t2: TList).(\lambda (_: ((((\forall (u: T).((sn3 c (THeads (Flat 
Appl) t2 u)) \to (\forall (t3: T).((sn3 c (THeads (Flat Appl) t2 t3)) \to 
(sn3 c (THeads (Flat Appl) t2 (THead (Flat Cast) u t3)))))))) \to (\forall 
(u: T).((sn3 c (THead (Flat Appl) t (THeads (Flat Appl) t2 u))) \to (\forall 
(t3: T).((sn3 c (THead (Flat Appl) t (THeads (Flat Appl) t2 t3))) \to (sn3 c 
(THead (Flat Appl) t (THeads (Flat Appl) t2 (THead (Flat Cast) u 
t3))))))))))).(\lambda (H0: ((\forall (u: T).((sn3 c (THeads (Flat Appl) 
(TCons t1 t2) u)) \to (\forall (t3: T).((sn3 c (THeads (Flat Appl) (TCons t1 
t2) t3)) \to (sn3 c (THeads (Flat Appl) (TCons t1 t2) (THead (Flat Cast) u 
t3))))))))).(\lambda (u: T).(\lambda (H1: (sn3 c (THead (Flat Appl) t (THeads 
(Flat Appl) (TCons t1 t2) u)))).(\lambda (t3: T).(\lambda (H2: (sn3 c (THead 
(Flat Appl) t (THeads (Flat Appl) (TCons t1 t2) t3)))).(let H_x \def 
(sn3_gen_flat Appl c t (THeads (Flat Appl) (TCons t1 t2) t3) H2) in (let H3 
\def H_x in (and_ind (sn3 c t) (sn3 c (THeads (Flat Appl) (TCons t1 t2) t3)) 
(sn3 c (THead (Flat Appl) t (THeads (Flat Appl) (TCons t1 t2) (THead (Flat 
Cast) u t3)))) (\lambda (_: (sn3 c t)).(\lambda (H5: (sn3 c (THeads (Flat 
Appl) (TCons t1 t2) t3))).(let H6 \def H5 in (let H_x0 \def (sn3_gen_flat 
Appl c t (THeads (Flat Appl) (TCons t1 t2) u) H1) in (let H7 \def H_x0 in 
(and_ind (sn3 c t) (sn3 c (THeads (Flat Appl) (TCons t1 t2) u)) (sn3 c (THead 
(Flat Appl) t (THeads (Flat Appl) (TCons t1 t2) (THead (Flat Cast) u t3)))) 
(\lambda (H8: (sn3 c t)).(\lambda (H9: (sn3 c (THeads (Flat Appl) (TCons t1 
t2) u))).(let H10 \def H9 in (sn3_appl_appls t1 (THead (Flat Cast) u t3) t2 c 
(H0 u H10 t3 H6) t H8 (\lambda (u2: T).(\lambda (H11: (pr3 c (THeads (Flat 
Appl) (TCons t1 t2) (THead (Flat Cast) u t3)) u2)).(\lambda (H12: (((iso 
(THeads (Flat Appl) (TCons t1 t2) (THead (Flat Cast) u t3)) u2) \to (\forall 
(P: Prop).P)))).(sn3_pr3_trans c (THead (Flat Appl) t (THeads (Flat Appl) 
(TCons t1 t2) t3)) H2 (THead (Flat Appl) t u2) (pr3_thin_dx c (THeads (Flat 
Appl) (TCons t1 t2) t3) u2 (pr3_iso_appls_cast c u t3 (TCons t1 t2) u2 H11 
H12) t Appl))))))))) H7)))))) H3))))))))))) t0))) vs)).

theorem sn3_lift:
 \forall (d: C).(\forall (t: T).((sn3 d t) \to (\forall (c: C).(\forall (h: 
nat).(\forall (i: nat).((drop h i c d) \to (sn3 c (lift h i t))))))))
\def
 \lambda (d: C).(\lambda (t: T).(\lambda (H: (sn3 d t)).(sn3_ind d (\lambda 
(t0: T).(\forall (c: C).(\forall (h: nat).(\forall (i: nat).((drop h i c d) 
\to (sn3 c (lift h i t0))))))) (\lambda (t1: T).(\lambda (_: ((\forall (t2: 
T).((((eq T t1 t2) \to (\forall (P: Prop).P))) \to ((pr3 d t1 t2) \to (sn3 d 
t2)))))).(\lambda (H1: ((\forall (t2: T).((((eq T t1 t2) \to (\forall (P: 
Prop).P))) \to ((pr3 d t1 t2) \to (\forall (c: C).(\forall (h: nat).(\forall 
(i: nat).((drop h i c d) \to (sn3 c (lift h i t2))))))))))).(\lambda (c: 
C).(\lambda (h: nat).(\lambda (i: nat).(\lambda (H2: (drop h i c 
d)).(sn3_pr2_intro c (lift h i t1) (\lambda (t2: T).(\lambda (H3: (((eq T 
(lift h i t1) t2) \to (\forall (P: Prop).P)))).(\lambda (H4: (pr2 c (lift h i 
t1) t2)).(let H5 \def (pr2_gen_lift c t1 t2 h i H4 d H2) in (ex2_ind T 
(\lambda (t3: T).(eq T t2 (lift h i t3))) (\lambda (t3: T).(pr2 d t1 t3)) 
(sn3 c t2) (\lambda (x: T).(\lambda (H6: (eq T t2 (lift h i x))).(\lambda 
(H7: (pr2 d t1 x)).(let H8 \def (eq_ind T t2 (\lambda (t0: T).((eq T (lift h 
i t1) t0) \to (\forall (P: Prop).P))) H3 (lift h i x) H6) in (eq_ind_r T 
(lift h i x) (\lambda (t0: T).(sn3 c t0)) (H1 x (\lambda (H9: (eq T t1 
x)).(\lambda (P: Prop).(let H10 \def (eq_ind_r T x (\lambda (t0: T).((eq T 
(lift h i t1) (lift h i t0)) \to (\forall (P0: Prop).P0))) H8 t1 H9) in (let 
H11 \def (eq_ind_r T x (\lambda (t0: T).(pr2 d t1 t0)) H7 t1 H9) in (H10 
(refl_equal T (lift h i t1)) P))))) (pr3_pr2 d t1 x H7) c h i H2) t2 H6))))) 
H5))))))))))))) t H))).

theorem sn3_abbr:
 \forall (c: C).(\forall (d: C).(\forall (v: T).(\forall (i: nat).((getl i c 
(CHead d (Bind Abbr) v)) \to ((sn3 d v) \to (sn3 c (TLRef i)))))))
\def
 \lambda (c: C).(\lambda (d: C).(\lambda (v: T).(\lambda (i: nat).(\lambda 
(H: (getl i c (CHead d (Bind Abbr) v))).(\lambda (H0: (sn3 d 
v)).(sn3_pr2_intro c (TLRef i) (\lambda (t2: T).(\lambda (H1: (((eq T (TLRef 
i) t2) \to (\forall (P: Prop).P)))).(\lambda (H2: (pr2 c (TLRef i) t2)).(let 
H3 \def (pr2_gen_lref c t2 i H2) in (or_ind (eq T t2 (TLRef i)) (ex2_2 C T 
(\lambda (d0: C).(\lambda (u: T).(getl i c (CHead d0 (Bind Abbr) u)))) 
(\lambda (_: C).(\lambda (u: T).(eq T t2 (lift (S i) O u))))) (sn3 c t2) 
(\lambda (H4: (eq T t2 (TLRef i))).(let H5 \def (eq_ind T t2 (\lambda (t: 
T).((eq T (TLRef i) t) \to (\forall (P: Prop).P))) H1 (TLRef i) H4) in 
(eq_ind_r T (TLRef i) (\lambda (t: T).(sn3 c t)) (H5 (refl_equal T (TLRef i)) 
(sn3 c (TLRef i))) t2 H4))) (\lambda (H4: (ex2_2 C T (\lambda (d0: 
C).(\lambda (u: T).(getl i c (CHead d0 (Bind Abbr) u)))) (\lambda (_: 
C).(\lambda (u: T).(eq T t2 (lift (S i) O u)))))).(ex2_2_ind C T (\lambda 
(d0: C).(\lambda (u: T).(getl i c (CHead d0 (Bind Abbr) u)))) (\lambda (_: 
C).(\lambda (u: T).(eq T t2 (lift (S i) O u)))) (sn3 c t2) (\lambda (x0: 
C).(\lambda (x1: T).(\lambda (H5: (getl i c (CHead x0 (Bind Abbr) 
x1))).(\lambda (H6: (eq T t2 (lift (S i) O x1))).(let H7 \def (eq_ind T t2 
(\lambda (t: T).((eq T (TLRef i) t) \to (\forall (P: Prop).P))) H1 (lift (S 
i) O x1) H6) in (eq_ind_r T (lift (S i) O x1) (\lambda (t: T).(sn3 c t)) (let 
H8 \def (eq_ind C (CHead d (Bind Abbr) v) (\lambda (c0: C).(getl i c c0)) H 
(CHead x0 (Bind Abbr) x1) (getl_mono c (CHead d (Bind Abbr) v) i H (CHead x0 
(Bind Abbr) x1) H5)) in (let H9 \def (f_equal C C (\lambda (e: C).(match e in 
C return (\lambda (_: C).C) with [(CSort _) \Rightarrow d | (CHead c0 _ _) 
\Rightarrow c0])) (CHead d (Bind Abbr) v) (CHead x0 (Bind Abbr) x1) 
(getl_mono c (CHead d (Bind Abbr) v) i H (CHead x0 (Bind Abbr) x1) H5)) in 
((let H10 \def (f_equal C T (\lambda (e: C).(match e in C return (\lambda (_: 
C).T) with [(CSort _) \Rightarrow v | (CHead _ _ t) \Rightarrow t])) (CHead d 
(Bind Abbr) v) (CHead x0 (Bind Abbr) x1) (getl_mono c (CHead d (Bind Abbr) v) 
i H (CHead x0 (Bind Abbr) x1) H5)) in (\lambda (H11: (eq C d x0)).(let H12 
\def (eq_ind_r T x1 (\lambda (t: T).(getl i c (CHead x0 (Bind Abbr) t))) H8 v 
H10) in (eq_ind T v (\lambda (t: T).(sn3 c (lift (S i) O t))) (let H13 \def 
(eq_ind_r C x0 (\lambda (c0: C).(getl i c (CHead c0 (Bind Abbr) v))) H12 d 
H11) in (sn3_lift d v H0 c (S i) O (getl_drop Abbr c d v i H13))) x1 H10)))) 
H9))) t2 H6)))))) H4)) H3))))))))))).

theorem sns3_lifts:
 \forall (c: C).(\forall (d: C).(\forall (h: nat).(\forall (i: nat).((drop h 
i c d) \to (\forall (ts: TList).((sns3 d ts) \to (sns3 c (lifts h i ts))))))))
\def
 \lambda (c: C).(\lambda (d: C).(\lambda (h: nat).(\lambda (i: nat).(\lambda 
(H: (drop h i c d)).(\lambda (ts: TList).(TList_ind (\lambda (t: 
TList).((sns3 d t) \to (sns3 c (lifts h i t)))) (\lambda (H0: True).H0) 
(\lambda (t: T).(\lambda (t0: TList).(\lambda (H0: (((sns3 d t0) \to (sns3 c 
(lifts h i t0))))).(\lambda (H1: (land (sn3 d t) (sns3 d t0))).(let H2 \def 
H1 in (and_ind (sn3 d t) (sns3 d t0) (land (sn3 c (lift h i t)) (sns3 c 
(lifts h i t0))) (\lambda (H3: (sn3 d t)).(\lambda (H4: (sns3 d t0)).(conj 
(sn3 c (lift h i t)) (sns3 c (lifts h i t0)) (sn3_lift d t H3 c h i H) (H0 
H4)))) H2)))))) ts)))))).

