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

include "Basic-1/ty3/arity_props.ma".

include "Basic-1/nf2/fwd.ma".

theorem pc3_dec:
 \forall (g: G).(\forall (c: C).(\forall (u1: T).(\forall (t1: T).((ty3 g c 
u1 t1) \to (\forall (u2: T).(\forall (t2: T).((ty3 g c u2 t2) \to (or (pc3 c 
u1 u2) ((pc3 c u1 u2) \to False)))))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (u1: T).(\lambda (t1: T).(\lambda 
(H: (ty3 g c u1 t1)).(\lambda (u2: T).(\lambda (t2: T).(\lambda (H0: (ty3 g c 
u2 t2)).(let H_y \def (ty3_sn3 g c u1 t1 H) in (let H_y0 \def (ty3_sn3 g c u2 
t2 H0) in (let H_x \def (nf2_sn3 c u1 H_y) in (let H1 \def H_x in (ex2_ind T 
(\lambda (u: T).(pr3 c u1 u)) (\lambda (u: T).(nf2 c u)) (or (pc3 c u1 u2) 
((pc3 c u1 u2) \to False)) (\lambda (x: T).(\lambda (H2: (pr3 c u1 
x)).(\lambda (H3: (nf2 c x)).(let H_x0 \def (nf2_sn3 c u2 H_y0) in (let H4 
\def H_x0 in (ex2_ind T (\lambda (u: T).(pr3 c u2 u)) (\lambda (u: T).(nf2 c 
u)) (or (pc3 c u1 u2) ((pc3 c u1 u2) \to False)) (\lambda (x0: T).(\lambda 
(H5: (pr3 c u2 x0)).(\lambda (H6: (nf2 c x0)).(let H_x1 \def (term_dec x x0) 
in (let H7 \def H_x1 in (or_ind (eq T x x0) ((eq T x x0) \to (\forall (P: 
Prop).P)) (or (pc3 c u1 u2) ((pc3 c u1 u2) \to False)) (\lambda (H8: (eq T x 
x0)).(let H9 \def (eq_ind_r T x0 (\lambda (t: T).(nf2 c t)) H6 x H8) in (let 
H10 \def (eq_ind_r T x0 (\lambda (t: T).(pr3 c u2 t)) H5 x H8) in (or_introl 
(pc3 c u1 u2) ((pc3 c u1 u2) \to False) (pc3_pr3_t c u1 x H2 u2 H10))))) 
(\lambda (H8: (((eq T x x0) \to (\forall (P: Prop).P)))).(or_intror (pc3 c u1 
u2) ((pc3 c u1 u2) \to False) (\lambda (H9: (pc3 c u1 u2)).(let H10 \def H9 
in (ex2_ind T (\lambda (t: T).(pr3 c u1 t)) (\lambda (t: T).(pr3 c u2 t)) 
False (\lambda (x1: T).(\lambda (H11: (pr3 c u1 x1)).(\lambda (H12: (pr3 c u2 
x1)).(let H_x2 \def (pr3_confluence c u2 x0 H5 x1 H12) in (let H13 \def H_x2 
in (ex2_ind T (\lambda (t: T).(pr3 c x0 t)) (\lambda (t: T).(pr3 c x1 t)) 
False (\lambda (x2: T).(\lambda (H14: (pr3 c x0 x2)).(\lambda (H15: (pr3 c x1 
x2)).(let H_y1 \def (nf2_pr3_unfold c x0 x2 H14 H6) in (let H16 \def 
(eq_ind_r T x2 (\lambda (t: T).(pr3 c x1 t)) H15 x0 H_y1) in (let H17 \def 
(nf2_pr3_confluence c x H3 x0 H6 u1 H2) in (H8 (H17 (pr3_t x1 u1 c H11 x0 
H16)) False))))))) H13)))))) H10))))) H7)))))) H4)))))) H1)))))))))))).
(* COMMENTS
Initial nodes: 551
END *)

theorem pc3_abst_dec:
 \forall (g: G).(\forall (c: C).(\forall (u1: T).(\forall (t1: T).((ty3 g c 
u1 t1) \to (\forall (u2: T).(\forall (t2: T).((ty3 g c u2 t2) \to (or (ex4_2 
T T (\lambda (u: T).(\lambda (_: T).(pc3 c u1 (THead (Bind Abst) u2 u)))) 
(\lambda (u: T).(\lambda (v2: T).(ty3 g c (THead (Bind Abst) v2 u) t1))) 
(\lambda (_: T).(\lambda (v2: T).(pr3 c u2 v2))) (\lambda (_: T).(\lambda 
(v2: T).(nf2 c v2)))) (\forall (u: T).((pc3 c u1 (THead (Bind Abst) u2 u)) 
\to False))))))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (u1: T).(\lambda (t1: T).(\lambda 
(H: (ty3 g c u1 t1)).(\lambda (u2: T).(\lambda (t2: T).(\lambda (H0: (ty3 g c 
u2 t2)).(let H1 \def (ty3_sn3 g c u1 t1 H) in (let H2 \def (ty3_sn3 g c u2 t2 
H0) in (let H_x \def (nf2_sn3 c u1 H1) in (let H3 \def H_x in (ex2_ind T 
(\lambda (u: T).(pr3 c u1 u)) (\lambda (u: T).(nf2 c u)) (or (ex4_2 T T 
(\lambda (u: T).(\lambda (_: T).(pc3 c u1 (THead (Bind Abst) u2 u)))) 
(\lambda (u: T).(\lambda (v2: T).(ty3 g c (THead (Bind Abst) v2 u) t1))) 
(\lambda (_: T).(\lambda (v2: T).(pr3 c u2 v2))) (\lambda (_: T).(\lambda 
(v2: T).(nf2 c v2)))) (\forall (u: T).((pc3 c u1 (THead (Bind Abst) u2 u)) 
\to False))) (\lambda (x: T).(\lambda (H4: (pr3 c u1 x)).(\lambda (H5: (nf2 c 
x)).(let H_x0 \def (nf2_sn3 c u2 H2) in (let H6 \def H_x0 in (ex2_ind T 
(\lambda (u: T).(pr3 c u2 u)) (\lambda (u: T).(nf2 c u)) (or (ex4_2 T T 
(\lambda (u: T).(\lambda (_: T).(pc3 c u1 (THead (Bind Abst) u2 u)))) 
(\lambda (u: T).(\lambda (v2: T).(ty3 g c (THead (Bind Abst) v2 u) t1))) 
(\lambda (_: T).(\lambda (v2: T).(pr3 c u2 v2))) (\lambda (_: T).(\lambda 
(v2: T).(nf2 c v2)))) (\forall (u: T).((pc3 c u1 (THead (Bind Abst) u2 u)) 
\to False))) (\lambda (x0: T).(\lambda (H7: (pr3 c u2 x0)).(\lambda (H8: (nf2 
c x0)).(let H_x1 \def (abst_dec x x0) in (let H9 \def H_x1 in (or_ind (ex T 
(\lambda (t: T).(eq T x (THead (Bind Abst) x0 t)))) (\forall (t: T).((eq T x 
(THead (Bind Abst) x0 t)) \to (\forall (P: Prop).P))) (or (ex4_2 T T (\lambda 
(u: T).(\lambda (_: T).(pc3 c u1 (THead (Bind Abst) u2 u)))) (\lambda (u: 
T).(\lambda (v2: T).(ty3 g c (THead (Bind Abst) v2 u) t1))) (\lambda (_: 
T).(\lambda (v2: T).(pr3 c u2 v2))) (\lambda (_: T).(\lambda (v2: T).(nf2 c 
v2)))) (\forall (u: T).((pc3 c u1 (THead (Bind Abst) u2 u)) \to False))) 
(\lambda (H10: (ex T (\lambda (t: T).(eq T x (THead (Bind Abst) x0 
t))))).(ex_ind T (\lambda (t: T).(eq T x (THead (Bind Abst) x0 t))) (or 
(ex4_2 T T (\lambda (u: T).(\lambda (_: T).(pc3 c u1 (THead (Bind Abst) u2 
u)))) (\lambda (u: T).(\lambda (v2: T).(ty3 g c (THead (Bind Abst) v2 u) 
t1))) (\lambda (_: T).(\lambda (v2: T).(pr3 c u2 v2))) (\lambda (_: 
T).(\lambda (v2: T).(nf2 c v2)))) (\forall (u: T).((pc3 c u1 (THead (Bind 
Abst) u2 u)) \to False))) (\lambda (x1: T).(\lambda (H11: (eq T x (THead 
(Bind Abst) x0 x1))).(let H12 \def (eq_ind T x (\lambda (t: T).(nf2 c t)) H5 
(THead (Bind Abst) x0 x1) H11) in (let H13 \def (eq_ind T x (\lambda (t: 
T).(pr3 c u1 t)) H4 (THead (Bind Abst) x0 x1) H11) in (let H_y \def 
(ty3_sred_pr3 c u1 (THead (Bind Abst) x0 x1) H13 g t1 H) in (or_introl (ex4_2 
T T (\lambda (u: T).(\lambda (_: T).(pc3 c u1 (THead (Bind Abst) u2 u)))) 
(\lambda (u: T).(\lambda (v2: T).(ty3 g c (THead (Bind Abst) v2 u) t1))) 
(\lambda (_: T).(\lambda (v2: T).(pr3 c u2 v2))) (\lambda (_: T).(\lambda 
(v2: T).(nf2 c v2)))) (\forall (u: T).((pc3 c u1 (THead (Bind Abst) u2 u)) 
\to False)) (ex4_2_intro T T (\lambda (u: T).(\lambda (_: T).(pc3 c u1 (THead 
(Bind Abst) u2 u)))) (\lambda (u: T).(\lambda (v2: T).(ty3 g c (THead (Bind 
Abst) v2 u) t1))) (\lambda (_: T).(\lambda (v2: T).(pr3 c u2 v2))) (\lambda 
(_: T).(\lambda (v2: T).(nf2 c v2))) x1 x0 (pc3_pr3_t c u1 (THead (Bind Abst) 
x0 x1) H13 (THead (Bind Abst) u2 x1) (pr3_head_12 c u2 x0 H7 (Bind Abst) x1 
x1 (pr3_refl (CHead c (Bind Abst) x0) x1))) H_y H7 H8))))))) H10)) (\lambda 
(H10: ((\forall (t: T).((eq T x (THead (Bind Abst) x0 t)) \to (\forall (P: 
Prop).P))))).(or_intror (ex4_2 T T (\lambda (u: T).(\lambda (_: T).(pc3 c u1 
(THead (Bind Abst) u2 u)))) (\lambda (u: T).(\lambda (v2: T).(ty3 g c (THead 
(Bind Abst) v2 u) t1))) (\lambda (_: T).(\lambda (v2: T).(pr3 c u2 v2))) 
(\lambda (_: T).(\lambda (v2: T).(nf2 c v2)))) (\forall (u: T).((pc3 c u1 
(THead (Bind Abst) u2 u)) \to False)) (\lambda (u: T).(\lambda (H11: (pc3 c 
u1 (THead (Bind Abst) u2 u))).(let H12 \def H11 in (ex2_ind T (\lambda (t: 
T).(pr3 c u1 t)) (\lambda (t: T).(pr3 c (THead (Bind Abst) u2 u) t)) False 
(\lambda (x1: T).(\lambda (H13: (pr3 c u1 x1)).(\lambda (H14: (pr3 c (THead 
(Bind Abst) u2 u) x1)).(ex2_ind T (\lambda (t: T).(pr3 c x1 t)) (\lambda (t: 
T).(pr3 c x t)) False (\lambda (x2: T).(\lambda (H15: (pr3 c x1 x2)).(\lambda 
(H16: (pr3 c x x2)).(let H_y \def (nf2_pr3_unfold c x x2 H16 H5) in (let H17 
\def (eq_ind_r T x2 (\lambda (t: T).(pr3 c x1 t)) H15 x H_y) in (let H18 \def 
(pr3_gen_abst c u2 u x1 H14) in (ex3_2_ind T T (\lambda (u3: T).(\lambda (t3: 
T).(eq T x1 (THead (Bind Abst) u3 t3)))) (\lambda (u3: T).(\lambda (_: 
T).(pr3 c u2 u3))) (\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall 
(u0: T).(pr3 (CHead c (Bind b) u0) u t3))))) False (\lambda (x3: T).(\lambda 
(x4: T).(\lambda (H19: (eq T x1 (THead (Bind Abst) x3 x4))).(\lambda (H20: 
(pr3 c u2 x3)).(\lambda (_: ((\forall (b: B).(\forall (u0: T).(pr3 (CHead c 
(Bind b) u0) u x4))))).(let H22 \def (eq_ind T x1 (\lambda (t: T).(pr3 c t 
x)) H17 (THead (Bind Abst) x3 x4) H19) in (let H23 \def (pr3_gen_abst c x3 x4 
x H22) in (ex3_2_ind T T (\lambda (u3: T).(\lambda (t3: T).(eq T x (THead 
(Bind Abst) u3 t3)))) (\lambda (u3: T).(\lambda (_: T).(pr3 c x3 u3))) 
(\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall (u0: T).(pr3 (CHead 
c (Bind b) u0) x4 t3))))) False (\lambda (x5: T).(\lambda (x6: T).(\lambda 
(H24: (eq T x (THead (Bind Abst) x5 x6))).(\lambda (H25: (pr3 c x3 
x5)).(\lambda (_: ((\forall (b: B).(\forall (u0: T).(pr3 (CHead c (Bind b) 
u0) x4 x6))))).(let H27 \def (eq_ind T x (\lambda (t: T).(\forall (t0: 
T).((eq T t (THead (Bind Abst) x0 t0)) \to (\forall (P: Prop).P)))) H10 
(THead (Bind Abst) x5 x6) H24) in (let H28 \def (eq_ind T x (\lambda (t: 
T).(nf2 c t)) H5 (THead (Bind Abst) x5 x6) H24) in (let H29 \def 
(nf2_gen_abst c x5 x6 H28) in (land_ind (nf2 c x5) (nf2 (CHead c (Bind Abst) 
x5) x6) False (\lambda (H30: (nf2 c x5)).(\lambda (_: (nf2 (CHead c (Bind 
Abst) x5) x6)).(let H32 \def (nf2_pr3_confluence c x0 H8 x5 H30 u2 H7) in 
(H27 x6 (sym_eq T (THead (Bind Abst) x0 x6) (THead (Bind Abst) x5 x6) 
(f_equal3 K T T T THead (Bind Abst) (Bind Abst) x0 x5 x6 x6 (refl_equal K 
(Bind Abst)) (H32 (pr3_t x3 u2 c H20 x5 H25)) (refl_equal T x6))) False)))) 
H29))))))))) H23)))))))) H18))))))) (pr3_confluence c u1 x1 H13 x H4))))) 
H12)))))) H9)))))) H6)))))) H3)))))))))))).
(* COMMENTS
Initial nodes: 1759
END *)

