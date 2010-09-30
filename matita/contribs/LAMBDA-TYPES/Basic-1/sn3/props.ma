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

include "Basic-1/sn3/nf2.ma".

include "Basic-1/sn3/fwd.ma".

include "Basic-1/nf2/iso.ma".

include "Basic-1/pr3/iso.ma".

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
(* COMMENTS
Initial nodes: 289
END *)

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
(* COMMENTS
Initial nodes: 467
END *)

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
(* COMMENTS
Initial nodes: 1239
END *)

theorem sn3_cflat:
 \forall (c: C).(\forall (t: T).((sn3 c t) \to (\forall (f: F).(\forall (u: 
T).(sn3 (CHead c (Flat f) u) t)))))
\def
 \lambda (c: C).(\lambda (t: T).(\lambda (H: (sn3 c t)).(\lambda (f: 
F).(\lambda (u: T).(sn3_ind c (\lambda (t0: T).(sn3 (CHead c (Flat f) u) t0)) 
(\lambda (t1: T).(\lambda (_: ((\forall (t2: T).((((eq T t1 t2) \to (\forall 
(P: Prop).P))) \to ((pr3 c t1 t2) \to (sn3 c t2)))))).(\lambda (H1: ((\forall 
(t2: T).((((eq T t1 t2) \to (\forall (P: Prop).P))) \to ((pr3 c t1 t2) \to 
(sn3 (CHead c (Flat f) u) t2)))))).(sn3_pr2_intro (CHead c (Flat f) u) t1 
(\lambda (t2: T).(\lambda (H2: (((eq T t1 t2) \to (\forall (P: 
Prop).P)))).(\lambda (H3: (pr2 (CHead c (Flat f) u) t1 t2)).(H1 t2 H2 
(pr3_pr2 c t1 t2 (pr2_gen_cflat f c u t1 t2 H3)))))))))) t H))))).
(* COMMENTS
Initial nodes: 175
END *)

theorem sn3_shift:
 \forall (b: B).(\forall (c: C).(\forall (v: T).(\forall (t: T).((sn3 c 
(THead (Bind b) v t)) \to (sn3 (CHead c (Bind b) v) t)))))
\def
 \lambda (b: B).(\lambda (c: C).(\lambda (v: T).(\lambda (t: T).(\lambda (H: 
(sn3 c (THead (Bind b) v t))).(let H_x \def (sn3_gen_bind b c v t H) in (let 
H0 \def H_x in (land_ind (sn3 c v) (sn3 (CHead c (Bind b) v) t) (sn3 (CHead c 
(Bind b) v) t) (\lambda (_: (sn3 c v)).(\lambda (H2: (sn3 (CHead c (Bind b) 
v) t)).H2)) H0))))))).
(* COMMENTS
Initial nodes: 95
END *)

theorem sn3_change:
 \forall (b: B).((not (eq B b Abbr)) \to (\forall (c: C).(\forall (v1: 
T).(\forall (t: T).((sn3 (CHead c (Bind b) v1) t) \to (\forall (v2: T).(sn3 
(CHead c (Bind b) v2) t)))))))
\def
 \lambda (b: B).(\lambda (H: (not (eq B b Abbr))).(\lambda (c: C).(\lambda 
(v1: T).(\lambda (t: T).(\lambda (H0: (sn3 (CHead c (Bind b) v1) t)).(\lambda 
(v2: T).(sn3_ind (CHead c (Bind b) v1) (\lambda (t0: T).(sn3 (CHead c (Bind 
b) v2) t0)) (\lambda (t1: T).(\lambda (_: ((\forall (t2: T).((((eq T t1 t2) 
\to (\forall (P: Prop).P))) \to ((pr3 (CHead c (Bind b) v1) t1 t2) \to (sn3 
(CHead c (Bind b) v1) t2)))))).(\lambda (H2: ((\forall (t2: T).((((eq T t1 
t2) \to (\forall (P: Prop).P))) \to ((pr3 (CHead c (Bind b) v1) t1 t2) \to 
(sn3 (CHead c (Bind b) v2) t2)))))).(sn3_pr2_intro (CHead c (Bind b) v2) t1 
(\lambda (t2: T).(\lambda (H3: (((eq T t1 t2) \to (\forall (P: 
Prop).P)))).(\lambda (H4: (pr2 (CHead c (Bind b) v2) t1 t2)).(H2 t2 H3 
(pr3_pr2 (CHead c (Bind b) v1) t1 t2 (pr2_change b H c v2 t1 t2 H4 
v1)))))))))) t H0))))))).
(* COMMENTS
Initial nodes: 239
END *)

theorem sn3_gen_def:
 \forall (c: C).(\forall (d: C).(\forall (v: T).(\forall (i: nat).((getl i c 
(CHead d (Bind Abbr) v)) \to ((sn3 c (TLRef i)) \to (sn3 d v))))))
\def
 \lambda (c: C).(\lambda (d: C).(\lambda (v: T).(\lambda (i: nat).(\lambda 
(H: (getl i c (CHead d (Bind Abbr) v))).(\lambda (H0: (sn3 c (TLRef 
i))).(sn3_gen_lift c v (S i) O (sn3_pr3_trans c (TLRef i) H0 (lift (S i) O v) 
(pr3_pr2 c (TLRef i) (lift (S i) O v) (pr2_delta c d v i H (TLRef i) (TLRef 
i) (pr0_refl (TLRef i)) (lift (S i) O v) (subst0_lref v i)))) d (getl_drop 
Abbr c d v i H))))))).
(* COMMENTS
Initial nodes: 139
END *)

theorem sn3_cdelta:
 \forall (v: T).(\forall (t: T).(\forall (i: nat).(((\forall (w: T).(ex T 
(\lambda (u: T).(subst0 i w t u))))) \to (\forall (c: C).(\forall (d: 
C).((getl i c (CHead d (Bind Abbr) v)) \to ((sn3 c t) \to (sn3 d v))))))))
\def
 \lambda (v: T).(\lambda (t: T).(\lambda (i: nat).(\lambda (H: ((\forall (w: 
T).(ex T (\lambda (u: T).(subst0 i w t u)))))).(let H_x \def (H v) in (let H0 
\def H_x in (ex_ind T (\lambda (u: T).(subst0 i v t u)) (\forall (c: 
C).(\forall (d: C).((getl i c (CHead d (Bind Abbr) v)) \to ((sn3 c t) \to 
(sn3 d v))))) (\lambda (x: T).(\lambda (H1: (subst0 i v t x)).(subst0_ind 
(\lambda (n: nat).(\lambda (t0: T).(\lambda (t1: T).(\lambda (_: T).(\forall 
(c: C).(\forall (d: C).((getl n c (CHead d (Bind Abbr) t0)) \to ((sn3 c t1) 
\to (sn3 d t0))))))))) (\lambda (v0: T).(\lambda (i0: nat).(\lambda (c: 
C).(\lambda (d: C).(\lambda (H2: (getl i0 c (CHead d (Bind Abbr) 
v0))).(\lambda (H3: (sn3 c (TLRef i0))).(sn3_gen_def c d v0 i0 H2 H3))))))) 
(\lambda (v0: T).(\lambda (u2: T).(\lambda (u1: T).(\lambda (i0: 
nat).(\lambda (_: (subst0 i0 v0 u1 u2)).(\lambda (H3: ((\forall (c: 
C).(\forall (d: C).((getl i0 c (CHead d (Bind Abbr) v0)) \to ((sn3 c u1) \to 
(sn3 d v0))))))).(\lambda (t0: T).(\lambda (k: K).(\lambda (c: C).(\lambda 
(d: C).(\lambda (H4: (getl i0 c (CHead d (Bind Abbr) v0))).(\lambda (H5: (sn3 
c (THead k u1 t0))).(let H_y \def (sn3_gen_head k c u1 t0 H5) in (H3 c d H4 
H_y)))))))))))))) (\lambda (k: K).(\lambda (v0: T).(\lambda (t2: T).(\lambda 
(t1: T).(\lambda (i0: nat).(\lambda (H2: (subst0 (s k i0) v0 t1 t2)).(\lambda 
(H3: ((\forall (c: C).(\forall (d: C).((getl (s k i0) c (CHead d (Bind Abbr) 
v0)) \to ((sn3 c t1) \to (sn3 d v0))))))).(\lambda (u: T).(\lambda (c: 
C).(\lambda (d: C).(\lambda (H4: (getl i0 c (CHead d (Bind Abbr) 
v0))).(\lambda (H5: (sn3 c (THead k u t1))).(K_ind (\lambda (k0: K).((subst0 
(s k0 i0) v0 t1 t2) \to (((\forall (c0: C).(\forall (d0: C).((getl (s k0 i0) 
c0 (CHead d0 (Bind Abbr) v0)) \to ((sn3 c0 t1) \to (sn3 d0 v0)))))) \to ((sn3 
c (THead k0 u t1)) \to (sn3 d v0))))) (\lambda (b: B).(\lambda (_: (subst0 (s 
(Bind b) i0) v0 t1 t2)).(\lambda (H7: ((\forall (c0: C).(\forall (d0: 
C).((getl (s (Bind b) i0) c0 (CHead d0 (Bind Abbr) v0)) \to ((sn3 c0 t1) \to 
(sn3 d0 v0))))))).(\lambda (H8: (sn3 c (THead (Bind b) u t1))).(let H_x0 \def 
(sn3_gen_bind b c u t1 H8) in (let H9 \def H_x0 in (land_ind (sn3 c u) (sn3 
(CHead c (Bind b) u) t1) (sn3 d v0) (\lambda (_: (sn3 c u)).(\lambda (H11: 
(sn3 (CHead c (Bind b) u) t1)).(H7 (CHead c (Bind b) u) d (getl_clear_bind b 
(CHead c (Bind b) u) c u (clear_bind b c u) (CHead d (Bind Abbr) v0) i0 H4) 
H11))) H9))))))) (\lambda (f: F).(\lambda (_: (subst0 (s (Flat f) i0) v0 t1 
t2)).(\lambda (H7: ((\forall (c0: C).(\forall (d0: C).((getl (s (Flat f) i0) 
c0 (CHead d0 (Bind Abbr) v0)) \to ((sn3 c0 t1) \to (sn3 d0 v0))))))).(\lambda 
(H8: (sn3 c (THead (Flat f) u t1))).(let H_x0 \def (sn3_gen_flat f c u t1 H8) 
in (let H9 \def H_x0 in (land_ind (sn3 c u) (sn3 c t1) (sn3 d v0) (\lambda 
(_: (sn3 c u)).(\lambda (H11: (sn3 c t1)).(H7 c d H4 H11))) H9))))))) k H2 H3 
H5))))))))))))) (\lambda (v0: T).(\lambda (u1: T).(\lambda (u2: T).(\lambda 
(i0: nat).(\lambda (_: (subst0 i0 v0 u1 u2)).(\lambda (H3: ((\forall (c: 
C).(\forall (d: C).((getl i0 c (CHead d (Bind Abbr) v0)) \to ((sn3 c u1) \to 
(sn3 d v0))))))).(\lambda (k: K).(\lambda (t1: T).(\lambda (t2: T).(\lambda 
(_: (subst0 (s k i0) v0 t1 t2)).(\lambda (_: ((\forall (c: C).(\forall (d: 
C).((getl (s k i0) c (CHead d (Bind Abbr) v0)) \to ((sn3 c t1) \to (sn3 d 
v0))))))).(\lambda (c: C).(\lambda (d: C).(\lambda (H6: (getl i0 c (CHead d 
(Bind Abbr) v0))).(\lambda (H7: (sn3 c (THead k u1 t1))).(let H_y \def 
(sn3_gen_head k c u1 t1 H7) in (H3 c d H6 H_y))))))))))))))))) i v t x H1))) 
H0)))))).
(* COMMENTS
Initial nodes: 949
END *)

theorem sn3_cpr3_trans:
 \forall (c: C).(\forall (u1: T).(\forall (u2: T).((pr3 c u1 u2) \to (\forall 
(k: K).(\forall (t: T).((sn3 (CHead c k u1) t) \to (sn3 (CHead c k u2) 
t)))))))
\def
 \lambda (c: C).(\lambda (u1: T).(\lambda (u2: T).(\lambda (H: (pr3 c u1 
u2)).(\lambda (k: K).(\lambda (t: T).(\lambda (H0: (sn3 (CHead c k u1) 
t)).(sn3_ind (CHead c k u1) (\lambda (t0: T).(sn3 (CHead c k u2) t0)) 
(\lambda (t1: T).(\lambda (_: ((\forall (t2: T).((((eq T t1 t2) \to (\forall 
(P: Prop).P))) \to ((pr3 (CHead c k u1) t1 t2) \to (sn3 (CHead c k u1) 
t2)))))).(\lambda (H2: ((\forall (t2: T).((((eq T t1 t2) \to (\forall (P: 
Prop).P))) \to ((pr3 (CHead c k u1) t1 t2) \to (sn3 (CHead c k u2) 
t2)))))).(sn3_sing (CHead c k u2) t1 (\lambda (t2: T).(\lambda (H3: (((eq T 
t1 t2) \to (\forall (P: Prop).P)))).(\lambda (H4: (pr3 (CHead c k u2) t1 
t2)).(H2 t2 H3 (pr3_pr3_pr3_t c u1 u2 H t1 t2 k H4))))))))) t H0))))))).
(* COMMENTS
Initial nodes: 203
END *)

theorem sn3_bind:
 \forall (b: B).(\forall (c: C).(\forall (u: T).((sn3 c u) \to (\forall (t: 
T).((sn3 (CHead c (Bind b) u) t) \to (sn3 c (THead (Bind b) u t)))))))
\def
 \lambda (b: B).(\lambda (c: C).(\lambda (u: T).(\lambda (H: (sn3 c 
u)).(sn3_ind c (\lambda (t: T).(\forall (t0: T).((sn3 (CHead c (Bind b) t) 
t0) \to (sn3 c (THead (Bind b) t t0))))) (\lambda (t1: T).(\lambda (_: 
((\forall (t2: T).((((eq T t1 t2) \to (\forall (P: Prop).P))) \to ((pr3 c t1 
t2) \to (sn3 c t2)))))).(\lambda (H1: ((\forall (t2: T).((((eq T t1 t2) \to 
(\forall (P: Prop).P))) \to ((pr3 c t1 t2) \to (\forall (t: T).((sn3 (CHead c 
(Bind b) t2) t) \to (sn3 c (THead (Bind b) t2 t))))))))).(\lambda (t: 
T).(\lambda (H2: (sn3 (CHead c (Bind b) t1) t)).(sn3_ind (CHead c (Bind b) 
t1) (\lambda (t0: T).(sn3 c (THead (Bind b) t1 t0))) (\lambda (t2: 
T).(\lambda (H3: ((\forall (t3: T).((((eq T t2 t3) \to (\forall (P: 
Prop).P))) \to ((pr3 (CHead c (Bind b) t1) t2 t3) \to (sn3 (CHead c (Bind b) 
t1) t3)))))).(\lambda (H4: ((\forall (t3: T).((((eq T t2 t3) \to (\forall (P: 
Prop).P))) \to ((pr3 (CHead c (Bind b) t1) t2 t3) \to (sn3 c (THead (Bind b) 
t1 t3))))))).(sn3_sing c (THead (Bind b) t1 t2) (\lambda (t3: T).(\lambda 
(H5: (((eq T (THead (Bind b) t1 t2) t3) \to (\forall (P: Prop).P)))).(\lambda 
(H6: (pr3 c (THead (Bind b) t1 t2) t3)).(let H_x \def (bind_dec_not b Abst) 
in (let H7 \def H_x in (or_ind (eq B b Abst) (not (eq B b Abst)) (sn3 c t3) 
(\lambda (H8: (eq B b Abst)).(let H9 \def (eq_ind B b (\lambda (b0: B).(pr3 c 
(THead (Bind b0) t1 t2) t3)) H6 Abst H8) in (let H10 \def (eq_ind B b 
(\lambda (b0: B).((eq T (THead (Bind b0) t1 t2) t3) \to (\forall (P: 
Prop).P))) H5 Abst H8) in (let H11 \def (eq_ind B b (\lambda (b0: B).(\forall 
(t4: T).((((eq T t2 t4) \to (\forall (P: Prop).P))) \to ((pr3 (CHead c (Bind 
b0) t1) t2 t4) \to (sn3 c (THead (Bind b0) t1 t4)))))) H4 Abst H8) in (let 
H12 \def (eq_ind B b (\lambda (b0: B).(\forall (t4: T).((((eq T t2 t4) \to 
(\forall (P: Prop).P))) \to ((pr3 (CHead c (Bind b0) t1) t2 t4) \to (sn3 
(CHead c (Bind b0) t1) t4))))) H3 Abst H8) in (let H13 \def (eq_ind B b 
(\lambda (b0: B).(\forall (t4: T).((((eq T t1 t4) \to (\forall (P: Prop).P))) 
\to ((pr3 c t1 t4) \to (\forall (t0: T).((sn3 (CHead c (Bind b0) t4) t0) \to 
(sn3 c (THead (Bind b0) t4 t0)))))))) H1 Abst H8) in (let H14 \def 
(pr3_gen_abst c t1 t2 t3 H9) in (ex3_2_ind T T (\lambda (u2: T).(\lambda (t4: 
T).(eq T t3 (THead (Bind Abst) u2 t4)))) (\lambda (u2: T).(\lambda (_: 
T).(pr3 c t1 u2))) (\lambda (_: T).(\lambda (t4: T).(\forall (b0: B).(\forall 
(u0: T).(pr3 (CHead c (Bind b0) u0) t2 t4))))) (sn3 c t3) (\lambda (x0: 
T).(\lambda (x1: T).(\lambda (H15: (eq T t3 (THead (Bind Abst) x0 
x1))).(\lambda (H16: (pr3 c t1 x0)).(\lambda (H17: ((\forall (b0: B).(\forall 
(u0: T).(pr3 (CHead c (Bind b0) u0) t2 x1))))).(let H18 \def (eq_ind T t3 
(\lambda (t0: T).((eq T (THead (Bind Abst) t1 t2) t0) \to (\forall (P: 
Prop).P))) H10 (THead (Bind Abst) x0 x1) H15) in (eq_ind_r T (THead (Bind 
Abst) x0 x1) (\lambda (t0: T).(sn3 c t0)) (let H_x0 \def (term_dec t1 x0) in 
(let H19 \def H_x0 in (or_ind (eq T t1 x0) ((eq T t1 x0) \to (\forall (P: 
Prop).P)) (sn3 c (THead (Bind Abst) x0 x1)) (\lambda (H20: (eq T t1 x0)).(let 
H21 \def (eq_ind_r T x0 (\lambda (t0: T).((eq T (THead (Bind Abst) t1 t2) 
(THead (Bind Abst) t0 x1)) \to (\forall (P: Prop).P))) H18 t1 H20) in (let 
H22 \def (eq_ind_r T x0 (\lambda (t0: T).(pr3 c t1 t0)) H16 t1 H20) in 
(eq_ind T t1 (\lambda (t0: T).(sn3 c (THead (Bind Abst) t0 x1))) (let H_x1 
\def (term_dec t2 x1) in (let H23 \def H_x1 in (or_ind (eq T t2 x1) ((eq T t2 
x1) \to (\forall (P: Prop).P)) (sn3 c (THead (Bind Abst) t1 x1)) (\lambda 
(H24: (eq T t2 x1)).(let H25 \def (eq_ind_r T x1 (\lambda (t0: T).((eq T 
(THead (Bind Abst) t1 t2) (THead (Bind Abst) t1 t0)) \to (\forall (P: 
Prop).P))) H21 t2 H24) in (let H26 \def (eq_ind_r T x1 (\lambda (t0: 
T).(\forall (b0: B).(\forall (u0: T).(pr3 (CHead c (Bind b0) u0) t2 t0)))) 
H17 t2 H24) in (eq_ind T t2 (\lambda (t0: T).(sn3 c (THead (Bind Abst) t1 
t0))) (H25 (refl_equal T (THead (Bind Abst) t1 t2)) (sn3 c (THead (Bind Abst) 
t1 t2))) x1 H24)))) (\lambda (H24: (((eq T t2 x1) \to (\forall (P: 
Prop).P)))).(H11 x1 H24 (H17 Abst t1))) H23))) x0 H20)))) (\lambda (H20: 
(((eq T t1 x0) \to (\forall (P: Prop).P)))).(let H_x1 \def (term_dec t2 x1) 
in (let H21 \def H_x1 in (or_ind (eq T t2 x1) ((eq T t2 x1) \to (\forall (P: 
Prop).P)) (sn3 c (THead (Bind Abst) x0 x1)) (\lambda (H22: (eq T t2 x1)).(let 
H23 \def (eq_ind_r T x1 (\lambda (t0: T).(\forall (b0: B).(\forall (u0: 
T).(pr3 (CHead c (Bind b0) u0) t2 t0)))) H17 t2 H22) in (eq_ind T t2 (\lambda 
(t0: T).(sn3 c (THead (Bind Abst) x0 t0))) (H13 x0 H20 H16 t2 (sn3_cpr3_trans 
c t1 x0 H16 (Bind Abst) t2 (sn3_sing (CHead c (Bind Abst) t1) t2 H12))) x1 
H22))) (\lambda (H22: (((eq T t2 x1) \to (\forall (P: Prop).P)))).(H13 x0 H20 
H16 x1 (sn3_cpr3_trans c t1 x0 H16 (Bind Abst) x1 (H12 x1 H22 (H17 Abst 
t1))))) H21)))) H19))) t3 H15))))))) H14)))))))) (\lambda (H8: (not (eq B b 
Abst))).(let H_x0 \def (pr3_gen_bind b H8 c t1 t2 t3 H6) in (let H9 \def H_x0 
in (or_ind (ex3_2 T T (\lambda (u2: T).(\lambda (t4: T).(eq T t3 (THead (Bind 
b) u2 t4)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c t1 u2))) (\lambda (_: 
T).(\lambda (t4: T).(pr3 (CHead c (Bind b) t1) t2 t4)))) (pr3 (CHead c (Bind 
b) t1) t2 (lift (S O) O t3)) (sn3 c t3) (\lambda (H10: (ex3_2 T T (\lambda 
(u2: T).(\lambda (t4: T).(eq T t3 (THead (Bind b) u2 t4)))) (\lambda (u2: 
T).(\lambda (_: T).(pr3 c t1 u2))) (\lambda (_: T).(\lambda (t4: T).(pr3 
(CHead c (Bind b) t1) t2 t4))))).(ex3_2_ind T T (\lambda (u2: T).(\lambda 
(t4: T).(eq T t3 (THead (Bind b) u2 t4)))) (\lambda (u2: T).(\lambda (_: 
T).(pr3 c t1 u2))) (\lambda (_: T).(\lambda (t4: T).(pr3 (CHead c (Bind b) 
t1) t2 t4))) (sn3 c t3) (\lambda (x0: T).(\lambda (x1: T).(\lambda (H11: (eq 
T t3 (THead (Bind b) x0 x1))).(\lambda (H12: (pr3 c t1 x0)).(\lambda (H13: 
(pr3 (CHead c (Bind b) t1) t2 x1)).(let H14 \def (eq_ind T t3 (\lambda (t0: 
T).((eq T (THead (Bind b) t1 t2) t0) \to (\forall (P: Prop).P))) H5 (THead 
(Bind b) x0 x1) H11) in (eq_ind_r T (THead (Bind b) x0 x1) (\lambda (t0: 
T).(sn3 c t0)) (let H_x1 \def (term_dec t1 x0) in (let H15 \def H_x1 in 
(or_ind (eq T t1 x0) ((eq T t1 x0) \to (\forall (P: Prop).P)) (sn3 c (THead 
(Bind b) x0 x1)) (\lambda (H16: (eq T t1 x0)).(let H17 \def (eq_ind_r T x0 
(\lambda (t0: T).((eq T (THead (Bind b) t1 t2) (THead (Bind b) t0 x1)) \to 
(\forall (P: Prop).P))) H14 t1 H16) in (let H18 \def (eq_ind_r T x0 (\lambda 
(t0: T).(pr3 c t1 t0)) H12 t1 H16) in (eq_ind T t1 (\lambda (t0: T).(sn3 c 
(THead (Bind b) t0 x1))) (let H_x2 \def (term_dec t2 x1) in (let H19 \def 
H_x2 in (or_ind (eq T t2 x1) ((eq T t2 x1) \to (\forall (P: Prop).P)) (sn3 c 
(THead (Bind b) t1 x1)) (\lambda (H20: (eq T t2 x1)).(let H21 \def (eq_ind_r 
T x1 (\lambda (t0: T).((eq T (THead (Bind b) t1 t2) (THead (Bind b) t1 t0)) 
\to (\forall (P: Prop).P))) H17 t2 H20) in (let H22 \def (eq_ind_r T x1 
(\lambda (t0: T).(pr3 (CHead c (Bind b) t1) t2 t0)) H13 t2 H20) in (eq_ind T 
t2 (\lambda (t0: T).(sn3 c (THead (Bind b) t1 t0))) (H21 (refl_equal T (THead 
(Bind b) t1 t2)) (sn3 c (THead (Bind b) t1 t2))) x1 H20)))) (\lambda (H20: 
(((eq T t2 x1) \to (\forall (P: Prop).P)))).(H4 x1 H20 H13)) H19))) x0 
H16)))) (\lambda (H16: (((eq T t1 x0) \to (\forall (P: Prop).P)))).(let H_x2 
\def (term_dec t2 x1) in (let H17 \def H_x2 in (or_ind (eq T t2 x1) ((eq T t2 
x1) \to (\forall (P: Prop).P)) (sn3 c (THead (Bind b) x0 x1)) (\lambda (H18: 
(eq T t2 x1)).(let H19 \def (eq_ind_r T x1 (\lambda (t0: T).(pr3 (CHead c 
(Bind b) t1) t2 t0)) H13 t2 H18) in (eq_ind T t2 (\lambda (t0: T).(sn3 c 
(THead (Bind b) x0 t0))) (H1 x0 H16 H12 t2 (sn3_cpr3_trans c t1 x0 H12 (Bind 
b) t2 (sn3_sing (CHead c (Bind b) t1) t2 H3))) x1 H18))) (\lambda (H18: (((eq 
T t2 x1) \to (\forall (P: Prop).P)))).(H1 x0 H16 H12 x1 (sn3_cpr3_trans c t1 
x0 H12 (Bind b) x1 (H3 x1 H18 H13)))) H17)))) H15))) t3 H11))))))) H10)) 
(\lambda (H10: (pr3 (CHead c (Bind b) t1) t2 (lift (S O) O 
t3))).(sn3_gen_lift (CHead c (Bind b) t1) t3 (S O) O (sn3_pr3_trans (CHead c 
(Bind b) t1) t2 (sn3_sing (CHead c (Bind b) t1) t2 H3) (lift (S O) O t3) H10) 
c (drop_drop (Bind b) O c c (drop_refl c) t1))) H9)))) H7)))))))))) t 
H2)))))) u H)))).
(* COMMENTS
Initial nodes: 2401
END *)

theorem sn3_beta:
 \forall (c: C).(\forall (v: T).(\forall (t: T).((sn3 c (THead (Bind Abbr) v 
t)) \to (\forall (w: T).((sn3 c w) \to (sn3 c (THead (Flat Appl) v (THead 
(Bind Abst) w t))))))))
\def
 \lambda (c: C).(\lambda (v: T).(\lambda (t: T).(\lambda (H: (sn3 c (THead 
(Bind Abbr) v t))).(insert_eq T (THead (Bind Abbr) v t) (\lambda (t0: T).(sn3 
c t0)) (\lambda (_: T).(\forall (w: T).((sn3 c w) \to (sn3 c (THead (Flat 
Appl) v (THead (Bind Abst) w t)))))) (\lambda (y: T).(\lambda (H0: (sn3 c 
y)).(unintro T t (\lambda (t0: T).((eq T y (THead (Bind Abbr) v t0)) \to 
(\forall (w: T).((sn3 c w) \to (sn3 c (THead (Flat Appl) v (THead (Bind Abst) 
w t0))))))) (unintro T v (\lambda (t0: T).(\forall (x: T).((eq T y (THead 
(Bind Abbr) t0 x)) \to (\forall (w: T).((sn3 c w) \to (sn3 c (THead (Flat 
Appl) t0 (THead (Bind Abst) w x)))))))) (sn3_ind c (\lambda (t0: T).(\forall 
(x: T).(\forall (x0: T).((eq T t0 (THead (Bind Abbr) x x0)) \to (\forall (w: 
T).((sn3 c w) \to (sn3 c (THead (Flat Appl) x (THead (Bind Abst) w 
x0))))))))) (\lambda (t1: T).(\lambda (H1: ((\forall (t2: T).((((eq T t1 t2) 
\to (\forall (P: Prop).P))) \to ((pr3 c t1 t2) \to (sn3 c t2)))))).(\lambda 
(H2: ((\forall (t2: T).((((eq T t1 t2) \to (\forall (P: Prop).P))) \to ((pr3 
c t1 t2) \to (\forall (x: T).(\forall (x0: T).((eq T t2 (THead (Bind Abbr) x 
x0)) \to (\forall (w: T).((sn3 c w) \to (sn3 c (THead (Flat Appl) x (THead 
(Bind Abst) w x0))))))))))))).(\lambda (x: T).(\lambda (x0: T).(\lambda (H3: 
(eq T t1 (THead (Bind Abbr) x x0))).(\lambda (w: T).(\lambda (H4: (sn3 c 
w)).(let H5 \def (eq_ind T t1 (\lambda (t0: T).(\forall (t2: T).((((eq T t0 
t2) \to (\forall (P: Prop).P))) \to ((pr3 c t0 t2) \to (\forall (x1: 
T).(\forall (x2: T).((eq T t2 (THead (Bind Abbr) x1 x2)) \to (\forall (w0: 
T).((sn3 c w0) \to (sn3 c (THead (Flat Appl) x1 (THead (Bind Abst) w0 
x2)))))))))))) H2 (THead (Bind Abbr) x x0) H3) in (let H6 \def (eq_ind T t1 
(\lambda (t0: T).(\forall (t2: T).((((eq T t0 t2) \to (\forall (P: Prop).P))) 
\to ((pr3 c t0 t2) \to (sn3 c t2))))) H1 (THead (Bind Abbr) x x0) H3) in 
(sn3_ind c (\lambda (t0: T).(sn3 c (THead (Flat Appl) x (THead (Bind Abst) t0 
x0)))) (\lambda (t2: T).(\lambda (H7: ((\forall (t3: T).((((eq T t2 t3) \to 
(\forall (P: Prop).P))) \to ((pr3 c t2 t3) \to (sn3 c t3)))))).(\lambda (H8: 
((\forall (t3: T).((((eq T t2 t3) \to (\forall (P: Prop).P))) \to ((pr3 c t2 
t3) \to (sn3 c (THead (Flat Appl) x (THead (Bind Abst) t3 
x0)))))))).(sn3_pr2_intro c (THead (Flat Appl) x (THead (Bind Abst) t2 x0)) 
(\lambda (t3: T).(\lambda (H9: (((eq T (THead (Flat Appl) x (THead (Bind 
Abst) t2 x0)) t3) \to (\forall (P: Prop).P)))).(\lambda (H10: (pr2 c (THead 
(Flat Appl) x (THead (Bind Abst) t2 x0)) t3)).(let H11 \def (pr2_gen_appl c x 
(THead (Bind Abst) t2 x0) t3 H10) in (or3_ind (ex3_2 T T (\lambda (u2: 
T).(\lambda (t4: T).(eq T t3 (THead (Flat Appl) u2 t4)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c x u2))) (\lambda (_: T).(\lambda (t4: T).(pr2 c 
(THead (Bind Abst) t2 x0) t4)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind Abst) t2 x0) 
(THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (t4: T).(eq T t3 (THead (Bind Abbr) u2 t4)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c x u2))))) (\lambda 
(_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t4: T).(\forall (b: 
B).(\forall (u: T).(pr2 (CHead c (Bind b) u) z1 t4)))))))) (ex6_6 B T T T T T 
(\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T 
(THead (Bind Abst) t2 x0) (THead (Bind b) y1 z1)))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda 
(y2: T).(eq T t3 (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) 
z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c x u2))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 c y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b) 
y2) z1 z2)))))))) (sn3 c t3) (\lambda (H12: (ex3_2 T T (\lambda (u2: 
T).(\lambda (t4: T).(eq T t3 (THead (Flat Appl) u2 t4)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c x u2))) (\lambda (_: T).(\lambda (t4: T).(pr2 c 
(THead (Bind Abst) t2 x0) t4))))).(ex3_2_ind T T (\lambda (u2: T).(\lambda 
(t4: T).(eq T t3 (THead (Flat Appl) u2 t4)))) (\lambda (u2: T).(\lambda (_: 
T).(pr2 c x u2))) (\lambda (_: T).(\lambda (t4: T).(pr2 c (THead (Bind Abst) 
t2 x0) t4))) (sn3 c t3) (\lambda (x1: T).(\lambda (x2: T).(\lambda (H13: (eq 
T t3 (THead (Flat Appl) x1 x2))).(\lambda (H14: (pr2 c x x1)).(\lambda (H15: 
(pr2 c (THead (Bind Abst) t2 x0) x2)).(let H16 \def (eq_ind T t3 (\lambda 
(t0: T).((eq T (THead (Flat Appl) x (THead (Bind Abst) t2 x0)) t0) \to 
(\forall (P: Prop).P))) H9 (THead (Flat Appl) x1 x2) H13) in (eq_ind_r T 
(THead (Flat Appl) x1 x2) (\lambda (t0: T).(sn3 c t0)) (let H17 \def 
(pr2_gen_abst c t2 x0 x2 H15) in (ex3_2_ind T T (\lambda (u2: T).(\lambda 
(t4: T).(eq T x2 (THead (Bind Abst) u2 t4)))) (\lambda (u2: T).(\lambda (_: 
T).(pr2 c t2 u2))) (\lambda (_: T).(\lambda (t4: T).(\forall (b: B).(\forall 
(u: T).(pr2 (CHead c (Bind b) u) x0 t4))))) (sn3 c (THead (Flat Appl) x1 x2)) 
(\lambda (x3: T).(\lambda (x4: T).(\lambda (H18: (eq T x2 (THead (Bind Abst) 
x3 x4))).(\lambda (H19: (pr2 c t2 x3)).(\lambda (H20: ((\forall (b: 
B).(\forall (u: T).(pr2 (CHead c (Bind b) u) x0 x4))))).(let H21 \def (eq_ind 
T x2 (\lambda (t0: T).((eq T (THead (Flat Appl) x (THead (Bind Abst) t2 x0)) 
(THead (Flat Appl) x1 t0)) \to (\forall (P: Prop).P))) H16 (THead (Bind Abst) 
x3 x4) H18) in (eq_ind_r T (THead (Bind Abst) x3 x4) (\lambda (t0: T).(sn3 c 
(THead (Flat Appl) x1 t0))) (let H_x \def (term_dec t2 x3) in (let H22 \def 
H_x in (or_ind (eq T t2 x3) ((eq T t2 x3) \to (\forall (P: Prop).P)) (sn3 c 
(THead (Flat Appl) x1 (THead (Bind Abst) x3 x4))) (\lambda (H23: (eq T t2 
x3)).(let H24 \def (eq_ind_r T x3 (\lambda (t0: T).((eq T (THead (Flat Appl) 
x (THead (Bind Abst) t2 x0)) (THead (Flat Appl) x1 (THead (Bind Abst) t0 
x4))) \to (\forall (P: Prop).P))) H21 t2 H23) in (let H25 \def (eq_ind_r T x3 
(\lambda (t0: T).(pr2 c t2 t0)) H19 t2 H23) in (eq_ind T t2 (\lambda (t0: 
T).(sn3 c (THead (Flat Appl) x1 (THead (Bind Abst) t0 x4)))) (let H_x0 \def 
(term_dec x x1) in (let H26 \def H_x0 in (or_ind (eq T x x1) ((eq T x x1) \to 
(\forall (P: Prop).P)) (sn3 c (THead (Flat Appl) x1 (THead (Bind Abst) t2 
x4))) (\lambda (H27: (eq T x x1)).(let H28 \def (eq_ind_r T x1 (\lambda (t0: 
T).((eq T (THead (Flat Appl) x (THead (Bind Abst) t2 x0)) (THead (Flat Appl) 
t0 (THead (Bind Abst) t2 x4))) \to (\forall (P: Prop).P))) H24 x H27) in (let 
H29 \def (eq_ind_r T x1 (\lambda (t0: T).(pr2 c x t0)) H14 x H27) in (eq_ind 
T x (\lambda (t0: T).(sn3 c (THead (Flat Appl) t0 (THead (Bind Abst) t2 
x4)))) (let H_x1 \def (term_dec x0 x4) in (let H30 \def H_x1 in (or_ind (eq T 
x0 x4) ((eq T x0 x4) \to (\forall (P: Prop).P)) (sn3 c (THead (Flat Appl) x 
(THead (Bind Abst) t2 x4))) (\lambda (H31: (eq T x0 x4)).(let H32 \def 
(eq_ind_r T x4 (\lambda (t0: T).((eq T (THead (Flat Appl) x (THead (Bind 
Abst) t2 x0)) (THead (Flat Appl) x (THead (Bind Abst) t2 t0))) \to (\forall 
(P: Prop).P))) H28 x0 H31) in (let H33 \def (eq_ind_r T x4 (\lambda (t0: 
T).(\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) x0 t0)))) H20 x0 
H31) in (eq_ind T x0 (\lambda (t0: T).(sn3 c (THead (Flat Appl) x (THead 
(Bind Abst) t2 t0)))) (H32 (refl_equal T (THead (Flat Appl) x (THead (Bind 
Abst) t2 x0))) (sn3 c (THead (Flat Appl) x (THead (Bind Abst) t2 x0)))) x4 
H31)))) (\lambda (H31: (((eq T x0 x4) \to (\forall (P: Prop).P)))).(H5 (THead 
(Bind Abbr) x x4) (\lambda (H32: (eq T (THead (Bind Abbr) x x0) (THead (Bind 
Abbr) x x4))).(\lambda (P: Prop).(let H33 \def (f_equal T T (\lambda (e: 
T).(match e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow x0 | 
(TLRef _) \Rightarrow x0 | (THead _ _ t0) \Rightarrow t0])) (THead (Bind 
Abbr) x x0) (THead (Bind Abbr) x x4) H32) in (let H34 \def (eq_ind_r T x4 
(\lambda (t0: T).((eq T x0 t0) \to (\forall (P0: Prop).P0))) H31 x0 H33) in 
(let H35 \def (eq_ind_r T x4 (\lambda (t0: T).(\forall (b: B).(\forall (u: 
T).(pr2 (CHead c (Bind b) u) x0 t0)))) H20 x0 H33) in (H34 (refl_equal T x0) 
P)))))) (pr3_pr2 c (THead (Bind Abbr) x x0) (THead (Bind Abbr) x x4) 
(pr2_head_2 c x x0 x4 (Bind Abbr) (H20 Abbr x))) x x4 (refl_equal T (THead 
(Bind Abbr) x x4)) t2 (sn3_sing c t2 H7))) H30))) x1 H27)))) (\lambda (H27: 
(((eq T x x1) \to (\forall (P: Prop).P)))).(H5 (THead (Bind Abbr) x1 x4) 
(\lambda (H28: (eq T (THead (Bind Abbr) x x0) (THead (Bind Abbr) x1 
x4))).(\lambda (P: Prop).(let H29 \def (f_equal T T (\lambda (e: T).(match e 
in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow x | (TLRef _) 
\Rightarrow x | (THead _ t0 _) \Rightarrow t0])) (THead (Bind Abbr) x x0) 
(THead (Bind Abbr) x1 x4) H28) in ((let H30 \def (f_equal T T (\lambda (e: 
T).(match e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow x0 | 
(TLRef _) \Rightarrow x0 | (THead _ _ t0) \Rightarrow t0])) (THead (Bind 
Abbr) x x0) (THead (Bind Abbr) x1 x4) H28) in (\lambda (H31: (eq T x 
x1)).(let H32 \def (eq_ind_r T x4 (\lambda (t0: T).(\forall (b: B).(\forall 
(u: T).(pr2 (CHead c (Bind b) u) x0 t0)))) H20 x0 H30) in (let H33 \def 
(eq_ind_r T x1 (\lambda (t0: T).((eq T x t0) \to (\forall (P0: Prop).P0))) 
H27 x H31) in (let H34 \def (eq_ind_r T x1 (\lambda (t0: T).(pr2 c x t0)) H14 
x H31) in (H33 (refl_equal T x) P)))))) H29)))) (pr3_head_12 c x x1 (pr3_pr2 
c x x1 H14) (Bind Abbr) x0 x4 (pr3_pr2 (CHead c (Bind Abbr) x1) x0 x4 (H20 
Abbr x1))) x1 x4 (refl_equal T (THead (Bind Abbr) x1 x4)) t2 (sn3_sing c t2 
H7))) H26))) x3 H23)))) (\lambda (H23: (((eq T t2 x3) \to (\forall (P: 
Prop).P)))).(let H_x0 \def (term_dec x x1) in (let H24 \def H_x0 in (or_ind 
(eq T x x1) ((eq T x x1) \to (\forall (P: Prop).P)) (sn3 c (THead (Flat Appl) 
x1 (THead (Bind Abst) x3 x4))) (\lambda (H25: (eq T x x1)).(let H26 \def 
(eq_ind_r T x1 (\lambda (t0: T).(pr2 c x t0)) H14 x H25) in (eq_ind T x 
(\lambda (t0: T).(sn3 c (THead (Flat Appl) t0 (THead (Bind Abst) x3 x4)))) 
(let H_x1 \def (term_dec x0 x4) in (let H27 \def H_x1 in (or_ind (eq T x0 x4) 
((eq T x0 x4) \to (\forall (P: Prop).P)) (sn3 c (THead (Flat Appl) x (THead 
(Bind Abst) x3 x4))) (\lambda (H28: (eq T x0 x4)).(let H29 \def (eq_ind_r T 
x4 (\lambda (t0: T).(\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) 
x0 t0)))) H20 x0 H28) in (eq_ind T x0 (\lambda (t0: T).(sn3 c (THead (Flat 
Appl) x (THead (Bind Abst) x3 t0)))) (H8 x3 H23 (pr3_pr2 c t2 x3 H19)) x4 
H28))) (\lambda (H28: (((eq T x0 x4) \to (\forall (P: Prop).P)))).(H5 (THead 
(Bind Abbr) x x4) (\lambda (H29: (eq T (THead (Bind Abbr) x x0) (THead (Bind 
Abbr) x x4))).(\lambda (P: Prop).(let H30 \def (f_equal T T (\lambda (e: 
T).(match e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow x0 | 
(TLRef _) \Rightarrow x0 | (THead _ _ t0) \Rightarrow t0])) (THead (Bind 
Abbr) x x0) (THead (Bind Abbr) x x4) H29) in (let H31 \def (eq_ind_r T x4 
(\lambda (t0: T).((eq T x0 t0) \to (\forall (P0: Prop).P0))) H28 x0 H30) in 
(let H32 \def (eq_ind_r T x4 (\lambda (t0: T).(\forall (b: B).(\forall (u: 
T).(pr2 (CHead c (Bind b) u) x0 t0)))) H20 x0 H30) in (H31 (refl_equal T x0) 
P)))))) (pr3_pr2 c (THead (Bind Abbr) x x0) (THead (Bind Abbr) x x4) 
(pr2_head_2 c x x0 x4 (Bind Abbr) (H20 Abbr x))) x x4 (refl_equal T (THead 
(Bind Abbr) x x4)) x3 (H7 x3 H23 (pr3_pr2 c t2 x3 H19)))) H27))) x1 H25))) 
(\lambda (H25: (((eq T x x1) \to (\forall (P: Prop).P)))).(H5 (THead (Bind 
Abbr) x1 x4) (\lambda (H26: (eq T (THead (Bind Abbr) x x0) (THead (Bind Abbr) 
x1 x4))).(\lambda (P: Prop).(let H27 \def (f_equal T T (\lambda (e: T).(match 
e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow x | (TLRef _) 
\Rightarrow x | (THead _ t0 _) \Rightarrow t0])) (THead (Bind Abbr) x x0) 
(THead (Bind Abbr) x1 x4) H26) in ((let H28 \def (f_equal T T (\lambda (e: 
T).(match e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow x0 | 
(TLRef _) \Rightarrow x0 | (THead _ _ t0) \Rightarrow t0])) (THead (Bind 
Abbr) x x0) (THead (Bind Abbr) x1 x4) H26) in (\lambda (H29: (eq T x 
x1)).(let H30 \def (eq_ind_r T x4 (\lambda (t0: T).(\forall (b: B).(\forall 
(u: T).(pr2 (CHead c (Bind b) u) x0 t0)))) H20 x0 H28) in (let H31 \def 
(eq_ind_r T x1 (\lambda (t0: T).((eq T x t0) \to (\forall (P0: Prop).P0))) 
H25 x H29) in (let H32 \def (eq_ind_r T x1 (\lambda (t0: T).(pr2 c x t0)) H14 
x H29) in (H31 (refl_equal T x) P)))))) H27)))) (pr3_head_12 c x x1 (pr3_pr2 
c x x1 H14) (Bind Abbr) x0 x4 (pr3_pr2 (CHead c (Bind Abbr) x1) x0 x4 (H20 
Abbr x1))) x1 x4 (refl_equal T (THead (Bind Abbr) x1 x4)) x3 (H7 x3 H23 
(pr3_pr2 c t2 x3 H19)))) H24)))) H22))) x2 H18))))))) H17)) t3 H13))))))) 
H12)) (\lambda (H12: (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind Abst) t2 x0) (THead 
(Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (t4: T).(eq T t3 (THead (Bind Abbr) u2 t4)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c x u2))))) (\lambda 
(_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t4: T).(\forall (b: 
B).(\forall (u: T).(pr2 (CHead c (Bind b) u) z1 t4))))))))).(ex4_4_ind T T T 
T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T 
(THead (Bind Abst) t2 x0) (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t4: T).(eq T t3 (THead (Bind 
Abbr) u2 t4)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr2 c x u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t4: T).(\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) 
z1 t4))))))) (sn3 c t3) (\lambda (x1: T).(\lambda (x2: T).(\lambda (x3: 
T).(\lambda (x4: T).(\lambda (H13: (eq T (THead (Bind Abst) t2 x0) (THead 
(Bind Abst) x1 x2))).(\lambda (H14: (eq T t3 (THead (Bind Abbr) x3 
x4))).(\lambda (H15: (pr2 c x x3)).(\lambda (H16: ((\forall (b: B).(\forall 
(u: T).(pr2 (CHead c (Bind b) u) x2 x4))))).(let H17 \def (eq_ind T t3 
(\lambda (t0: T).((eq T (THead (Flat Appl) x (THead (Bind Abst) t2 x0)) t0) 
\to (\forall (P: Prop).P))) H9 (THead (Bind Abbr) x3 x4) H14) in (eq_ind_r T 
(THead (Bind Abbr) x3 x4) (\lambda (t0: T).(sn3 c t0)) (let H18 \def (f_equal 
T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) with [(TSort _) 
\Rightarrow t2 | (TLRef _) \Rightarrow t2 | (THead _ t0 _) \Rightarrow t0])) 
(THead (Bind Abst) t2 x0) (THead (Bind Abst) x1 x2) H13) in ((let H19 \def 
(f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) with 
[(TSort _) \Rightarrow x0 | (TLRef _) \Rightarrow x0 | (THead _ _ t0) 
\Rightarrow t0])) (THead (Bind Abst) t2 x0) (THead (Bind Abst) x1 x2) H13) in 
(\lambda (_: (eq T t2 x1)).(let H21 \def (eq_ind_r T x2 (\lambda (t0: 
T).(\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) t0 x4)))) H16 x0 
H19) in (let H_x \def (term_dec x x3) in (let H22 \def H_x in (or_ind (eq T x 
x3) ((eq T x x3) \to (\forall (P: Prop).P)) (sn3 c (THead (Bind Abbr) x3 x4)) 
(\lambda (H23: (eq T x x3)).(let H24 \def (eq_ind_r T x3 (\lambda (t0: 
T).(pr2 c x t0)) H15 x H23) in (eq_ind T x (\lambda (t0: T).(sn3 c (THead 
(Bind Abbr) t0 x4))) (let H_x0 \def (term_dec x0 x4) in (let H25 \def H_x0 in 
(or_ind (eq T x0 x4) ((eq T x0 x4) \to (\forall (P: Prop).P)) (sn3 c (THead 
(Bind Abbr) x x4)) (\lambda (H26: (eq T x0 x4)).(let H27 \def (eq_ind_r T x4 
(\lambda (t0: T).(\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) x0 
t0)))) H21 x0 H26) in (eq_ind T x0 (\lambda (t0: T).(sn3 c (THead (Bind Abbr) 
x t0))) (sn3_sing c (THead (Bind Abbr) x x0) H6) x4 H26))) (\lambda (H26: 
(((eq T x0 x4) \to (\forall (P: Prop).P)))).(H6 (THead (Bind Abbr) x x4) 
(\lambda (H27: (eq T (THead (Bind Abbr) x x0) (THead (Bind Abbr) x 
x4))).(\lambda (P: Prop).(let H28 \def (f_equal T T (\lambda (e: T).(match e 
in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow x0 | (TLRef _) 
\Rightarrow x0 | (THead _ _ t0) \Rightarrow t0])) (THead (Bind Abbr) x x0) 
(THead (Bind Abbr) x x4) H27) in (let H29 \def (eq_ind_r T x4 (\lambda (t0: 
T).((eq T x0 t0) \to (\forall (P0: Prop).P0))) H26 x0 H28) in (let H30 \def 
(eq_ind_r T x4 (\lambda (t0: T).(\forall (b: B).(\forall (u: T).(pr2 (CHead c 
(Bind b) u) x0 t0)))) H21 x0 H28) in (H29 (refl_equal T x0) P)))))) (pr3_pr2 
c (THead (Bind Abbr) x x0) (THead (Bind Abbr) x x4) (pr2_head_2 c x x0 x4 
(Bind Abbr) (H21 Abbr x))))) H25))) x3 H23))) (\lambda (H23: (((eq T x x3) 
\to (\forall (P: Prop).P)))).(H6 (THead (Bind Abbr) x3 x4) (\lambda (H24: (eq 
T (THead (Bind Abbr) x x0) (THead (Bind Abbr) x3 x4))).(\lambda (P: 
Prop).(let H25 \def (f_equal T T (\lambda (e: T).(match e in T return 
(\lambda (_: T).T) with [(TSort _) \Rightarrow x | (TLRef _) \Rightarrow x | 
(THead _ t0 _) \Rightarrow t0])) (THead (Bind Abbr) x x0) (THead (Bind Abbr) 
x3 x4) H24) in ((let H26 \def (f_equal T T (\lambda (e: T).(match e in T 
return (\lambda (_: T).T) with [(TSort _) \Rightarrow x0 | (TLRef _) 
\Rightarrow x0 | (THead _ _ t0) \Rightarrow t0])) (THead (Bind Abbr) x x0) 
(THead (Bind Abbr) x3 x4) H24) in (\lambda (H27: (eq T x x3)).(let H28 \def 
(eq_ind_r T x4 (\lambda (t0: T).(\forall (b: B).(\forall (u: T).(pr2 (CHead c 
(Bind b) u) x0 t0)))) H21 x0 H26) in (let H29 \def (eq_ind_r T x3 (\lambda 
(t0: T).((eq T x t0) \to (\forall (P0: Prop).P0))) H23 x H27) in (let H30 
\def (eq_ind_r T x3 (\lambda (t0: T).(pr2 c x t0)) H15 x H27) in (H29 
(refl_equal T x) P)))))) H25)))) (pr3_head_12 c x x3 (pr3_pr2 c x x3 H15) 
(Bind Abbr) x0 x4 (pr3_pr2 (CHead c (Bind Abbr) x3) x0 x4 (H21 Abbr x3))))) 
H22)))))) H18)) t3 H14)))))))))) H12)) (\lambda (H12: (ex6_6 B T T T T T 
(\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T 
(THead (Bind Abst) t2 x0) (THead (Bind b) y1 z1)))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda 
(y2: T).(eq T t3 (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) 
z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c x u2))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 c y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b) 
y2) z1 z2))))))))).(ex6_6_ind B T T T T T (\lambda (b: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B 
b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind Abst) t2 x0) (THead 
(Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T t3 (THead (Bind 
b) y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr2 c x u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 y2))))))) 
(\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda 
(_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b) y2) z1 z2))))))) (sn3 c t3) 
(\lambda (x1: B).(\lambda (x2: T).(\lambda (x3: T).(\lambda (x4: T).(\lambda 
(x5: T).(\lambda (x6: T).(\lambda (H13: (not (eq B x1 Abst))).(\lambda (H14: 
(eq T (THead (Bind Abst) t2 x0) (THead (Bind x1) x2 x3))).(\lambda (H15: (eq 
T t3 (THead (Bind x1) x6 (THead (Flat Appl) (lift (S O) O x5) x4)))).(\lambda 
(_: (pr2 c x x5)).(\lambda (H17: (pr2 c x2 x6)).(\lambda (H18: (pr2 (CHead c 
(Bind x1) x6) x3 x4)).(let H19 \def (eq_ind T t3 (\lambda (t0: T).((eq T 
(THead (Flat Appl) x (THead (Bind Abst) t2 x0)) t0) \to (\forall (P: 
Prop).P))) H9 (THead (Bind x1) x6 (THead (Flat Appl) (lift (S O) O x5) x4)) 
H15) in (eq_ind_r T (THead (Bind x1) x6 (THead (Flat Appl) (lift (S O) O x5) 
x4)) (\lambda (t0: T).(sn3 c t0)) (let H20 \def (f_equal T B (\lambda (e: 
T).(match e in T return (\lambda (_: T).B) with [(TSort _) \Rightarrow Abst | 
(TLRef _) \Rightarrow Abst | (THead k _ _) \Rightarrow (match k in K return 
(\lambda (_: K).B) with [(Bind b) \Rightarrow b | (Flat _) \Rightarrow 
Abst])])) (THead (Bind Abst) t2 x0) (THead (Bind x1) x2 x3) H14) in ((let H21 
\def (f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) 
with [(TSort _) \Rightarrow t2 | (TLRef _) \Rightarrow t2 | (THead _ t0 _) 
\Rightarrow t0])) (THead (Bind Abst) t2 x0) (THead (Bind x1) x2 x3) H14) in 
((let H22 \def (f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: 
T).T) with [(TSort _) \Rightarrow x0 | (TLRef _) \Rightarrow x0 | (THead _ _ 
t0) \Rightarrow t0])) (THead (Bind Abst) t2 x0) (THead (Bind x1) x2 x3) H14) 
in (\lambda (H23: (eq T t2 x2)).(\lambda (H24: (eq B Abst x1)).(let H25 \def 
(eq_ind_r T x3 (\lambda (t0: T).(pr2 (CHead c (Bind x1) x6) t0 x4)) H18 x0 
H22) in (let H26 \def (eq_ind_r T x2 (\lambda (t0: T).(pr2 c t0 x6)) H17 t2 
H23) in (let H27 \def (eq_ind_r B x1 (\lambda (b: B).(pr2 (CHead c (Bind b) 
x6) x0 x4)) H25 Abst H24) in (let H28 \def (eq_ind_r B x1 (\lambda (b: 
B).(not (eq B b Abst))) H13 Abst H24) in (eq_ind B Abst (\lambda (b: B).(sn3 
c (THead (Bind b) x6 (THead (Flat Appl) (lift (S O) O x5) x4)))) (let H29 
\def (match (H28 (refl_equal B Abst)) in False return (\lambda (_: 
False).(sn3 c (THead (Bind Abst) x6 (THead (Flat Appl) (lift (S O) O x5) 
x4)))) with []) in H29) x1 H24)))))))) H21)) H20)) t3 H15)))))))))))))) H12)) 
H11))))))))) w H4))))))))))) y H0))))) H)))).
(* COMMENTS
Initial nodes: 5699
END *)

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
(* COMMENTS
Initial nodes: 2125
END *)

theorem sn3_appl_abbr:
 \forall (c: C).(\forall (d: C).(\forall (w: T).(\forall (i: nat).((getl i c 
(CHead d (Bind Abbr) w)) \to (\forall (v: T).((sn3 c (THead (Flat Appl) v 
(lift (S i) O w))) \to (sn3 c (THead (Flat Appl) v (TLRef i)))))))))
\def
 \lambda (c: C).(\lambda (d: C).(\lambda (w: T).(\lambda (i: nat).(\lambda 
(H: (getl i c (CHead d (Bind Abbr) w))).(\lambda (v: T).(\lambda (H0: (sn3 c 
(THead (Flat Appl) v (lift (S i) O w)))).(insert_eq T (THead (Flat Appl) v 
(lift (S i) O w)) (\lambda (t: T).(sn3 c t)) (\lambda (_: T).(sn3 c (THead 
(Flat Appl) v (TLRef i)))) (\lambda (y: T).(\lambda (H1: (sn3 c y)).(unintro 
T v (\lambda (t: T).((eq T y (THead (Flat Appl) t (lift (S i) O w))) \to (sn3 
c (THead (Flat Appl) t (TLRef i))))) (sn3_ind c (\lambda (t: T).(\forall (x: 
T).((eq T t (THead (Flat Appl) x (lift (S i) O w))) \to (sn3 c (THead (Flat 
Appl) x (TLRef i)))))) (\lambda (t1: T).(\lambda (H2: ((\forall (t2: 
T).((((eq T t1 t2) \to (\forall (P: Prop).P))) \to ((pr3 c t1 t2) \to (sn3 c 
t2)))))).(\lambda (H3: ((\forall (t2: T).((((eq T t1 t2) \to (\forall (P: 
Prop).P))) \to ((pr3 c t1 t2) \to (\forall (x: T).((eq T t2 (THead (Flat 
Appl) x (lift (S i) O w))) \to (sn3 c (THead (Flat Appl) x (TLRef 
i)))))))))).(\lambda (x: T).(\lambda (H4: (eq T t1 (THead (Flat Appl) x (lift 
(S i) O w)))).(let H5 \def (eq_ind T t1 (\lambda (t: T).(\forall (t2: 
T).((((eq T t t2) \to (\forall (P: Prop).P))) \to ((pr3 c t t2) \to (\forall 
(x0: T).((eq T t2 (THead (Flat Appl) x0 (lift (S i) O w))) \to (sn3 c (THead 
(Flat Appl) x0 (TLRef i))))))))) H3 (THead (Flat Appl) x (lift (S i) O w)) 
H4) in (let H6 \def (eq_ind T t1 (\lambda (t: T).(\forall (t2: T).((((eq T t 
t2) \to (\forall (P: Prop).P))) \to ((pr3 c t t2) \to (sn3 c t2))))) H2 
(THead (Flat Appl) x (lift (S i) O w)) H4) in (sn3_pr2_intro c (THead (Flat 
Appl) x (TLRef i)) (\lambda (t2: T).(\lambda (H7: (((eq T (THead (Flat Appl) 
x (TLRef i)) t2) \to (\forall (P: Prop).P)))).(\lambda (H8: (pr2 c (THead 
(Flat Appl) x (TLRef i)) t2)).(let H9 \def (pr2_gen_appl c x (TLRef i) t2 H8) 
in (or3_ind (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead 
(Flat Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c x u2))) 
(\lambda (_: T).(\lambda (t3: T).(pr2 c (TLRef i) t3)))) (ex4_4 T T T T 
(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T 
(TLRef i) (THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind Abbr) u2 t3)))))) 
(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c x 
u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: 
T).(\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) z1 t3)))))))) 
(ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(eq T (TLRef i) (THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda 
(_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq 
T t2 (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) 
(\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr2 c x u2))))))) (\lambda (_: B).(\lambda (y1: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 
y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b) y2) z1 z2)))))))) 
(sn3 c t2) (\lambda (H10: (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T 
t2 (THead (Flat Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c x 
u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c (TLRef i) t3))))).(ex3_2_ind T 
T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Flat Appl) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c x u2))) (\lambda (_: T).(\lambda (t3: 
T).(pr2 c (TLRef i) t3))) (sn3 c t2) (\lambda (x0: T).(\lambda (x1: 
T).(\lambda (H11: (eq T t2 (THead (Flat Appl) x0 x1))).(\lambda (H12: (pr2 c 
x x0)).(\lambda (H13: (pr2 c (TLRef i) x1)).(let H14 \def (eq_ind T t2 
(\lambda (t: T).((eq T (THead (Flat Appl) x (TLRef i)) t) \to (\forall (P: 
Prop).P))) H7 (THead (Flat Appl) x0 x1) H11) in (eq_ind_r T (THead (Flat 
Appl) x0 x1) (\lambda (t: T).(sn3 c t)) (let H15 \def (pr2_gen_lref c x1 i 
H13) in (or_ind (eq T x1 (TLRef i)) (ex2_2 C T (\lambda (d0: C).(\lambda (u: 
T).(getl i c (CHead d0 (Bind Abbr) u)))) (\lambda (_: C).(\lambda (u: T).(eq 
T x1 (lift (S i) O u))))) (sn3 c (THead (Flat Appl) x0 x1)) (\lambda (H16: 
(eq T x1 (TLRef i))).(let H17 \def (eq_ind T x1 (\lambda (t: T).((eq T (THead 
(Flat Appl) x (TLRef i)) (THead (Flat Appl) x0 t)) \to (\forall (P: 
Prop).P))) H14 (TLRef i) H16) in (eq_ind_r T (TLRef i) (\lambda (t: T).(sn3 c 
(THead (Flat Appl) x0 t))) (let H_x \def (term_dec x x0) in (let H18 \def H_x 
in (or_ind (eq T x x0) ((eq T x x0) \to (\forall (P: Prop).P)) (sn3 c (THead 
(Flat Appl) x0 (TLRef i))) (\lambda (H19: (eq T x x0)).(let H20 \def 
(eq_ind_r T x0 (\lambda (t: T).((eq T (THead (Flat Appl) x (TLRef i)) (THead 
(Flat Appl) t (TLRef i))) \to (\forall (P: Prop).P))) H17 x H19) in (let H21 
\def (eq_ind_r T x0 (\lambda (t: T).(pr2 c x t)) H12 x H19) in (eq_ind T x 
(\lambda (t: T).(sn3 c (THead (Flat Appl) t (TLRef i)))) (H20 (refl_equal T 
(THead (Flat Appl) x (TLRef i))) (sn3 c (THead (Flat Appl) x (TLRef i)))) x0 
H19)))) (\lambda (H19: (((eq T x x0) \to (\forall (P: Prop).P)))).(H5 (THead 
(Flat Appl) x0 (lift (S i) O w)) (\lambda (H20: (eq T (THead (Flat Appl) x 
(lift (S i) O w)) (THead (Flat Appl) x0 (lift (S i) O w)))).(\lambda (P: 
Prop).(let H21 \def (f_equal T T (\lambda (e: T).(match e in T return 
(\lambda (_: T).T) with [(TSort _) \Rightarrow x | (TLRef _) \Rightarrow x | 
(THead _ t _) \Rightarrow t])) (THead (Flat Appl) x (lift (S i) O w)) (THead 
(Flat Appl) x0 (lift (S i) O w)) H20) in (let H22 \def (eq_ind_r T x0 
(\lambda (t: T).((eq T x t) \to (\forall (P0: Prop).P0))) H19 x H21) in (let 
H23 \def (eq_ind_r T x0 (\lambda (t: T).(pr2 c x t)) H12 x H21) in (H22 
(refl_equal T x) P)))))) (pr3_pr2 c (THead (Flat Appl) x (lift (S i) O w)) 
(THead (Flat Appl) x0 (lift (S i) O w)) (pr2_head_1 c x x0 H12 (Flat Appl) 
(lift (S i) O w))) x0 (refl_equal T (THead (Flat Appl) x0 (lift (S i) O 
w))))) H18))) x1 H16))) (\lambda (H16: (ex2_2 C T (\lambda (d0: C).(\lambda 
(u: T).(getl i c (CHead d0 (Bind Abbr) u)))) (\lambda (_: C).(\lambda (u: 
T).(eq T x1 (lift (S i) O u)))))).(ex2_2_ind C T (\lambda (d0: C).(\lambda 
(u: T).(getl i c (CHead d0 (Bind Abbr) u)))) (\lambda (_: C).(\lambda (u: 
T).(eq T x1 (lift (S i) O u)))) (sn3 c (THead (Flat Appl) x0 x1)) (\lambda 
(x2: C).(\lambda (x3: T).(\lambda (H17: (getl i c (CHead x2 (Bind Abbr) 
x3))).(\lambda (H18: (eq T x1 (lift (S i) O x3))).(let H19 \def (eq_ind T x1 
(\lambda (t: T).((eq T (THead (Flat Appl) x (TLRef i)) (THead (Flat Appl) x0 
t)) \to (\forall (P: Prop).P))) H14 (lift (S i) O x3) H18) in (eq_ind_r T 
(lift (S i) O x3) (\lambda (t: T).(sn3 c (THead (Flat Appl) x0 t))) (let H20 
\def (eq_ind C (CHead d (Bind Abbr) w) (\lambda (c0: C).(getl i c c0)) H 
(CHead x2 (Bind Abbr) x3) (getl_mono c (CHead d (Bind Abbr) w) i H (CHead x2 
(Bind Abbr) x3) H17)) in (let H21 \def (f_equal C C (\lambda (e: C).(match e 
in C return (\lambda (_: C).C) with [(CSort _) \Rightarrow d | (CHead c0 _ _) 
\Rightarrow c0])) (CHead d (Bind Abbr) w) (CHead x2 (Bind Abbr) x3) 
(getl_mono c (CHead d (Bind Abbr) w) i H (CHead x2 (Bind Abbr) x3) H17)) in 
((let H22 \def (f_equal C T (\lambda (e: C).(match e in C return (\lambda (_: 
C).T) with [(CSort _) \Rightarrow w | (CHead _ _ t) \Rightarrow t])) (CHead d 
(Bind Abbr) w) (CHead x2 (Bind Abbr) x3) (getl_mono c (CHead d (Bind Abbr) w) 
i H (CHead x2 (Bind Abbr) x3) H17)) in (\lambda (H23: (eq C d x2)).(let H24 
\def (eq_ind_r T x3 (\lambda (t: T).(getl i c (CHead x2 (Bind Abbr) t))) H20 
w H22) in (eq_ind T w (\lambda (t: T).(sn3 c (THead (Flat Appl) x0 (lift (S 
i) O t)))) (let H25 \def (eq_ind_r C x2 (\lambda (c0: C).(getl i c (CHead c0 
(Bind Abbr) w))) H24 d H23) in (let H_x \def (term_dec x x0) in (let H26 \def 
H_x in (or_ind (eq T x x0) ((eq T x x0) \to (\forall (P: Prop).P)) (sn3 c 
(THead (Flat Appl) x0 (lift (S i) O w))) (\lambda (H27: (eq T x x0)).(let H28 
\def (eq_ind_r T x0 (\lambda (t: T).(pr2 c x t)) H12 x H27) in (eq_ind T x 
(\lambda (t: T).(sn3 c (THead (Flat Appl) t (lift (S i) O w)))) (sn3_sing c 
(THead (Flat Appl) x (lift (S i) O w)) H6) x0 H27))) (\lambda (H27: (((eq T x 
x0) \to (\forall (P: Prop).P)))).(H6 (THead (Flat Appl) x0 (lift (S i) O w)) 
(\lambda (H28: (eq T (THead (Flat Appl) x (lift (S i) O w)) (THead (Flat 
Appl) x0 (lift (S i) O w)))).(\lambda (P: Prop).(let H29 \def (f_equal T T 
(\lambda (e: T).(match e in T return (\lambda (_: T).T) with [(TSort _) 
\Rightarrow x | (TLRef _) \Rightarrow x | (THead _ t _) \Rightarrow t])) 
(THead (Flat Appl) x (lift (S i) O w)) (THead (Flat Appl) x0 (lift (S i) O 
w)) H28) in (let H30 \def (eq_ind_r T x0 (\lambda (t: T).((eq T x t) \to 
(\forall (P0: Prop).P0))) H27 x H29) in (let H31 \def (eq_ind_r T x0 (\lambda 
(t: T).(pr2 c x t)) H12 x H29) in (H30 (refl_equal T x) P)))))) (pr3_pr2 c 
(THead (Flat Appl) x (lift (S i) O w)) (THead (Flat Appl) x0 (lift (S i) O 
w)) (pr2_head_1 c x x0 H12 (Flat Appl) (lift (S i) O w))))) H26)))) x3 
H22)))) H21))) x1 H18)))))) H16)) H15)) t2 H11))))))) H10)) (\lambda (H10: 
(ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: 
T).(eq T (TLRef i) (THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda 
(_: T).(\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind Abbr) u2 
t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: 
T).(pr2 c x u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda 
(t3: T).(\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) z1 
t3))))))))).(ex4_4_ind T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(eq T (TLRef i) (THead (Bind Abst) y1 z1)))))) (\lambda 
(_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead 
(Bind Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr2 c x u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda 
(_: T).(\lambda (t3: T).(\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind 
b) u) z1 t3))))))) (sn3 c t2) (\lambda (x0: T).(\lambda (x1: T).(\lambda (x2: 
T).(\lambda (x3: T).(\lambda (H11: (eq T (TLRef i) (THead (Bind Abst) x0 
x1))).(\lambda (H12: (eq T t2 (THead (Bind Abbr) x2 x3))).(\lambda (_: (pr2 c 
x x2)).(\lambda (_: ((\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind b) 
u) x1 x3))))).(let H15 \def (eq_ind T t2 (\lambda (t: T).((eq T (THead (Flat 
Appl) x (TLRef i)) t) \to (\forall (P: Prop).P))) H7 (THead (Bind Abbr) x2 
x3) H12) in (eq_ind_r T (THead (Bind Abbr) x2 x3) (\lambda (t: T).(sn3 c t)) 
(let H16 \def (eq_ind T (TLRef i) (\lambda (ee: T).(match ee in T return 
(\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow True | (THead _ _ _) \Rightarrow False])) I (THead (Bind Abst) x0 
x1) H11) in (False_ind (sn3 c (THead (Bind Abbr) x2 x3)) H16)) t2 
H12)))))))))) H10)) (\lambda (H10: (ex6_6 B T T T T T (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T (TLRef i) 
(THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T t2 (THead (Bind 
b) y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr2 c x u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 y2))))))) 
(\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda 
(_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b) y2) z1 z2))))))))).(ex6_6_ind 
B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(eq T (TLRef i) (THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda 
(_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq 
T t2 (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) 
(\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr2 c x u2))))))) (\lambda (_: B).(\lambda (y1: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 
y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b) y2) z1 z2))))))) 
(sn3 c t2) (\lambda (x0: B).(\lambda (x1: T).(\lambda (x2: T).(\lambda (x3: 
T).(\lambda (x4: T).(\lambda (x5: T).(\lambda (_: (not (eq B x0 
Abst))).(\lambda (H12: (eq T (TLRef i) (THead (Bind x0) x1 x2))).(\lambda 
(H13: (eq T t2 (THead (Bind x0) x5 (THead (Flat Appl) (lift (S O) O x4) 
x3)))).(\lambda (_: (pr2 c x x4)).(\lambda (_: (pr2 c x1 x5)).(\lambda (_: 
(pr2 (CHead c (Bind x0) x5) x2 x3)).(let H17 \def (eq_ind T t2 (\lambda (t: 
T).((eq T (THead (Flat Appl) x (TLRef i)) t) \to (\forall (P: Prop).P))) H7 
(THead (Bind x0) x5 (THead (Flat Appl) (lift (S O) O x4) x3)) H13) in 
(eq_ind_r T (THead (Bind x0) x5 (THead (Flat Appl) (lift (S O) O x4) x3)) 
(\lambda (t: T).(sn3 c t)) (let H18 \def (eq_ind T (TLRef i) (\lambda (ee: 
T).(match ee in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow 
False | (TLRef _) \Rightarrow True | (THead _ _ _) \Rightarrow False])) I 
(THead (Bind x0) x1 x2) H12) in (False_ind (sn3 c (THead (Bind x0) x5 (THead 
(Flat Appl) (lift (S O) O x4) x3))) H18)) t2 H13)))))))))))))) H10)) 
H9))))))))))))) y H1)))) H0))))))).
(* COMMENTS
Initial nodes: 3727
END *)

theorem sn3_appl_cast:
 \forall (c: C).(\forall (v: T).(\forall (u: T).((sn3 c (THead (Flat Appl) v 
u)) \to (\forall (t: T).((sn3 c (THead (Flat Appl) v t)) \to (sn3 c (THead 
(Flat Appl) v (THead (Flat Cast) u t))))))))
\def
 \lambda (c: C).(\lambda (v: T).(\lambda (u: T).(\lambda (H: (sn3 c (THead 
(Flat Appl) v u))).(insert_eq T (THead (Flat Appl) v u) (\lambda (t: T).(sn3 
c t)) (\lambda (_: T).(\forall (t0: T).((sn3 c (THead (Flat Appl) v t0)) \to 
(sn3 c (THead (Flat Appl) v (THead (Flat Cast) u t0)))))) (\lambda (y: 
T).(\lambda (H0: (sn3 c y)).(unintro T u (\lambda (t: T).((eq T y (THead 
(Flat Appl) v t)) \to (\forall (t0: T).((sn3 c (THead (Flat Appl) v t0)) \to 
(sn3 c (THead (Flat Appl) v (THead (Flat Cast) t t0))))))) (unintro T v 
(\lambda (t: T).(\forall (x: T).((eq T y (THead (Flat Appl) t x)) \to 
(\forall (t0: T).((sn3 c (THead (Flat Appl) t t0)) \to (sn3 c (THead (Flat 
Appl) t (THead (Flat Cast) x t0)))))))) (sn3_ind c (\lambda (t: T).(\forall 
(x: T).(\forall (x0: T).((eq T t (THead (Flat Appl) x x0)) \to (\forall (t0: 
T).((sn3 c (THead (Flat Appl) x t0)) \to (sn3 c (THead (Flat Appl) x (THead 
(Flat Cast) x0 t0))))))))) (\lambda (t1: T).(\lambda (H1: ((\forall (t2: 
T).((((eq T t1 t2) \to (\forall (P: Prop).P))) \to ((pr3 c t1 t2) \to (sn3 c 
t2)))))).(\lambda (H2: ((\forall (t2: T).((((eq T t1 t2) \to (\forall (P: 
Prop).P))) \to ((pr3 c t1 t2) \to (\forall (x: T).(\forall (x0: T).((eq T t2 
(THead (Flat Appl) x x0)) \to (\forall (t: T).((sn3 c (THead (Flat Appl) x 
t)) \to (sn3 c (THead (Flat Appl) x (THead (Flat Cast) x0 
t))))))))))))).(\lambda (x: T).(\lambda (x0: T).(\lambda (H3: (eq T t1 (THead 
(Flat Appl) x x0))).(\lambda (t: T).(\lambda (H4: (sn3 c (THead (Flat Appl) x 
t))).(insert_eq T (THead (Flat Appl) x t) (\lambda (t0: T).(sn3 c t0)) 
(\lambda (_: T).(sn3 c (THead (Flat Appl) x (THead (Flat Cast) x0 t)))) 
(\lambda (y0: T).(\lambda (H5: (sn3 c y0)).(unintro T t (\lambda (t0: T).((eq 
T y0 (THead (Flat Appl) x t0)) \to (sn3 c (THead (Flat Appl) x (THead (Flat 
Cast) x0 t0))))) (sn3_ind c (\lambda (t0: T).(\forall (x1: T).((eq T t0 
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
(* COMMENTS
Initial nodes: 5149
END *)

theorem sn3_appl_bind:
 \forall (b: B).((not (eq B b Abst)) \to (\forall (c: C).(\forall (u: 
T).((sn3 c u) \to (\forall (t: T).(\forall (v: T).((sn3 (CHead c (Bind b) u) 
(THead (Flat Appl) (lift (S O) O v) t)) \to (sn3 c (THead (Flat Appl) v 
(THead (Bind b) u t))))))))))
\def
 \lambda (b: B).(\lambda (H: (not (eq B b Abst))).(\lambda (c: C).(\lambda 
(u: T).(\lambda (H0: (sn3 c u)).(sn3_ind c (\lambda (t: T).(\forall (t0: 
T).(\forall (v: T).((sn3 (CHead c (Bind b) t) (THead (Flat Appl) (lift (S O) 
O v) t0)) \to (sn3 c (THead (Flat Appl) v (THead (Bind b) t t0))))))) 
(\lambda (t1: T).(\lambda (H1: ((\forall (t2: T).((((eq T t1 t2) \to (\forall 
(P: Prop).P))) \to ((pr3 c t1 t2) \to (sn3 c t2)))))).(\lambda (H2: ((\forall 
(t2: T).((((eq T t1 t2) \to (\forall (P: Prop).P))) \to ((pr3 c t1 t2) \to 
(\forall (t: T).(\forall (v: T).((sn3 (CHead c (Bind b) t2) (THead (Flat 
Appl) (lift (S O) O v) t)) \to (sn3 c (THead (Flat Appl) v (THead (Bind b) t2 
t))))))))))).(\lambda (t: T).(\lambda (v: T).(\lambda (H3: (sn3 (CHead c 
(Bind b) t1) (THead (Flat Appl) (lift (S O) O v) t))).(insert_eq T (THead 
(Flat Appl) (lift (S O) O v) t) (\lambda (t0: T).(sn3 (CHead c (Bind b) t1) 
t0)) (\lambda (_: T).(sn3 c (THead (Flat Appl) v (THead (Bind b) t1 t)))) 
(\lambda (y: T).(\lambda (H4: (sn3 (CHead c (Bind b) t1) y)).(unintro T t 
(\lambda (t0: T).((eq T y (THead (Flat Appl) (lift (S O) O v) t0)) \to (sn3 c 
(THead (Flat Appl) v (THead (Bind b) t1 t0))))) (unintro T v (\lambda (t0: 
T).(\forall (x: T).((eq T y (THead (Flat Appl) (lift (S O) O t0) x)) \to (sn3 
c (THead (Flat Appl) t0 (THead (Bind b) t1 x)))))) (sn3_ind (CHead c (Bind b) 
t1) (\lambda (t0: T).(\forall (x: T).(\forall (x0: T).((eq T t0 (THead (Flat 
Appl) (lift (S O) O x) x0)) \to (sn3 c (THead (Flat Appl) x (THead (Bind b) 
t1 x0))))))) (\lambda (t2: T).(\lambda (H5: ((\forall (t3: T).((((eq T t2 t3) 
\to (\forall (P: Prop).P))) \to ((pr3 (CHead c (Bind b) t1) t2 t3) \to (sn3 
(CHead c (Bind b) t1) t3)))))).(\lambda (H6: ((\forall (t3: T).((((eq T t2 
t3) \to (\forall (P: Prop).P))) \to ((pr3 (CHead c (Bind b) t1) t2 t3) \to 
(\forall (x: T).(\forall (x0: T).((eq T t3 (THead (Flat Appl) (lift (S O) O 
x) x0)) \to (sn3 c (THead (Flat Appl) x (THead (Bind b) t1 
x0))))))))))).(\lambda (x: T).(\lambda (x0: T).(\lambda (H7: (eq T t2 (THead 
(Flat Appl) (lift (S O) O x) x0))).(let H8 \def (eq_ind T t2 (\lambda (t0: 
T).(\forall (t3: T).((((eq T t0 t3) \to (\forall (P: Prop).P))) \to ((pr3 
(CHead c (Bind b) t1) t0 t3) \to (\forall (x1: T).(\forall (x2: T).((eq T t3 
(THead (Flat Appl) (lift (S O) O x1) x2)) \to (sn3 c (THead (Flat Appl) x1 
(THead (Bind b) t1 x2)))))))))) H6 (THead (Flat Appl) (lift (S O) O x) x0) 
H7) in (let H9 \def (eq_ind T t2 (\lambda (t0: T).(\forall (t3: T).((((eq T 
t0 t3) \to (\forall (P: Prop).P))) \to ((pr3 (CHead c (Bind b) t1) t0 t3) \to 
(sn3 (CHead c (Bind b) t1) t3))))) H5 (THead (Flat Appl) (lift (S O) O x) x0) 
H7) in (sn3_pr2_intro c (THead (Flat Appl) x (THead (Bind b) t1 x0)) (\lambda 
(t3: T).(\lambda (H10: (((eq T (THead (Flat Appl) x (THead (Bind b) t1 x0)) 
t3) \to (\forall (P: Prop).P)))).(\lambda (H11: (pr2 c (THead (Flat Appl) x 
(THead (Bind b) t1 x0)) t3)).(let H12 \def (pr2_gen_appl c x (THead (Bind b) 
t1 x0) t3 H11) in (or3_ind (ex3_2 T T (\lambda (u2: T).(\lambda (t4: T).(eq T 
t3 (THead (Flat Appl) u2 t4)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c x 
u2))) (\lambda (_: T).(\lambda (t4: T).(pr2 c (THead (Bind b) t1 x0) t4)))) 
(ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: 
T).(eq T (THead (Bind b) t1 x0) (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t4: T).(eq T t3 (THead (Bind 
Abbr) u2 t4)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr2 c x u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t4: T).(\forall (b0: B).(\forall (u0: T).(pr2 (CHead c (Bind b0) 
u0) z1 t4)))))))) (ex6_6 B T T T T T (\lambda (b0: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B 
b0 Abst)))))))) (\lambda (b0: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind b) t1 x0) (THead 
(Bind b0) y1 z1)))))))) (\lambda (b0: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T t3 (THead (Bind 
b0) y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr2 c x u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 y2))))))) 
(\lambda (b0: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda 
(_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b0) y2) z1 z2)))))))) (sn3 c t3) 
(\lambda (H13: (ex3_2 T T (\lambda (u2: T).(\lambda (t4: T).(eq T t3 (THead 
(Flat Appl) u2 t4)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c x u2))) 
(\lambda (_: T).(\lambda (t4: T).(pr2 c (THead (Bind b) t1 x0) 
t4))))).(ex3_2_ind T T (\lambda (u2: T).(\lambda (t4: T).(eq T t3 (THead 
(Flat Appl) u2 t4)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c x u2))) 
(\lambda (_: T).(\lambda (t4: T).(pr2 c (THead (Bind b) t1 x0) t4))) (sn3 c 
t3) (\lambda (x1: T).(\lambda (x2: T).(\lambda (H14: (eq T t3 (THead (Flat 
Appl) x1 x2))).(\lambda (H15: (pr2 c x x1)).(\lambda (H16: (pr2 c (THead 
(Bind b) t1 x0) x2)).(let H17 \def (eq_ind T t3 (\lambda (t0: T).((eq T 
(THead (Flat Appl) x (THead (Bind b) t1 x0)) t0) \to (\forall (P: Prop).P))) 
H10 (THead (Flat Appl) x1 x2) H14) in (eq_ind_r T (THead (Flat Appl) x1 x2) 
(\lambda (t0: T).(sn3 c t0)) (let H_x \def (pr3_gen_bind b H c t1 x0 x2) in 
(let H18 \def (H_x (pr3_pr2 c (THead (Bind b) t1 x0) x2 H16)) in (or_ind 
(ex3_2 T T (\lambda (u2: T).(\lambda (t4: T).(eq T x2 (THead (Bind b) u2 
t4)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c t1 u2))) (\lambda (_: 
T).(\lambda (t4: T).(pr3 (CHead c (Bind b) t1) x0 t4)))) (pr3 (CHead c (Bind 
b) t1) x0 (lift (S O) O x2)) (sn3 c (THead (Flat Appl) x1 x2)) (\lambda (H19: 
(ex3_2 T T (\lambda (u2: T).(\lambda (t4: T).(eq T x2 (THead (Bind b) u2 
t4)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c t1 u2))) (\lambda (_: 
T).(\lambda (t4: T).(pr3 (CHead c (Bind b) t1) x0 t4))))).(ex3_2_ind T T 
(\lambda (u2: T).(\lambda (t4: T).(eq T x2 (THead (Bind b) u2 t4)))) (\lambda 
(u2: T).(\lambda (_: T).(pr3 c t1 u2))) (\lambda (_: T).(\lambda (t4: T).(pr3 
(CHead c (Bind b) t1) x0 t4))) (sn3 c (THead (Flat Appl) x1 x2)) (\lambda 
(x3: T).(\lambda (x4: T).(\lambda (H20: (eq T x2 (THead (Bind b) x3 
x4))).(\lambda (H21: (pr3 c t1 x3)).(\lambda (H22: (pr3 (CHead c (Bind b) t1) 
x0 x4)).(let H23 \def (eq_ind T x2 (\lambda (t0: T).((eq T (THead (Flat Appl) 
x (THead (Bind b) t1 x0)) (THead (Flat Appl) x1 t0)) \to (\forall (P: 
Prop).P))) H17 (THead (Bind b) x3 x4) H20) in (eq_ind_r T (THead (Bind b) x3 
x4) (\lambda (t0: T).(sn3 c (THead (Flat Appl) x1 t0))) (let H_x0 \def 
(term_dec t1 x3) in (let H24 \def H_x0 in (or_ind (eq T t1 x3) ((eq T t1 x3) 
\to (\forall (P: Prop).P)) (sn3 c (THead (Flat Appl) x1 (THead (Bind b) x3 
x4))) (\lambda (H25: (eq T t1 x3)).(let H26 \def (eq_ind_r T x3 (\lambda (t0: 
T).((eq T (THead (Flat Appl) x (THead (Bind b) t1 x0)) (THead (Flat Appl) x1 
(THead (Bind b) t0 x4))) \to (\forall (P: Prop).P))) H23 t1 H25) in (let H27 
\def (eq_ind_r T x3 (\lambda (t0: T).(pr3 c t1 t0)) H21 t1 H25) in (eq_ind T 
t1 (\lambda (t0: T).(sn3 c (THead (Flat Appl) x1 (THead (Bind b) t0 x4)))) 
(let H_x1 \def (term_dec x0 x4) in (let H28 \def H_x1 in (or_ind (eq T x0 x4) 
((eq T x0 x4) \to (\forall (P: Prop).P)) (sn3 c (THead (Flat Appl) x1 (THead 
(Bind b) t1 x4))) (\lambda (H29: (eq T x0 x4)).(let H30 \def (eq_ind_r T x4 
(\lambda (t0: T).((eq T (THead (Flat Appl) x (THead (Bind b) t1 x0)) (THead 
(Flat Appl) x1 (THead (Bind b) t1 t0))) \to (\forall (P: Prop).P))) H26 x0 
H29) in (let H31 \def (eq_ind_r T x4 (\lambda (t0: T).(pr3 (CHead c (Bind b) 
t1) x0 t0)) H22 x0 H29) in (eq_ind T x0 (\lambda (t0: T).(sn3 c (THead (Flat 
Appl) x1 (THead (Bind b) t1 t0)))) (let H_x2 \def (term_dec x x1) in (let H32 
\def H_x2 in (or_ind (eq T x x1) ((eq T x x1) \to (\forall (P: Prop).P)) (sn3 
c (THead (Flat Appl) x1 (THead (Bind b) t1 x0))) (\lambda (H33: (eq T x 
x1)).(let H34 \def (eq_ind_r T x1 (\lambda (t0: T).((eq T (THead (Flat Appl) 
x (THead (Bind b) t1 x0)) (THead (Flat Appl) t0 (THead (Bind b) t1 x0))) \to 
(\forall (P: Prop).P))) H30 x H33) in (let H35 \def (eq_ind_r T x1 (\lambda 
(t0: T).(pr2 c x t0)) H15 x H33) in (eq_ind T x (\lambda (t0: T).(sn3 c 
(THead (Flat Appl) t0 (THead (Bind b) t1 x0)))) (H34 (refl_equal T (THead 
(Flat Appl) x (THead (Bind b) t1 x0))) (sn3 c (THead (Flat Appl) x (THead 
(Bind b) t1 x0)))) x1 H33)))) (\lambda (H33: (((eq T x x1) \to (\forall (P: 
Prop).P)))).(H8 (THead (Flat Appl) (lift (S O) O x1) x0) (\lambda (H34: (eq T 
(THead (Flat Appl) (lift (S O) O x) x0) (THead (Flat Appl) (lift (S O) O x1) 
x0))).(\lambda (P: Prop).(let H35 \def (f_equal T T (\lambda (e: T).(match e 
in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow ((let rec lref_map 
(f: ((nat \to nat))) (d: nat) (t0: T) on t0: T \def (match t0 with [(TSort n) 
\Rightarrow (TSort n) | (TLRef i) \Rightarrow (TLRef (match (blt i d) with 
[true \Rightarrow i | false \Rightarrow (f i)])) | (THead k u0 t4) 
\Rightarrow (THead k (lref_map f d u0) (lref_map f (s k d) t4))]) in 
lref_map) (\lambda (x5: nat).(plus x5 (S O))) O x) | (TLRef _) \Rightarrow 
((let rec lref_map (f: ((nat \to nat))) (d: nat) (t0: T) on t0: T \def (match 
t0 with [(TSort n) \Rightarrow (TSort n) | (TLRef i) \Rightarrow (TLRef 
(match (blt i d) with [true \Rightarrow i | false \Rightarrow (f i)])) | 
(THead k u0 t4) \Rightarrow (THead k (lref_map f d u0) (lref_map f (s k d) 
t4))]) in lref_map) (\lambda (x5: nat).(plus x5 (S O))) O x) | (THead _ t0 _) 
\Rightarrow t0])) (THead (Flat Appl) (lift (S O) O x) x0) (THead (Flat Appl) 
(lift (S O) O x1) x0) H34) in (let H36 \def (eq_ind_r T x1 (\lambda (t0: 
T).((eq T x t0) \to (\forall (P0: Prop).P0))) H33 x (lift_inj x x1 (S O) O 
H35)) in (let H37 \def (eq_ind_r T x1 (\lambda (t0: T).(pr2 c x t0)) H15 x 
(lift_inj x x1 (S O) O H35)) in (H36 (refl_equal T x) P)))))) (pr3_flat 
(CHead c (Bind b) t1) (lift (S O) O x) (lift (S O) O x1) (pr3_lift (CHead c 
(Bind b) t1) c (S O) O (drop_drop (Bind b) O c c (drop_refl c) t1) x x1 
(pr3_pr2 c x x1 H15)) x0 x0 (pr3_refl (CHead c (Bind b) t1) x0) Appl) x1 x0 
(refl_equal T (THead (Flat Appl) (lift (S O) O x1) x0)))) H32))) x4 H29)))) 
(\lambda (H29: (((eq T x0 x4) \to (\forall (P: Prop).P)))).(H8 (THead (Flat 
Appl) (lift (S O) O x1) x4) (\lambda (H30: (eq T (THead (Flat Appl) (lift (S 
O) O x) x0) (THead (Flat Appl) (lift (S O) O x1) x4))).(\lambda (P: 
Prop).(let H31 \def (f_equal T T (\lambda (e: T).(match e in T return 
(\lambda (_: T).T) with [(TSort _) \Rightarrow ((let rec lref_map (f: ((nat 
\to nat))) (d: nat) (t0: T) on t0: T \def (match t0 with [(TSort n) 
\Rightarrow (TSort n) | (TLRef i) \Rightarrow (TLRef (match (blt i d) with 
[true \Rightarrow i | false \Rightarrow (f i)])) | (THead k u0 t4) 
\Rightarrow (THead k (lref_map f d u0) (lref_map f (s k d) t4))]) in 
lref_map) (\lambda (x5: nat).(plus x5 (S O))) O x) | (TLRef _) \Rightarrow 
((let rec lref_map (f: ((nat \to nat))) (d: nat) (t0: T) on t0: T \def (match 
t0 with [(TSort n) \Rightarrow (TSort n) | (TLRef i) \Rightarrow (TLRef 
(match (blt i d) with [true \Rightarrow i | false \Rightarrow (f i)])) | 
(THead k u0 t4) \Rightarrow (THead k (lref_map f d u0) (lref_map f (s k d) 
t4))]) in lref_map) (\lambda (x5: nat).(plus x5 (S O))) O x) | (THead _ t0 _) 
\Rightarrow t0])) (THead (Flat Appl) (lift (S O) O x) x0) (THead (Flat Appl) 
(lift (S O) O x1) x4) H30) in ((let H32 \def (f_equal T T (\lambda (e: 
T).(match e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow x0 | 
(TLRef _) \Rightarrow x0 | (THead _ _ t0) \Rightarrow t0])) (THead (Flat 
Appl) (lift (S O) O x) x0) (THead (Flat Appl) (lift (S O) O x1) x4) H30) in 
(\lambda (H33: (eq T (lift (S O) O x) (lift (S O) O x1))).(let H34 \def 
(eq_ind_r T x4 (\lambda (t0: T).((eq T x0 t0) \to (\forall (P0: Prop).P0))) 
H29 x0 H32) in (let H35 \def (eq_ind_r T x4 (\lambda (t0: T).((eq T (THead 
(Flat Appl) x (THead (Bind b) t1 x0)) (THead (Flat Appl) x1 (THead (Bind b) 
t1 t0))) \to (\forall (P0: Prop).P0))) H26 x0 H32) in (let H36 \def (eq_ind_r 
T x4 (\lambda (t0: T).(pr3 (CHead c (Bind b) t1) x0 t0)) H22 x0 H32) in (let 
H37 \def (eq_ind_r T x1 (\lambda (t0: T).((eq T (THead (Flat Appl) x (THead 
(Bind b) t1 x0)) (THead (Flat Appl) t0 (THead (Bind b) t1 x0))) \to (\forall 
(P0: Prop).P0))) H35 x (lift_inj x x1 (S O) O H33)) in (let H38 \def 
(eq_ind_r T x1 (\lambda (t0: T).(pr2 c x t0)) H15 x (lift_inj x x1 (S O) O 
H33)) in (H34 (refl_equal T x0) P)))))))) H31)))) (pr3_flat (CHead c (Bind b) 
t1) (lift (S O) O x) (lift (S O) O x1) (pr3_lift (CHead c (Bind b) t1) c (S 
O) O (drop_drop (Bind b) O c c (drop_refl c) t1) x x1 (pr3_pr2 c x x1 H15)) 
x0 x4 H22 Appl) x1 x4 (refl_equal T (THead (Flat Appl) (lift (S O) O x1) 
x4)))) H28))) x3 H25)))) (\lambda (H25: (((eq T t1 x3) \to (\forall (P: 
Prop).P)))).(H2 x3 H25 H21 x4 x1 (sn3_cpr3_trans c t1 x3 H21 (Bind b) (THead 
(Flat Appl) (lift (S O) O x1) x4) (let H_x1 \def (term_dec x0 x4) in (let H26 
\def H_x1 in (or_ind (eq T x0 x4) ((eq T x0 x4) \to (\forall (P: Prop).P)) 
(sn3 (CHead c (Bind b) t1) (THead (Flat Appl) (lift (S O) O x1) x4)) (\lambda 
(H27: (eq T x0 x4)).(let H28 \def (eq_ind_r T x4 (\lambda (t0: T).(pr3 (CHead 
c (Bind b) t1) x0 t0)) H22 x0 H27) in (eq_ind T x0 (\lambda (t0: T).(sn3 
(CHead c (Bind b) t1) (THead (Flat Appl) (lift (S O) O x1) t0))) (let H_x2 
\def (term_dec x x1) in (let H29 \def H_x2 in (or_ind (eq T x x1) ((eq T x 
x1) \to (\forall (P: Prop).P)) (sn3 (CHead c (Bind b) t1) (THead (Flat Appl) 
(lift (S O) O x1) x0)) (\lambda (H30: (eq T x x1)).(let H31 \def (eq_ind_r T 
x1 (\lambda (t0: T).(pr2 c x t0)) H15 x H30) in (eq_ind T x (\lambda (t0: 
T).(sn3 (CHead c (Bind b) t1) (THead (Flat Appl) (lift (S O) O t0) x0))) 
(sn3_sing (CHead c (Bind b) t1) (THead (Flat Appl) (lift (S O) O x) x0) H9) 
x1 H30))) (\lambda (H30: (((eq T x x1) \to (\forall (P: Prop).P)))).(H9 
(THead (Flat Appl) (lift (S O) O x1) x0) (\lambda (H31: (eq T (THead (Flat 
Appl) (lift (S O) O x) x0) (THead (Flat Appl) (lift (S O) O x1) 
x0))).(\lambda (P: Prop).(let H32 \def (f_equal T T (\lambda (e: T).(match e 
in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow ((let rec lref_map 
(f: ((nat \to nat))) (d: nat) (t0: T) on t0: T \def (match t0 with [(TSort n) 
\Rightarrow (TSort n) | (TLRef i) \Rightarrow (TLRef (match (blt i d) with 
[true \Rightarrow i | false \Rightarrow (f i)])) | (THead k u0 t4) 
\Rightarrow (THead k (lref_map f d u0) (lref_map f (s k d) t4))]) in 
lref_map) (\lambda (x5: nat).(plus x5 (S O))) O x) | (TLRef _) \Rightarrow 
((let rec lref_map (f: ((nat \to nat))) (d: nat) (t0: T) on t0: T \def (match 
t0 with [(TSort n) \Rightarrow (TSort n) | (TLRef i) \Rightarrow (TLRef 
(match (blt i d) with [true \Rightarrow i | false \Rightarrow (f i)])) | 
(THead k u0 t4) \Rightarrow (THead k (lref_map f d u0) (lref_map f (s k d) 
t4))]) in lref_map) (\lambda (x5: nat).(plus x5 (S O))) O x) | (THead _ t0 _) 
\Rightarrow t0])) (THead (Flat Appl) (lift (S O) O x) x0) (THead (Flat Appl) 
(lift (S O) O x1) x0) H31) in (let H33 \def (eq_ind_r T x1 (\lambda (t0: 
T).((eq T x t0) \to (\forall (P0: Prop).P0))) H30 x (lift_inj x x1 (S O) O 
H32)) in (let H34 \def (eq_ind_r T x1 (\lambda (t0: T).(pr2 c x t0)) H15 x 
(lift_inj x x1 (S O) O H32)) in (H33 (refl_equal T x) P)))))) (pr3_flat 
(CHead c (Bind b) t1) (lift (S O) O x) (lift (S O) O x1) (pr3_lift (CHead c 
(Bind b) t1) c (S O) O (drop_drop (Bind b) O c c (drop_refl c) t1) x x1 
(pr3_pr2 c x x1 H15)) x0 x0 (pr3_refl (CHead c (Bind b) t1) x0) Appl))) 
H29))) x4 H27))) (\lambda (H27: (((eq T x0 x4) \to (\forall (P: 
Prop).P)))).(H9 (THead (Flat Appl) (lift (S O) O x1) x4) (\lambda (H28: (eq T 
(THead (Flat Appl) (lift (S O) O x) x0) (THead (Flat Appl) (lift (S O) O x1) 
x4))).(\lambda (P: Prop).(let H29 \def (f_equal T T (\lambda (e: T).(match e 
in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow ((let rec lref_map 
(f: ((nat \to nat))) (d: nat) (t0: T) on t0: T \def (match t0 with [(TSort n) 
\Rightarrow (TSort n) | (TLRef i) \Rightarrow (TLRef (match (blt i d) with 
[true \Rightarrow i | false \Rightarrow (f i)])) | (THead k u0 t4) 
\Rightarrow (THead k (lref_map f d u0) (lref_map f (s k d) t4))]) in 
lref_map) (\lambda (x5: nat).(plus x5 (S O))) O x) | (TLRef _) \Rightarrow 
((let rec lref_map (f: ((nat \to nat))) (d: nat) (t0: T) on t0: T \def (match 
t0 with [(TSort n) \Rightarrow (TSort n) | (TLRef i) \Rightarrow (TLRef 
(match (blt i d) with [true \Rightarrow i | false \Rightarrow (f i)])) | 
(THead k u0 t4) \Rightarrow (THead k (lref_map f d u0) (lref_map f (s k d) 
t4))]) in lref_map) (\lambda (x5: nat).(plus x5 (S O))) O x) | (THead _ t0 _) 
\Rightarrow t0])) (THead (Flat Appl) (lift (S O) O x) x0) (THead (Flat Appl) 
(lift (S O) O x1) x4) H28) in ((let H30 \def (f_equal T T (\lambda (e: 
T).(match e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow x0 | 
(TLRef _) \Rightarrow x0 | (THead _ _ t0) \Rightarrow t0])) (THead (Flat 
Appl) (lift (S O) O x) x0) (THead (Flat Appl) (lift (S O) O x1) x4) H28) in 
(\lambda (H31: (eq T (lift (S O) O x) (lift (S O) O x1))).(let H32 \def 
(eq_ind_r T x4 (\lambda (t0: T).((eq T x0 t0) \to (\forall (P0: Prop).P0))) 
H27 x0 H30) in (let H33 \def (eq_ind_r T x4 (\lambda (t0: T).(pr3 (CHead c 
(Bind b) t1) x0 t0)) H22 x0 H30) in (let H34 \def (eq_ind_r T x1 (\lambda 
(t0: T).(pr2 c x t0)) H15 x (lift_inj x x1 (S O) O H31)) in (H32 (refl_equal 
T x0) P)))))) H29)))) (pr3_flat (CHead c (Bind b) t1) (lift (S O) O x) (lift 
(S O) O x1) (pr3_lift (CHead c (Bind b) t1) c (S O) O (drop_drop (Bind b) O c 
c (drop_refl c) t1) x x1 (pr3_pr2 c x x1 H15)) x0 x4 H22 Appl))) H26)))))) 
H24))) x2 H20))))))) H19)) (\lambda (H19: (pr3 (CHead c (Bind b) t1) x0 (lift 
(S O) O x2))).(sn3_gen_lift (CHead c (Bind b) t1) (THead (Flat Appl) x1 x2) 
(S O) O (eq_ind_r T (THead (Flat Appl) (lift (S O) O x1) (lift (S O) (s (Flat 
Appl) O) x2)) (\lambda (t0: T).(sn3 (CHead c (Bind b) t1) t0)) (sn3_pr3_trans 
(CHead c (Bind b) t1) (THead (Flat Appl) (lift (S O) O x1) x0) (let H_x0 \def 
(term_dec x x1) in (let H20 \def H_x0 in (or_ind (eq T x x1) ((eq T x x1) \to 
(\forall (P: Prop).P)) (sn3 (CHead c (Bind b) t1) (THead (Flat Appl) (lift (S 
O) O x1) x0)) (\lambda (H21: (eq T x x1)).(let H22 \def (eq_ind_r T x1 
(\lambda (t0: T).(pr2 c x t0)) H15 x H21) in (eq_ind T x (\lambda (t0: 
T).(sn3 (CHead c (Bind b) t1) (THead (Flat Appl) (lift (S O) O t0) x0))) 
(sn3_sing (CHead c (Bind b) t1) (THead (Flat Appl) (lift (S O) O x) x0) H9) 
x1 H21))) (\lambda (H21: (((eq T x x1) \to (\forall (P: Prop).P)))).(H9 
(THead (Flat Appl) (lift (S O) O x1) x0) (\lambda (H22: (eq T (THead (Flat 
Appl) (lift (S O) O x) x0) (THead (Flat Appl) (lift (S O) O x1) 
x0))).(\lambda (P: Prop).(let H23 \def (f_equal T T (\lambda (e: T).(match e 
in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow ((let rec lref_map 
(f: ((nat \to nat))) (d: nat) (t0: T) on t0: T \def (match t0 with [(TSort n) 
\Rightarrow (TSort n) | (TLRef i) \Rightarrow (TLRef (match (blt i d) with 
[true \Rightarrow i | false \Rightarrow (f i)])) | (THead k u0 t4) 
\Rightarrow (THead k (lref_map f d u0) (lref_map f (s k d) t4))]) in 
lref_map) (\lambda (x3: nat).(plus x3 (S O))) O x) | (TLRef _) \Rightarrow 
((let rec lref_map (f: ((nat \to nat))) (d: nat) (t0: T) on t0: T \def (match 
t0 with [(TSort n) \Rightarrow (TSort n) | (TLRef i) \Rightarrow (TLRef 
(match (blt i d) with [true \Rightarrow i | false \Rightarrow (f i)])) | 
(THead k u0 t4) \Rightarrow (THead k (lref_map f d u0) (lref_map f (s k d) 
t4))]) in lref_map) (\lambda (x3: nat).(plus x3 (S O))) O x) | (THead _ t0 _) 
\Rightarrow t0])) (THead (Flat Appl) (lift (S O) O x) x0) (THead (Flat Appl) 
(lift (S O) O x1) x0) H22) in (let H24 \def (eq_ind_r T x1 (\lambda (t0: 
T).((eq T x t0) \to (\forall (P0: Prop).P0))) H21 x (lift_inj x x1 (S O) O 
H23)) in (let H25 \def (eq_ind_r T x1 (\lambda (t0: T).(pr2 c x t0)) H15 x 
(lift_inj x x1 (S O) O H23)) in (H24 (refl_equal T x) P)))))) (pr3_flat 
(CHead c (Bind b) t1) (lift (S O) O x) (lift (S O) O x1) (pr3_lift (CHead c 
(Bind b) t1) c (S O) O (drop_drop (Bind b) O c c (drop_refl c) t1) x x1 
(pr3_pr2 c x x1 H15)) x0 x0 (pr3_refl (CHead c (Bind b) t1) x0) Appl))) 
H20))) (THead (Flat Appl) (lift (S O) O x1) (lift (S O) O x2)) (pr3_thin_dx 
(CHead c (Bind b) t1) x0 (lift (S O) O x2) H19 (lift (S O) O x1) Appl)) (lift 
(S O) O (THead (Flat Appl) x1 x2)) (lift_head (Flat Appl) x1 x2 (S O) O)) c 
(drop_drop (Bind b) O c c (drop_refl c) t1))) H18))) t3 H14))))))) H13)) 
(\lambda (H13: (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(eq T (THead (Bind b) t1 x0) (THead (Bind Abst) y1 
z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t4: 
T).(eq T t3 (THead (Bind Abbr) u2 t4)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c x u2))))) (\lambda (_: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (t4: T).(\forall (b0: B).(\forall (u0: 
T).(pr2 (CHead c (Bind b0) u0) z1 t4))))))))).(ex4_4_ind T T T T (\lambda 
(y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind 
b) t1 x0) (THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (t4: T).(eq T t3 (THead (Bind Abbr) u2 t4)))))) 
(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c x 
u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t4: 
T).(\forall (b0: B).(\forall (u0: T).(pr2 (CHead c (Bind b0) u0) z1 t4))))))) 
(sn3 c t3) (\lambda (x1: T).(\lambda (x2: T).(\lambda (x3: T).(\lambda (x4: 
T).(\lambda (H14: (eq T (THead (Bind b) t1 x0) (THead (Bind Abst) x1 
x2))).(\lambda (H15: (eq T t3 (THead (Bind Abbr) x3 x4))).(\lambda (_: (pr2 c 
x x3)).(\lambda (H17: ((\forall (b0: B).(\forall (u0: T).(pr2 (CHead c (Bind 
b0) u0) x2 x4))))).(let H18 \def (eq_ind T t3 (\lambda (t0: T).((eq T (THead 
(Flat Appl) x (THead (Bind b) t1 x0)) t0) \to (\forall (P: Prop).P))) H10 
(THead (Bind Abbr) x3 x4) H15) in (eq_ind_r T (THead (Bind Abbr) x3 x4) 
(\lambda (t0: T).(sn3 c t0)) (let H19 \def (f_equal T B (\lambda (e: 
T).(match e in T return (\lambda (_: T).B) with [(TSort _) \Rightarrow b | 
(TLRef _) \Rightarrow b | (THead k _ _) \Rightarrow (match k in K return 
(\lambda (_: K).B) with [(Bind b0) \Rightarrow b0 | (Flat _) \Rightarrow 
b])])) (THead (Bind b) t1 x0) (THead (Bind Abst) x1 x2) H14) in ((let H20 
\def (f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) 
with [(TSort _) \Rightarrow t1 | (TLRef _) \Rightarrow t1 | (THead _ t0 _) 
\Rightarrow t0])) (THead (Bind b) t1 x0) (THead (Bind Abst) x1 x2) H14) in 
((let H21 \def (f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: 
T).T) with [(TSort _) \Rightarrow x0 | (TLRef _) \Rightarrow x0 | (THead _ _ 
t0) \Rightarrow t0])) (THead (Bind b) t1 x0) (THead (Bind Abst) x1 x2) H14) 
in (\lambda (_: (eq T t1 x1)).(\lambda (H23: (eq B b Abst)).(let H24 \def 
(eq_ind_r T x2 (\lambda (t0: T).(\forall (b0: B).(\forall (u0: T).(pr2 (CHead 
c (Bind b0) u0) t0 x4)))) H17 x0 H21) in (let H25 \def (eq_ind B b (\lambda 
(b0: B).((eq T (THead (Flat Appl) x (THead (Bind b0) t1 x0)) (THead (Bind 
Abbr) x3 x4)) \to (\forall (P: Prop).P))) H18 Abst H23) in (let H26 \def 
(eq_ind B b (\lambda (b0: B).(\forall (t4: T).((((eq T (THead (Flat Appl) 
(lift (S O) O x) x0) t4) \to (\forall (P: Prop).P))) \to ((pr3 (CHead c (Bind 
b0) t1) (THead (Flat Appl) (lift (S O) O x) x0) t4) \to (sn3 (CHead c (Bind 
b0) t1) t4))))) H9 Abst H23) in (let H27 \def (eq_ind B b (\lambda (b0: 
B).(\forall (t4: T).((((eq T (THead (Flat Appl) (lift (S O) O x) x0) t4) \to 
(\forall (P: Prop).P))) \to ((pr3 (CHead c (Bind b0) t1) (THead (Flat Appl) 
(lift (S O) O x) x0) t4) \to (\forall (x5: T).(\forall (x6: T).((eq T t4 
(THead (Flat Appl) (lift (S O) O x5) x6)) \to (sn3 c (THead (Flat Appl) x5 
(THead (Bind b0) t1 x6)))))))))) H8 Abst H23) in (let H28 \def (eq_ind B b 
(\lambda (b0: B).(\forall (t4: T).((((eq T t1 t4) \to (\forall (P: Prop).P))) 
\to ((pr3 c t1 t4) \to (\forall (t0: T).(\forall (v0: T).((sn3 (CHead c (Bind 
b0) t4) (THead (Flat Appl) (lift (S O) O v0) t0)) \to (sn3 c (THead (Flat 
Appl) v0 (THead (Bind b0) t4 t0)))))))))) H2 Abst H23) in (let H29 \def 
(eq_ind B b (\lambda (b0: B).(not (eq B b0 Abst))) H Abst H23) in (let H30 
\def (match (H29 (refl_equal B Abst)) in False return (\lambda (_: 
False).(sn3 c (THead (Bind Abbr) x3 x4))) with []) in H30)))))))))) H20)) 
H19)) t3 H15)))))))))) H13)) (\lambda (H13: (ex6_6 B T T T T T (\lambda (b0: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(not (eq B b0 Abst)))))))) (\lambda (b0: B).(\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind b) 
t1 x0) (THead (Bind b0) y1 z1)))))))) (\lambda (b0: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T 
t3 (THead (Bind b0) y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) 
(\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr2 c x u2))))))) (\lambda (_: B).(\lambda (y1: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 
y2))))))) (\lambda (b0: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b0) y2) z1 
z2))))))))).(ex6_6_ind B T T T T T (\lambda (b0: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b0 
Abst)))))))) (\lambda (b0: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind b) t1 x0) (THead (Bind 
b0) y1 z1)))))))) (\lambda (b0: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T t3 (THead (Bind b0) y2 (THead 
(Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c x 
u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 y2))))))) (\lambda (b0: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 (CHead c (Bind b0) y2) z1 z2))))))) (sn3 c t3) (\lambda (x1: 
B).(\lambda (x2: T).(\lambda (x3: T).(\lambda (x4: T).(\lambda (x5: 
T).(\lambda (x6: T).(\lambda (_: (not (eq B x1 Abst))).(\lambda (H15: (eq T 
(THead (Bind b) t1 x0) (THead (Bind x1) x2 x3))).(\lambda (H16: (eq T t3 
(THead (Bind x1) x6 (THead (Flat Appl) (lift (S O) O x5) x4)))).(\lambda 
(H17: (pr2 c x x5)).(\lambda (H18: (pr2 c x2 x6)).(\lambda (H19: (pr2 (CHead 
c (Bind x1) x6) x3 x4)).(let H20 \def (eq_ind T t3 (\lambda (t0: T).((eq T 
(THead (Flat Appl) x (THead (Bind b) t1 x0)) t0) \to (\forall (P: Prop).P))) 
H10 (THead (Bind x1) x6 (THead (Flat Appl) (lift (S O) O x5) x4)) H16) in 
(eq_ind_r T (THead (Bind x1) x6 (THead (Flat Appl) (lift (S O) O x5) x4)) 
(\lambda (t0: T).(sn3 c t0)) (let H21 \def (f_equal T B (\lambda (e: 
T).(match e in T return (\lambda (_: T).B) with [(TSort _) \Rightarrow b | 
(TLRef _) \Rightarrow b | (THead k _ _) \Rightarrow (match k in K return 
(\lambda (_: K).B) with [(Bind b0) \Rightarrow b0 | (Flat _) \Rightarrow 
b])])) (THead (Bind b) t1 x0) (THead (Bind x1) x2 x3) H15) in ((let H22 \def 
(f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) with 
[(TSort _) \Rightarrow t1 | (TLRef _) \Rightarrow t1 | (THead _ t0 _) 
\Rightarrow t0])) (THead (Bind b) t1 x0) (THead (Bind x1) x2 x3) H15) in 
((let H23 \def (f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: 
T).T) with [(TSort _) \Rightarrow x0 | (TLRef _) \Rightarrow x0 | (THead _ _ 
t0) \Rightarrow t0])) (THead (Bind b) t1 x0) (THead (Bind x1) x2 x3) H15) in 
(\lambda (H24: (eq T t1 x2)).(\lambda (H25: (eq B b x1)).(let H26 \def 
(eq_ind_r T x3 (\lambda (t0: T).(pr2 (CHead c (Bind x1) x6) t0 x4)) H19 x0 
H23) in (let H27 \def (eq_ind_r T x2 (\lambda (t0: T).(pr2 c t0 x6)) H18 t1 
H24) in (let H28 \def (eq_ind_r B x1 (\lambda (b0: B).(pr2 (CHead c (Bind b0) 
x6) x0 x4)) H26 b H25) in (eq_ind B b (\lambda (b0: B).(sn3 c (THead (Bind 
b0) x6 (THead (Flat Appl) (lift (S O) O x5) x4)))) (sn3_pr3_trans c (THead 
(Bind b) t1 (THead (Flat Appl) (lift (S O) O x5) x4)) (sn3_bind b c t1 
(sn3_sing c t1 H1) (THead (Flat Appl) (lift (S O) O x5) x4) (let H_x \def 
(term_dec x x5) in (let H29 \def H_x in (or_ind (eq T x x5) ((eq T x x5) \to 
(\forall (P: Prop).P)) (sn3 (CHead c (Bind b) t1) (THead (Flat Appl) (lift (S 
O) O x5) x4)) (\lambda (H30: (eq T x x5)).(let H31 \def (eq_ind_r T x5 
(\lambda (t0: T).(pr2 c x t0)) H17 x H30) in (eq_ind T x (\lambda (t0: 
T).(sn3 (CHead c (Bind b) t1) (THead (Flat Appl) (lift (S O) O t0) x4))) (let 
H_x0 \def (term_dec x0 x4) in (let H32 \def H_x0 in (or_ind (eq T x0 x4) ((eq 
T x0 x4) \to (\forall (P: Prop).P)) (sn3 (CHead c (Bind b) t1) (THead (Flat 
Appl) (lift (S O) O x) x4)) (\lambda (H33: (eq T x0 x4)).(let H34 \def 
(eq_ind_r T x4 (\lambda (t0: T).(pr2 (CHead c (Bind b) x6) x0 t0)) H28 x0 
H33) in (eq_ind T x0 (\lambda (t0: T).(sn3 (CHead c (Bind b) t1) (THead (Flat 
Appl) (lift (S O) O x) t0))) (sn3_sing (CHead c (Bind b) t1) (THead (Flat 
Appl) (lift (S O) O x) x0) H9) x4 H33))) (\lambda (H33: (((eq T x0 x4) \to 
(\forall (P: Prop).P)))).(H9 (THead (Flat Appl) (lift (S O) O x) x4) (\lambda 
(H34: (eq T (THead (Flat Appl) (lift (S O) O x) x0) (THead (Flat Appl) (lift 
(S O) O x) x4))).(\lambda (P: Prop).(let H35 \def (f_equal T T (\lambda (e: 
T).(match e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow x0 | 
(TLRef _) \Rightarrow x0 | (THead _ _ t0) \Rightarrow t0])) (THead (Flat 
Appl) (lift (S O) O x) x0) (THead (Flat Appl) (lift (S O) O x) x4) H34) in 
(let H36 \def (eq_ind_r T x4 (\lambda (t0: T).((eq T x0 t0) \to (\forall (P0: 
Prop).P0))) H33 x0 H35) in (let H37 \def (eq_ind_r T x4 (\lambda (t0: T).(pr2 
(CHead c (Bind b) x6) x0 t0)) H28 x0 H35) in (H36 (refl_equal T x0) P)))))) 
(pr3_pr3_pr3_t c t1 x6 (pr3_pr2 c t1 x6 H27) (THead (Flat Appl) (lift (S O) O 
x) x0) (THead (Flat Appl) (lift (S O) O x) x4) (Bind b) (pr3_pr2 (CHead c 
(Bind b) x6) (THead (Flat Appl) (lift (S O) O x) x0) (THead (Flat Appl) (lift 
(S O) O x) x4) (pr2_thin_dx (CHead c (Bind b) x6) x0 x4 H28 (lift (S O) O x) 
Appl))))) H32))) x5 H30))) (\lambda (H30: (((eq T x x5) \to (\forall (P: 
Prop).P)))).(H9 (THead (Flat Appl) (lift (S O) O x5) x4) (\lambda (H31: (eq T 
(THead (Flat Appl) (lift (S O) O x) x0) (THead (Flat Appl) (lift (S O) O x5) 
x4))).(\lambda (P: Prop).(let H32 \def (f_equal T T (\lambda (e: T).(match e 
in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow ((let rec lref_map 
(f: ((nat \to nat))) (d: nat) (t0: T) on t0: T \def (match t0 with [(TSort n) 
\Rightarrow (TSort n) | (TLRef i) \Rightarrow (TLRef (match (blt i d) with 
[true \Rightarrow i | false \Rightarrow (f i)])) | (THead k u0 t4) 
\Rightarrow (THead k (lref_map f d u0) (lref_map f (s k d) t4))]) in 
lref_map) (\lambda (x7: nat).(plus x7 (S O))) O x) | (TLRef _) \Rightarrow 
((let rec lref_map (f: ((nat \to nat))) (d: nat) (t0: T) on t0: T \def (match 
t0 with [(TSort n) \Rightarrow (TSort n) | (TLRef i) \Rightarrow (TLRef 
(match (blt i d) with [true \Rightarrow i | false \Rightarrow (f i)])) | 
(THead k u0 t4) \Rightarrow (THead k (lref_map f d u0) (lref_map f (s k d) 
t4))]) in lref_map) (\lambda (x7: nat).(plus x7 (S O))) O x) | (THead _ t0 _) 
\Rightarrow t0])) (THead (Flat Appl) (lift (S O) O x) x0) (THead (Flat Appl) 
(lift (S O) O x5) x4) H31) in ((let H33 \def (f_equal T T (\lambda (e: 
T).(match e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow x0 | 
(TLRef _) \Rightarrow x0 | (THead _ _ t0) \Rightarrow t0])) (THead (Flat 
Appl) (lift (S O) O x) x0) (THead (Flat Appl) (lift (S O) O x5) x4) H31) in 
(\lambda (H34: (eq T (lift (S O) O x) (lift (S O) O x5))).(let H35 \def 
(eq_ind_r T x5 (\lambda (t0: T).((eq T x t0) \to (\forall (P0: Prop).P0))) 
H30 x (lift_inj x x5 (S O) O H34)) in (let H36 \def (eq_ind_r T x5 (\lambda 
(t0: T).(pr2 c x t0)) H17 x (lift_inj x x5 (S O) O H34)) in (let H37 \def 
(eq_ind_r T x4 (\lambda (t0: T).(pr2 (CHead c (Bind b) x6) x0 t0)) H28 x0 
H33) in (H35 (refl_equal T x) P)))))) H32)))) (pr3_pr3_pr3_t c t1 x6 (pr3_pr2 
c t1 x6 H27) (THead (Flat Appl) (lift (S O) O x) x0) (THead (Flat Appl) (lift 
(S O) O x5) x4) (Bind b) (pr3_flat (CHead c (Bind b) x6) (lift (S O) O x) 
(lift (S O) O x5) (pr3_lift (CHead c (Bind b) x6) c (S O) O (drop_drop (Bind 
b) O c c (drop_refl c) x6) x x5 (pr3_pr2 c x x5 H17)) x0 x4 (pr3_pr2 (CHead c 
(Bind b) x6) x0 x4 H28) Appl)))) H29)))) (THead (Bind b) x6 (THead (Flat 
Appl) (lift (S O) O x5) x4)) (pr3_pr2 c (THead (Bind b) t1 (THead (Flat Appl) 
(lift (S O) O x5) x4)) (THead (Bind b) x6 (THead (Flat Appl) (lift (S O) O 
x5) x4)) (pr2_head_1 c t1 x6 H27 (Bind b) (THead (Flat Appl) (lift (S O) O 
x5) x4)))) x1 H25))))))) H22)) H21)) t3 H16)))))))))))))) H13)) 
H12)))))))))))))) y H4))))) H3))))))) u H0))))).
(* COMMENTS
Initial nodes: 9191
END *)

theorem sn3_appl_appl:
 \forall (v1: T).(\forall (t1: T).(let u1 \def (THead (Flat Appl) v1 t1) in 
(\forall (c: C).((sn3 c u1) \to (\forall (v2: T).((sn3 c v2) \to (((\forall 
(u2: T).((pr3 c u1 u2) \to ((((iso u1 u2) \to (\forall (P: Prop).P))) \to 
(sn3 c (THead (Flat Appl) v2 u2)))))) \to (sn3 c (THead (Flat Appl) v2 
u1)))))))))
\def
 \lambda (v1: T).(\lambda (t1: T).(let u1 \def (THead (Flat Appl) v1 t1) in 
(\lambda (c: C).(\lambda (H: (sn3 c (THead (Flat Appl) v1 t1))).(insert_eq T 
(THead (Flat Appl) v1 t1) (\lambda (t: T).(sn3 c t)) (\lambda (t: T).(\forall 
(v2: T).((sn3 c v2) \to (((\forall (u2: T).((pr3 c t u2) \to ((((iso t u2) 
\to (\forall (P: Prop).P))) \to (sn3 c (THead (Flat Appl) v2 u2)))))) \to 
(sn3 c (THead (Flat Appl) v2 t)))))) (\lambda (y: T).(\lambda (H0: (sn3 c 
y)).(unintro T t1 (\lambda (t: T).((eq T y (THead (Flat Appl) v1 t)) \to 
(\forall (v2: T).((sn3 c v2) \to (((\forall (u2: T).((pr3 c y u2) \to ((((iso 
y u2) \to (\forall (P: Prop).P))) \to (sn3 c (THead (Flat Appl) v2 u2)))))) 
\to (sn3 c (THead (Flat Appl) v2 y))))))) (unintro T v1 (\lambda (t: 
T).(\forall (x: T).((eq T y (THead (Flat Appl) t x)) \to (\forall (v2: 
T).((sn3 c v2) \to (((\forall (u2: T).((pr3 c y u2) \to ((((iso y u2) \to 
(\forall (P: Prop).P))) \to (sn3 c (THead (Flat Appl) v2 u2)))))) \to (sn3 c 
(THead (Flat Appl) v2 y)))))))) (sn3_ind c (\lambda (t: T).(\forall (x: 
T).(\forall (x0: T).((eq T t (THead (Flat Appl) x x0)) \to (\forall (v2: 
T).((sn3 c v2) \to (((\forall (u2: T).((pr3 c t u2) \to ((((iso t u2) \to 
(\forall (P: Prop).P))) \to (sn3 c (THead (Flat Appl) v2 u2)))))) \to (sn3 c 
(THead (Flat Appl) v2 t))))))))) (\lambda (t2: T).(\lambda (H1: ((\forall 
(t3: T).((((eq T t2 t3) \to (\forall (P: Prop).P))) \to ((pr3 c t2 t3) \to 
(sn3 c t3)))))).(\lambda (H2: ((\forall (t3: T).((((eq T t2 t3) \to (\forall 
(P: Prop).P))) \to ((pr3 c t2 t3) \to (\forall (x: T).(\forall (x0: T).((eq T 
t3 (THead (Flat Appl) x x0)) \to (\forall (v2: T).((sn3 c v2) \to (((\forall 
(u2: T).((pr3 c t3 u2) \to ((((iso t3 u2) \to (\forall (P: Prop).P))) \to 
(sn3 c (THead (Flat Appl) v2 u2)))))) \to (sn3 c (THead (Flat Appl) v2 
t3))))))))))))).(\lambda (x: T).(\lambda (x0: T).(\lambda (H3: (eq T t2 
(THead (Flat Appl) x x0))).(\lambda (v2: T).(\lambda (H4: (sn3 c 
v2)).(sn3_ind c (\lambda (t: T).(((\forall (u2: T).((pr3 c t2 u2) \to ((((iso 
t2 u2) \to (\forall (P: Prop).P))) \to (sn3 c (THead (Flat Appl) t u2)))))) 
\to (sn3 c (THead (Flat Appl) t t2)))) (\lambda (t0: T).(\lambda (H5: 
((\forall (t3: T).((((eq T t0 t3) \to (\forall (P: Prop).P))) \to ((pr3 c t0 
t3) \to (sn3 c t3)))))).(\lambda (H6: ((\forall (t3: T).((((eq T t0 t3) \to 
(\forall (P: Prop).P))) \to ((pr3 c t0 t3) \to (((\forall (u2: T).((pr3 c t2 
u2) \to ((((iso t2 u2) \to (\forall (P: Prop).P))) \to (sn3 c (THead (Flat 
Appl) t3 u2)))))) \to (sn3 c (THead (Flat Appl) t3 t2)))))))).(\lambda (H7: 
((\forall (u2: T).((pr3 c t2 u2) \to ((((iso t2 u2) \to (\forall (P: 
Prop).P))) \to (sn3 c (THead (Flat Appl) t0 u2))))))).(let H8 \def (eq_ind T 
t2 (\lambda (t: T).(\forall (u2: T).((pr3 c t u2) \to ((((iso t u2) \to 
(\forall (P: Prop).P))) \to (sn3 c (THead (Flat Appl) t0 u2)))))) H7 (THead 
(Flat Appl) x x0) H3) in (let H9 \def (eq_ind T t2 (\lambda (t: T).(\forall 
(t3: T).((((eq T t0 t3) \to (\forall (P: Prop).P))) \to ((pr3 c t0 t3) \to 
(((\forall (u2: T).((pr3 c t u2) \to ((((iso t u2) \to (\forall (P: 
Prop).P))) \to (sn3 c (THead (Flat Appl) t3 u2)))))) \to (sn3 c (THead (Flat 
Appl) t3 t))))))) H6 (THead (Flat Appl) x x0) H3) in (let H10 \def (eq_ind T 
t2 (\lambda (t: T).(\forall (t3: T).((((eq T t t3) \to (\forall (P: 
Prop).P))) \to ((pr3 c t t3) \to (\forall (x1: T).(\forall (x2: T).((eq T t3 
(THead (Flat Appl) x1 x2)) \to (\forall (v3: T).((sn3 c v3) \to (((\forall 
(u2: T).((pr3 c t3 u2) \to ((((iso t3 u2) \to (\forall (P: Prop).P))) \to 
(sn3 c (THead (Flat Appl) v3 u2)))))) \to (sn3 c (THead (Flat Appl) v3 
t3)))))))))))) H2 (THead (Flat Appl) x x0) H3) in (let H11 \def (eq_ind T t2 
(\lambda (t: T).(\forall (t3: T).((((eq T t t3) \to (\forall (P: Prop).P))) 
\to ((pr3 c t t3) \to (sn3 c t3))))) H1 (THead (Flat Appl) x x0) H3) in 
(eq_ind_r T (THead (Flat Appl) x x0) (\lambda (t: T).(sn3 c (THead (Flat 
Appl) t0 t))) (sn3_pr2_intro c (THead (Flat Appl) t0 (THead (Flat Appl) x 
x0)) (\lambda (t3: T).(\lambda (H12: (((eq T (THead (Flat Appl) t0 (THead 
(Flat Appl) x x0)) t3) \to (\forall (P: Prop).P)))).(\lambda (H13: (pr2 c 
(THead (Flat Appl) t0 (THead (Flat Appl) x x0)) t3)).(let H14 \def 
(pr2_gen_appl c t0 (THead (Flat Appl) x x0) t3 H13) in (or3_ind (ex3_2 T T 
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
y2) z1 z2)))))))) (sn3 c t3) (\lambda (H15: (ex3_2 T T (\lambda (u2: 
T).(\lambda (t4: T).(eq T t3 (THead (Flat Appl) u2 t4)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c t0 u2))) (\lambda (_: T).(\lambda (t4: T).(pr2 c 
(THead (Flat Appl) x x0) t4))))).(ex3_2_ind T T (\lambda (u2: T).(\lambda 
(t4: T).(eq T t3 (THead (Flat Appl) u2 t4)))) (\lambda (u2: T).(\lambda (_: 
T).(pr2 c t0 u2))) (\lambda (_: T).(\lambda (t4: T).(pr2 c (THead (Flat Appl) 
x x0) t4))) (sn3 c t3) (\lambda (x1: T).(\lambda (x2: T).(\lambda (H16: (eq T 
t3 (THead (Flat Appl) x1 x2))).(\lambda (H17: (pr2 c t0 x1)).(\lambda (H18: 
(pr2 c (THead (Flat Appl) x x0) x2)).(let H19 \def (eq_ind T t3 (\lambda (t: 
T).((eq T (THead (Flat Appl) t0 (THead (Flat Appl) x x0)) t) \to (\forall (P: 
Prop).P))) H12 (THead (Flat Appl) x1 x2) H16) in (eq_ind_r T (THead (Flat 
Appl) x1 x2) (\lambda (t: T).(sn3 c t)) (let H20 \def (pr2_gen_appl c x x0 x2 
H18) in (or3_ind (ex3_2 T T (\lambda (u2: T).(\lambda (t4: T).(eq T x2 (THead 
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
(THead (Flat Appl) x1 x2)) (\lambda (H21: (ex3_2 T T (\lambda (u2: 
T).(\lambda (t4: T).(eq T x2 (THead (Flat Appl) u2 t4)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c x u2))) (\lambda (_: T).(\lambda (t4: T).(pr2 c x0 
t4))))).(ex3_2_ind T T (\lambda (u2: T).(\lambda (t4: T).(eq T x2 (THead 
(Flat Appl) u2 t4)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c x u2))) 
(\lambda (_: T).(\lambda (t4: T).(pr2 c x0 t4))) (sn3 c (THead (Flat Appl) x1 
x2)) (\lambda (x3: T).(\lambda (x4: T).(\lambda (H22: (eq T x2 (THead (Flat 
Appl) x3 x4))).(\lambda (H23: (pr2 c x x3)).(\lambda (H24: (pr2 c x0 
x4)).(let H25 \def (eq_ind T x2 (\lambda (t: T).((eq T (THead (Flat Appl) t0 
(THead (Flat Appl) x x0)) (THead (Flat Appl) x1 t)) \to (\forall (P: 
Prop).P))) H19 (THead (Flat Appl) x3 x4) H22) in (eq_ind_r T (THead (Flat 
Appl) x3 x4) (\lambda (t: T).(sn3 c (THead (Flat Appl) x1 t))) (let H_x \def 
(term_dec (THead (Flat Appl) x x0) (THead (Flat Appl) x3 x4)) in (let H26 
\def H_x in (or_ind (eq T (THead (Flat Appl) x x0) (THead (Flat Appl) x3 x4)) 
((eq T (THead (Flat Appl) x x0) (THead (Flat Appl) x3 x4)) \to (\forall (P: 
Prop).P)) (sn3 c (THead (Flat Appl) x1 (THead (Flat Appl) x3 x4))) (\lambda 
(H27: (eq T (THead (Flat Appl) x x0) (THead (Flat Appl) x3 x4))).(let H28 
\def (f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) 
with [(TSort _) \Rightarrow x | (TLRef _) \Rightarrow x | (THead _ t _) 
\Rightarrow t])) (THead (Flat Appl) x x0) (THead (Flat Appl) x3 x4) H27) in 
((let H29 \def (f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: 
T).T) with [(TSort _) \Rightarrow x0 | (TLRef _) \Rightarrow x0 | (THead _ _ 
t) \Rightarrow t])) (THead (Flat Appl) x x0) (THead (Flat Appl) x3 x4) H27) 
in (\lambda (H30: (eq T x x3)).(let H31 \def (eq_ind_r T x4 (\lambda (t: 
T).((eq T (THead (Flat Appl) t0 (THead (Flat Appl) x x0)) (THead (Flat Appl) 
x1 (THead (Flat Appl) x3 t))) \to (\forall (P: Prop).P))) H25 x0 H29) in (let 
H32 \def (eq_ind_r T x4 (\lambda (t: T).(pr2 c x0 t)) H24 x0 H29) in (eq_ind 
T x0 (\lambda (t: T).(sn3 c (THead (Flat Appl) x1 (THead (Flat Appl) x3 t)))) 
(let H33 \def (eq_ind_r T x3 (\lambda (t: T).((eq T (THead (Flat Appl) t0 
(THead (Flat Appl) x x0)) (THead (Flat Appl) x1 (THead (Flat Appl) t x0))) 
\to (\forall (P: Prop).P))) H31 x H30) in (let H34 \def (eq_ind_r T x3 
(\lambda (t: T).(pr2 c x t)) H23 x H30) in (eq_ind T x (\lambda (t: T).(sn3 c 
(THead (Flat Appl) x1 (THead (Flat Appl) t x0)))) (let H_x0 \def (term_dec t0 
x1) in (let H35 \def H_x0 in (or_ind (eq T t0 x1) ((eq T t0 x1) \to (\forall 
(P: Prop).P)) (sn3 c (THead (Flat Appl) x1 (THead (Flat Appl) x x0))) 
(\lambda (H36: (eq T t0 x1)).(let H37 \def (eq_ind_r T x1 (\lambda (t: 
T).((eq T (THead (Flat Appl) t0 (THead (Flat Appl) x x0)) (THead (Flat Appl) 
t (THead (Flat Appl) x x0))) \to (\forall (P: Prop).P))) H33 t0 H36) in (let 
H38 \def (eq_ind_r T x1 (\lambda (t: T).(pr2 c t0 t)) H17 t0 H36) in (eq_ind 
T t0 (\lambda (t: T).(sn3 c (THead (Flat Appl) t (THead (Flat Appl) x x0)))) 
(H37 (refl_equal T (THead (Flat Appl) t0 (THead (Flat Appl) x x0))) (sn3 c 
(THead (Flat Appl) t0 (THead (Flat Appl) x x0)))) x1 H36)))) (\lambda (H36: 
(((eq T t0 x1) \to (\forall (P: Prop).P)))).(H9 x1 H36 (pr3_pr2 c t0 x1 H17) 
(\lambda (u2: T).(\lambda (H37: (pr3 c (THead (Flat Appl) x x0) u2)).(\lambda 
(H38: (((iso (THead (Flat Appl) x x0) u2) \to (\forall (P: 
Prop).P)))).(sn3_pr3_trans c (THead (Flat Appl) t0 u2) (H8 u2 H37 H38) (THead 
(Flat Appl) x1 u2) (pr3_pr2 c (THead (Flat Appl) t0 u2) (THead (Flat Appl) x1 
u2) (pr2_head_1 c t0 x1 H17 (Flat Appl) u2)))))))) H35))) x3 H30))) x4 
H29))))) H28))) (\lambda (H27: (((eq T (THead (Flat Appl) x x0) (THead (Flat 
Appl) x3 x4)) \to (\forall (P: Prop).P)))).(H10 (THead (Flat Appl) x3 x4) H27 
(pr3_flat c x x3 (pr3_pr2 c x x3 H23) x0 x4 (pr3_pr2 c x0 x4 H24) Appl) x3 x4 
(refl_equal T (THead (Flat Appl) x3 x4)) x1 (sn3_pr3_trans c t0 (sn3_sing c 
t0 H5) x1 (pr3_pr2 c t0 x1 H17)) (\lambda (u2: T).(\lambda (H28: (pr3 c 
(THead (Flat Appl) x3 x4) u2)).(\lambda (H29: (((iso (THead (Flat Appl) x3 
x4) u2) \to (\forall (P: Prop).P)))).(sn3_pr3_trans c (THead (Flat Appl) t0 
u2) (H8 u2 (pr3_sing c (THead (Flat Appl) x x4) (THead (Flat Appl) x x0) 
(pr2_thin_dx c x0 x4 H24 x Appl) u2 (pr3_sing c (THead (Flat Appl) x3 x4) 
(THead (Flat Appl) x x4) (pr2_head_1 c x x3 H23 (Flat Appl) x4) u2 H28)) 
(\lambda (H30: (iso (THead (Flat Appl) x x0) u2)).(\lambda (P: Prop).(H29 
(iso_trans (THead (Flat Appl) x3 x4) (THead (Flat Appl) x x0) (iso_head x3 x 
x4 x0 (Flat Appl)) u2 H30) P)))) (THead (Flat Appl) x1 u2) (pr3_pr2 c (THead 
(Flat Appl) t0 u2) (THead (Flat Appl) x1 u2) (pr2_head_1 c t0 x1 H17 (Flat 
Appl) u2)))))))) H26))) x2 H22))))))) H21)) (\lambda (H21: (ex4_4 T T T T 
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
(x6: T).(\lambda (H22: (eq T x0 (THead (Bind Abst) x3 x4))).(\lambda (H23: 
(eq T x2 (THead (Bind Abbr) x5 x6))).(\lambda (H24: (pr2 c x x5)).(\lambda 
(H25: ((\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) x4 
x6))))).(let H26 \def (eq_ind T x2 (\lambda (t: T).((eq T (THead (Flat Appl) 
t0 (THead (Flat Appl) x x0)) (THead (Flat Appl) x1 t)) \to (\forall (P: 
Prop).P))) H19 (THead (Bind Abbr) x5 x6) H23) in (eq_ind_r T (THead (Bind 
Abbr) x5 x6) (\lambda (t: T).(sn3 c (THead (Flat Appl) x1 t))) (let H27 \def 
(eq_ind T x0 (\lambda (t: T).((eq T (THead (Flat Appl) t0 (THead (Flat Appl) 
x t)) (THead (Flat Appl) x1 (THead (Bind Abbr) x5 x6))) \to (\forall (P: 
Prop).P))) H26 (THead (Bind Abst) x3 x4) H22) in (let H28 \def (eq_ind T x0 
(\lambda (t: T).(\forall (t4: T).((((eq T (THead (Flat Appl) x t) t4) \to 
(\forall (P: Prop).P))) \to ((pr3 c (THead (Flat Appl) x t) t4) \to (sn3 c 
t4))))) H11 (THead (Bind Abst) x3 x4) H22) in (let H29 \def (eq_ind T x0 
(\lambda (t: T).(\forall (t4: T).((((eq T (THead (Flat Appl) x t) t4) \to 
(\forall (P: Prop).P))) \to ((pr3 c (THead (Flat Appl) x t) t4) \to (\forall 
(x7: T).(\forall (x8: T).((eq T t4 (THead (Flat Appl) x7 x8)) \to (\forall 
(v3: T).((sn3 c v3) \to (((\forall (u2: T).((pr3 c t4 u2) \to ((((iso t4 u2) 
\to (\forall (P: Prop).P))) \to (sn3 c (THead (Flat Appl) v3 u2)))))) \to 
(sn3 c (THead (Flat Appl) v3 t4)))))))))))) H10 (THead (Bind Abst) x3 x4) 
H22) in (let H30 \def (eq_ind T x0 (\lambda (t: T).(\forall (u2: T).((pr3 c 
(THead (Flat Appl) x t) u2) \to ((((iso (THead (Flat Appl) x t) u2) \to 
(\forall (P: Prop).P))) \to (sn3 c (THead (Flat Appl) t0 u2)))))) H8 (THead 
(Bind Abst) x3 x4) H22) in (let H31 \def (eq_ind T x0 (\lambda (t: 
T).(\forall (t4: T).((((eq T t0 t4) \to (\forall (P: Prop).P))) \to ((pr3 c 
t0 t4) \to (((\forall (u2: T).((pr3 c (THead (Flat Appl) x t) u2) \to ((((iso 
(THead (Flat Appl) x t) u2) \to (\forall (P: Prop).P))) \to (sn3 c (THead 
(Flat Appl) t4 u2)))))) \to (sn3 c (THead (Flat Appl) t4 (THead (Flat Appl) x 
t)))))))) H9 (THead (Bind Abst) x3 x4) H22) in (sn3_pr3_trans c (THead (Flat 
Appl) t0 (THead (Bind Abbr) x5 x6)) (H30 (THead (Bind Abbr) x5 x6) (pr3_sing 
c (THead (Bind Abbr) x x4) (THead (Flat Appl) x (THead (Bind Abst) x3 x4)) 
(pr2_free c (THead (Flat Appl) x (THead (Bind Abst) x3 x4)) (THead (Bind 
Abbr) x x4) (pr0_beta x3 x x (pr0_refl x) x4 x4 (pr0_refl x4))) (THead (Bind 
Abbr) x5 x6) (pr3_head_12 c x x5 (pr3_pr2 c x x5 H24) (Bind Abbr) x4 x6 
(pr3_pr2 (CHead c (Bind Abbr) x5) x4 x6 (H25 Abbr x5)))) (\lambda (H32: (iso 
(THead (Flat Appl) x (THead (Bind Abst) x3 x4)) (THead (Bind Abbr) x5 
x6))).(\lambda (P: Prop).(let H33 \def (match H32 in iso return (\lambda (t: 
T).(\lambda (t4: T).(\lambda (_: (iso t t4)).((eq T t (THead (Flat Appl) x 
(THead (Bind Abst) x3 x4))) \to ((eq T t4 (THead (Bind Abbr) x5 x6)) \to 
P))))) with [(iso_sort n1 n2) \Rightarrow (\lambda (H33: (eq T (TSort n1) 
(THead (Flat Appl) x (THead (Bind Abst) x3 x4)))).(\lambda (H34: (eq T (TSort 
n2) (THead (Bind Abbr) x5 x6))).((let H35 \def (eq_ind T (TSort n1) (\lambda 
(e: T).(match e in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow 
True | (TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow False])) I 
(THead (Flat Appl) x (THead (Bind Abst) x3 x4)) H33) in (False_ind ((eq T 
(TSort n2) (THead (Bind Abbr) x5 x6)) \to P) H35)) H34))) | (iso_lref i1 i2) 
\Rightarrow (\lambda (H33: (eq T (TLRef i1) (THead (Flat Appl) x (THead (Bind 
Abst) x3 x4)))).(\lambda (H34: (eq T (TLRef i2) (THead (Bind Abbr) x5 
x6))).((let H35 \def (eq_ind T (TLRef i1) (\lambda (e: T).(match e in T 
return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow True | (THead _ _ _) \Rightarrow False])) I (THead (Flat Appl) x 
(THead (Bind Abst) x3 x4)) H33) in (False_ind ((eq T (TLRef i2) (THead (Bind 
Abbr) x5 x6)) \to P) H35)) H34))) | (iso_head v4 v5 t4 t5 k) \Rightarrow 
(\lambda (H33: (eq T (THead k v4 t4) (THead (Flat Appl) x (THead (Bind Abst) 
x3 x4)))).(\lambda (H34: (eq T (THead k v5 t5) (THead (Bind Abbr) x5 
x6))).((let H35 \def (f_equal T T (\lambda (e: T).(match e in T return 
(\lambda (_: T).T) with [(TSort _) \Rightarrow t4 | (TLRef _) \Rightarrow t4 
| (THead _ _ t) \Rightarrow t])) (THead k v4 t4) (THead (Flat Appl) x (THead 
(Bind Abst) x3 x4)) H33) in ((let H36 \def (f_equal T T (\lambda (e: 
T).(match e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow v4 | 
(TLRef _) \Rightarrow v4 | (THead _ t _) \Rightarrow t])) (THead k v4 t4) 
(THead (Flat Appl) x (THead (Bind Abst) x3 x4)) H33) in ((let H37 \def 
(f_equal T K (\lambda (e: T).(match e in T return (\lambda (_: T).K) with 
[(TSort _) \Rightarrow k | (TLRef _) \Rightarrow k | (THead k0 _ _) 
\Rightarrow k0])) (THead k v4 t4) (THead (Flat Appl) x (THead (Bind Abst) x3 
x4)) H33) in (eq_ind K (Flat Appl) (\lambda (k0: K).((eq T v4 x) \to ((eq T 
t4 (THead (Bind Abst) x3 x4)) \to ((eq T (THead k0 v5 t5) (THead (Bind Abbr) 
x5 x6)) \to P)))) (\lambda (H38: (eq T v4 x)).(eq_ind T x (\lambda (_: 
T).((eq T t4 (THead (Bind Abst) x3 x4)) \to ((eq T (THead (Flat Appl) v5 t5) 
(THead (Bind Abbr) x5 x6)) \to P))) (\lambda (H39: (eq T t4 (THead (Bind 
Abst) x3 x4))).(eq_ind T (THead (Bind Abst) x3 x4) (\lambda (_: T).((eq T 
(THead (Flat Appl) v5 t5) (THead (Bind Abbr) x5 x6)) \to P)) (\lambda (H40: 
(eq T (THead (Flat Appl) v5 t5) (THead (Bind Abbr) x5 x6))).(let H41 \def 
(eq_ind T (THead (Flat Appl) v5 t5) (\lambda (e: T).(match e in T return 
(\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow False | (THead k0 _ _) \Rightarrow (match k0 in K return (\lambda 
(_: K).Prop) with [(Bind _) \Rightarrow False | (Flat _) \Rightarrow 
True])])) I (THead (Bind Abbr) x5 x6) H40) in (False_ind P H41))) t4 (sym_eq 
T t4 (THead (Bind Abst) x3 x4) H39))) v4 (sym_eq T v4 x H38))) k (sym_eq K k 
(Flat Appl) H37))) H36)) H35)) H34)))]) in (H33 (refl_equal T (THead (Flat 
Appl) x (THead (Bind Abst) x3 x4))) (refl_equal T (THead (Bind Abbr) x5 
x6))))))) (THead (Flat Appl) x1 (THead (Bind Abbr) x5 x6)) (pr3_pr2 c (THead 
(Flat Appl) t0 (THead (Bind Abbr) x5 x6)) (THead (Flat Appl) x1 (THead (Bind 
Abbr) x5 x6)) (pr2_head_1 c t0 x1 H17 (Flat Appl) (THead (Bind Abbr) x5 
x6))))))))) x2 H23)))))))))) H21)) (\lambda (H21: (ex6_6 B T T T T T (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
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
(x5: T).(\lambda (x6: T).(\lambda (x7: T).(\lambda (x8: T).(\lambda (H22: 
(not (eq B x3 Abst))).(\lambda (H23: (eq T x0 (THead (Bind x3) x4 
x5))).(\lambda (H24: (eq T x2 (THead (Bind x3) x8 (THead (Flat Appl) (lift (S 
O) O x7) x6)))).(\lambda (H25: (pr2 c x x7)).(\lambda (H26: (pr2 c x4 
x8)).(\lambda (H27: (pr2 (CHead c (Bind x3) x8) x5 x6)).(let H28 \def (eq_ind 
T x2 (\lambda (t: T).((eq T (THead (Flat Appl) t0 (THead (Flat Appl) x x0)) 
(THead (Flat Appl) x1 t)) \to (\forall (P: Prop).P))) H19 (THead (Bind x3) x8 
(THead (Flat Appl) (lift (S O) O x7) x6)) H24) in (eq_ind_r T (THead (Bind 
x3) x8 (THead (Flat Appl) (lift (S O) O x7) x6)) (\lambda (t: T).(sn3 c 
(THead (Flat Appl) x1 t))) (let H29 \def (eq_ind T x0 (\lambda (t: T).((eq T 
(THead (Flat Appl) t0 (THead (Flat Appl) x t)) (THead (Flat Appl) x1 (THead 
(Bind x3) x8 (THead (Flat Appl) (lift (S O) O x7) x6)))) \to (\forall (P: 
Prop).P))) H28 (THead (Bind x3) x4 x5) H23) in (let H30 \def (eq_ind T x0 
(\lambda (t: T).(\forall (t4: T).((((eq T (THead (Flat Appl) x t) t4) \to 
(\forall (P: Prop).P))) \to ((pr3 c (THead (Flat Appl) x t) t4) \to (sn3 c 
t4))))) H11 (THead (Bind x3) x4 x5) H23) in (let H31 \def (eq_ind T x0 
(\lambda (t: T).(\forall (t4: T).((((eq T (THead (Flat Appl) x t) t4) \to 
(\forall (P: Prop).P))) \to ((pr3 c (THead (Flat Appl) x t) t4) \to (\forall 
(x9: T).(\forall (x10: T).((eq T t4 (THead (Flat Appl) x9 x10)) \to (\forall 
(v3: T).((sn3 c v3) \to (((\forall (u2: T).((pr3 c t4 u2) \to ((((iso t4 u2) 
\to (\forall (P: Prop).P))) \to (sn3 c (THead (Flat Appl) v3 u2)))))) \to 
(sn3 c (THead (Flat Appl) v3 t4)))))))))))) H10 (THead (Bind x3) x4 x5) H23) 
in (let H32 \def (eq_ind T x0 (\lambda (t: T).(\forall (u2: T).((pr3 c (THead 
(Flat Appl) x t) u2) \to ((((iso (THead (Flat Appl) x t) u2) \to (\forall (P: 
Prop).P))) \to (sn3 c (THead (Flat Appl) t0 u2)))))) H8 (THead (Bind x3) x4 
x5) H23) in (let H33 \def (eq_ind T x0 (\lambda (t: T).(\forall (t4: 
T).((((eq T t0 t4) \to (\forall (P: Prop).P))) \to ((pr3 c t0 t4) \to 
(((\forall (u2: T).((pr3 c (THead (Flat Appl) x t) u2) \to ((((iso (THead 
(Flat Appl) x t) u2) \to (\forall (P: Prop).P))) \to (sn3 c (THead (Flat 
Appl) t4 u2)))))) \to (sn3 c (THead (Flat Appl) t4 (THead (Flat Appl) x 
t)))))))) H9 (THead (Bind x3) x4 x5) H23) in (sn3_pr3_trans c (THead (Flat 
Appl) t0 (THead (Bind x3) x8 (THead (Flat Appl) (lift (S O) O x7) x6))) (H32 
(THead (Bind x3) x8 (THead (Flat Appl) (lift (S O) O x7) x6)) (pr3_sing c 
(THead (Bind x3) x4 (THead (Flat Appl) (lift (S O) O x) x5)) (THead (Flat 
Appl) x (THead (Bind x3) x4 x5)) (pr2_free c (THead (Flat Appl) x (THead 
(Bind x3) x4 x5)) (THead (Bind x3) x4 (THead (Flat Appl) (lift (S O) O x) 
x5)) (pr0_upsilon x3 H22 x x (pr0_refl x) x4 x4 (pr0_refl x4) x5 x5 (pr0_refl 
x5))) (THead (Bind x3) x8 (THead (Flat Appl) (lift (S O) O x7) x6)) 
(pr3_head_12 c x4 x8 (pr3_pr2 c x4 x8 H26) (Bind x3) (THead (Flat Appl) (lift 
(S O) O x) x5) (THead (Flat Appl) (lift (S O) O x7) x6) (pr3_head_12 (CHead c 
(Bind x3) x8) (lift (S O) O x) (lift (S O) O x7) (pr3_lift (CHead c (Bind x3) 
x8) c (S O) O (drop_drop (Bind x3) O c c (drop_refl c) x8) x x7 (pr3_pr2 c x 
x7 H25)) (Flat Appl) x5 x6 (pr3_pr2 (CHead (CHead c (Bind x3) x8) (Flat Appl) 
(lift (S O) O x7)) x5 x6 (pr2_cflat (CHead c (Bind x3) x8) x5 x6 H27 Appl 
(lift (S O) O x7)))))) (\lambda (H34: (iso (THead (Flat Appl) x (THead (Bind 
x3) x4 x5)) (THead (Bind x3) x8 (THead (Flat Appl) (lift (S O) O x7) 
x6)))).(\lambda (P: Prop).(let H35 \def (match H34 in iso return (\lambda (t: 
T).(\lambda (t4: T).(\lambda (_: (iso t t4)).((eq T t (THead (Flat Appl) x 
(THead (Bind x3) x4 x5))) \to ((eq T t4 (THead (Bind x3) x8 (THead (Flat 
Appl) (lift (S O) O x7) x6))) \to P))))) with [(iso_sort n1 n2) \Rightarrow 
(\lambda (H35: (eq T (TSort n1) (THead (Flat Appl) x (THead (Bind x3) x4 
x5)))).(\lambda (H36: (eq T (TSort n2) (THead (Bind x3) x8 (THead (Flat Appl) 
(lift (S O) O x7) x6)))).((let H37 \def (eq_ind T (TSort n1) (\lambda (e: 
T).(match e in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow 
True | (TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow False])) I 
(THead (Flat Appl) x (THead (Bind x3) x4 x5)) H35) in (False_ind ((eq T 
(TSort n2) (THead (Bind x3) x8 (THead (Flat Appl) (lift (S O) O x7) x6))) \to 
P) H37)) H36))) | (iso_lref i1 i2) \Rightarrow (\lambda (H35: (eq T (TLRef 
i1) (THead (Flat Appl) x (THead (Bind x3) x4 x5)))).(\lambda (H36: (eq T 
(TLRef i2) (THead (Bind x3) x8 (THead (Flat Appl) (lift (S O) O x7) 
x6)))).((let H37 \def (eq_ind T (TLRef i1) (\lambda (e: T).(match e in T 
return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow True | (THead _ _ _) \Rightarrow False])) I (THead (Flat Appl) x 
(THead (Bind x3) x4 x5)) H35) in (False_ind ((eq T (TLRef i2) (THead (Bind 
x3) x8 (THead (Flat Appl) (lift (S O) O x7) x6))) \to P) H37)) H36))) | 
(iso_head v4 v5 t4 t5 k) \Rightarrow (\lambda (H35: (eq T (THead k v4 t4) 
(THead (Flat Appl) x (THead (Bind x3) x4 x5)))).(\lambda (H36: (eq T (THead k 
v5 t5) (THead (Bind x3) x8 (THead (Flat Appl) (lift (S O) O x7) x6)))).((let 
H37 \def (f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) 
with [(TSort _) \Rightarrow t4 | (TLRef _) \Rightarrow t4 | (THead _ _ t) 
\Rightarrow t])) (THead k v4 t4) (THead (Flat Appl) x (THead (Bind x3) x4 
x5)) H35) in ((let H38 \def (f_equal T T (\lambda (e: T).(match e in T return 
(\lambda (_: T).T) with [(TSort _) \Rightarrow v4 | (TLRef _) \Rightarrow v4 
| (THead _ t _) \Rightarrow t])) (THead k v4 t4) (THead (Flat Appl) x (THead 
(Bind x3) x4 x5)) H35) in ((let H39 \def (f_equal T K (\lambda (e: T).(match 
e in T return (\lambda (_: T).K) with [(TSort _) \Rightarrow k | (TLRef _) 
\Rightarrow k | (THead k0 _ _) \Rightarrow k0])) (THead k v4 t4) (THead (Flat 
Appl) x (THead (Bind x3) x4 x5)) H35) in (eq_ind K (Flat Appl) (\lambda (k0: 
K).((eq T v4 x) \to ((eq T t4 (THead (Bind x3) x4 x5)) \to ((eq T (THead k0 
v5 t5) (THead (Bind x3) x8 (THead (Flat Appl) (lift (S O) O x7) x6))) \to 
P)))) (\lambda (H40: (eq T v4 x)).(eq_ind T x (\lambda (_: T).((eq T t4 
(THead (Bind x3) x4 x5)) \to ((eq T (THead (Flat Appl) v5 t5) (THead (Bind 
x3) x8 (THead (Flat Appl) (lift (S O) O x7) x6))) \to P))) (\lambda (H41: (eq 
T t4 (THead (Bind x3) x4 x5))).(eq_ind T (THead (Bind x3) x4 x5) (\lambda (_: 
T).((eq T (THead (Flat Appl) v5 t5) (THead (Bind x3) x8 (THead (Flat Appl) 
(lift (S O) O x7) x6))) \to P)) (\lambda (H42: (eq T (THead (Flat Appl) v5 
t5) (THead (Bind x3) x8 (THead (Flat Appl) (lift (S O) O x7) x6)))).(let H43 
\def (eq_ind T (THead (Flat Appl) v5 t5) (\lambda (e: T).(match e in T return 
(\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow False | (THead k0 _ _) \Rightarrow (match k0 in K return (\lambda 
(_: K).Prop) with [(Bind _) \Rightarrow False | (Flat _) \Rightarrow 
True])])) I (THead (Bind x3) x8 (THead (Flat Appl) (lift (S O) O x7) x6)) 
H42) in (False_ind P H43))) t4 (sym_eq T t4 (THead (Bind x3) x4 x5) H41))) v4 
(sym_eq T v4 x H40))) k (sym_eq K k (Flat Appl) H39))) H38)) H37)) H36)))]) 
in (H35 (refl_equal T (THead (Flat Appl) x (THead (Bind x3) x4 x5))) 
(refl_equal T (THead (Bind x3) x8 (THead (Flat Appl) (lift (S O) O x7) 
x6)))))))) (THead (Flat Appl) x1 (THead (Bind x3) x8 (THead (Flat Appl) (lift 
(S O) O x7) x6))) (pr3_pr2 c (THead (Flat Appl) t0 (THead (Bind x3) x8 (THead 
(Flat Appl) (lift (S O) O x7) x6))) (THead (Flat Appl) x1 (THead (Bind x3) x8 
(THead (Flat Appl) (lift (S O) O x7) x6))) (pr2_head_1 c t0 x1 H17 (Flat 
Appl) (THead (Bind x3) x8 (THead (Flat Appl) (lift (S O) O x7) x6)))))))))) 
x2 H24)))))))))))))) H21)) H20)) t3 H16))))))) H15)) (\lambda (H15: (ex4_4 T 
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
T).(\lambda (x2: T).(\lambda (x3: T).(\lambda (x4: T).(\lambda (H16: (eq T 
(THead (Flat Appl) x x0) (THead (Bind Abst) x1 x2))).(\lambda (H17: (eq T t3 
(THead (Bind Abbr) x3 x4))).(\lambda (_: (pr2 c t0 x3)).(\lambda (_: 
((\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) x2 x4))))).(let 
H20 \def (eq_ind T t3 (\lambda (t: T).((eq T (THead (Flat Appl) t0 (THead 
(Flat Appl) x x0)) t) \to (\forall (P: Prop).P))) H12 (THead (Bind Abbr) x3 
x4) H17) in (eq_ind_r T (THead (Bind Abbr) x3 x4) (\lambda (t: T).(sn3 c t)) 
(let H21 \def (eq_ind T (THead (Flat Appl) x x0) (\lambda (ee: T).(match ee 
in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef 
_) \Rightarrow False | (THead k _ _) \Rightarrow (match k in K return 
(\lambda (_: K).Prop) with [(Bind _) \Rightarrow False | (Flat _) \Rightarrow 
True])])) I (THead (Bind Abst) x1 x2) H16) in (False_ind (sn3 c (THead (Bind 
Abbr) x3 x4)) H21)) t3 H17)))))))))) H15)) (\lambda (H15: (ex6_6 B T T T T T 
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
(x5: T).(\lambda (x6: T).(\lambda (_: (not (eq B x1 Abst))).(\lambda (H17: 
(eq T (THead (Flat Appl) x x0) (THead (Bind x1) x2 x3))).(\lambda (H18: (eq T 
t3 (THead (Bind x1) x6 (THead (Flat Appl) (lift (S O) O x5) x4)))).(\lambda 
(_: (pr2 c t0 x5)).(\lambda (_: (pr2 c x2 x6)).(\lambda (_: (pr2 (CHead c 
(Bind x1) x6) x3 x4)).(let H22 \def (eq_ind T t3 (\lambda (t: T).((eq T 
(THead (Flat Appl) t0 (THead (Flat Appl) x x0)) t) \to (\forall (P: 
Prop).P))) H12 (THead (Bind x1) x6 (THead (Flat Appl) (lift (S O) O x5) x4)) 
H18) in (eq_ind_r T (THead (Bind x1) x6 (THead (Flat Appl) (lift (S O) O x5) 
x4)) (\lambda (t: T).(sn3 c t)) (let H23 \def (eq_ind T (THead (Flat Appl) x 
x0) (\lambda (ee: T).(match ee in T return (\lambda (_: T).Prop) with [(TSort 
_) \Rightarrow False | (TLRef _) \Rightarrow False | (THead k _ _) 
\Rightarrow (match k in K return (\lambda (_: K).Prop) with [(Bind _) 
\Rightarrow False | (Flat _) \Rightarrow True])])) I (THead (Bind x1) x2 x3) 
H17) in (False_ind (sn3 c (THead (Bind x1) x6 (THead (Flat Appl) (lift (S O) 
O x5) x4))) H23)) t3 H18)))))))))))))) H15)) H14)))))) t2 H3))))))))) v2 
H4))))))))) y H0))))) H))))).
(* COMMENTS
Initial nodes: 9317
END *)

theorem sn3_appl_beta:
 \forall (c: C).(\forall (u: T).(\forall (v: T).(\forall (t: T).((sn3 c 
(THead (Flat Appl) u (THead (Bind Abbr) v t))) \to (\forall (w: T).((sn3 c w) 
\to (sn3 c (THead (Flat Appl) u (THead (Flat Appl) v (THead (Bind Abst) w 
t))))))))))
\def
 \lambda (c: C).(\lambda (u: T).(\lambda (v: T).(\lambda (t: T).(\lambda (H: 
(sn3 c (THead (Flat Appl) u (THead (Bind Abbr) v t)))).(\lambda (w: 
T).(\lambda (H0: (sn3 c w)).(let H_x \def (sn3_gen_flat Appl c u (THead (Bind 
Abbr) v t) H) in (let H1 \def H_x in (land_ind (sn3 c u) (sn3 c (THead (Bind 
Abbr) v t)) (sn3 c (THead (Flat Appl) u (THead (Flat Appl) v (THead (Bind 
Abst) w t)))) (\lambda (H2: (sn3 c u)).(\lambda (H3: (sn3 c (THead (Bind 
Abbr) v t))).(sn3_appl_appl v (THead (Bind Abst) w t) c (sn3_beta c v t H3 w 
H0) u H2 (\lambda (u2: T).(\lambda (H4: (pr3 c (THead (Flat Appl) v (THead 
(Bind Abst) w t)) u2)).(\lambda (H5: (((iso (THead (Flat Appl) v (THead (Bind 
Abst) w t)) u2) \to (\forall (P: Prop).P)))).(sn3_pr3_trans c (THead (Flat 
Appl) u (THead (Bind Abbr) v t)) H (THead (Flat Appl) u u2) (pr3_thin_dx c 
(THead (Bind Abbr) v t) u2 (pr3_iso_beta v w t c u2 H4 H5) u Appl)))))))) 
H1))))))))).
(* COMMENTS
Initial nodes: 289
END *)

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
(* COMMENTS
Initial nodes: 141
END *)

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
in (land_ind (sn3 c t) True (sn3 c (THead (Flat Appl) t (THeads (Flat Appl) 
TNil (TLRef i)))) (\lambda (H3: (sn3 c t)).(\lambda (_: True).(sn3_appl_lref 
c i H t H3))) H2)))) (\lambda (t1: T).(\lambda (t2: TList).(\lambda (_: 
(((((sns3 c t2) \to (sn3 c (THeads (Flat Appl) t2 (TLRef i))))) \to ((land 
(sn3 c t) (sns3 c t2)) \to (sn3 c (THead (Flat Appl) t (THeads (Flat Appl) t2 
(TLRef i)))))))).(\lambda (H1: (((sns3 c (TCons t1 t2)) \to (sn3 c (THeads 
(Flat Appl) (TCons t1 t2) (TLRef i)))))).(\lambda (H2: (land (sn3 c t) (sns3 
c (TCons t1 t2)))).(let H3 \def H2 in (land_ind (sn3 c t) (land (sn3 c t1) 
(sns3 c t2)) (sn3 c (THead (Flat Appl) t (THeads (Flat Appl) (TCons t1 t2) 
(TLRef i)))) (\lambda (H4: (sn3 c t)).(\lambda (H5: (land (sn3 c t1) (sns3 c 
t2))).(land_ind (sn3 c t1) (sns3 c t2) (sn3 c (THead (Flat Appl) t (THeads 
(Flat Appl) (TCons t1 t2) (TLRef i)))) (\lambda (H6: (sn3 c t1)).(\lambda 
(H7: (sns3 c t2)).(sn3_appl_appls t1 (TLRef i) t2 c (H1 (conj (sn3 c t1) 
(sns3 c t2) H6 H7)) t H4 (\lambda (u2: T).(\lambda (H8: (pr3 c (THeads (Flat 
Appl) (TCons t1 t2) (TLRef i)) u2)).(\lambda (H9: (((iso (THeads (Flat Appl) 
(TCons t1 t2) (TLRef i)) u2) \to (\forall (P: Prop).P)))).(H9 
(nf2_iso_appls_lref c i H (TCons t1 t2) u2 H8) (sn3 c (THead (Flat Appl) t 
u2))))))))) H5))) H3))))))) t0))) us)))).
(* COMMENTS
Initial nodes: 577
END *)

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
\def H_x in (land_ind (sn3 c t) (sn3 c (THead (Flat Appl) t1 (THeads (Flat 
Appl) t2 t3))) (sn3 c (THead (Flat Appl) t (THeads (Flat Appl) (TCons t1 t2) 
(THead (Flat Cast) u t3)))) (\lambda (_: (sn3 c t)).(\lambda (H5: (sn3 c 
(THead (Flat Appl) t1 (THeads (Flat Appl) t2 t3)))).(let H6 \def H5 in (let 
H_x0 \def (sn3_gen_flat Appl c t (THeads (Flat Appl) (TCons t1 t2) u) H1) in 
(let H7 \def H_x0 in (land_ind (sn3 c t) (sn3 c (THead (Flat Appl) t1 (THeads 
(Flat Appl) t2 u))) (sn3 c (THead (Flat Appl) t (THeads (Flat Appl) (TCons t1 
t2) (THead (Flat Cast) u t3)))) (\lambda (H8: (sn3 c t)).(\lambda (H9: (sn3 c 
(THead (Flat Appl) t1 (THeads (Flat Appl) t2 u)))).(let H10 \def H9 in 
(sn3_appl_appls t1 (THead (Flat Cast) u t3) t2 c (H0 u H10 t3 H6) t H8 
(\lambda (u2: T).(\lambda (H11: (pr3 c (THeads (Flat Appl) (TCons t1 t2) 
(THead (Flat Cast) u t3)) u2)).(\lambda (H12: (((iso (THeads (Flat Appl) 
(TCons t1 t2) (THead (Flat Cast) u t3)) u2) \to (\forall (P: 
Prop).P)))).(sn3_pr3_trans c (THead (Flat Appl) t (THeads (Flat Appl) (TCons 
t1 t2) t3)) H2 (THead (Flat Appl) t u2) (pr3_thin_dx c (THeads (Flat Appl) 
(TCons t1 t2) t3) u2 (pr3_iso_appls_cast c u t3 (TCons t1 t2) u2 H11 H12) t 
Appl))))))))) H7)))))) H3))))))))))) t0))) vs)).
(* COMMENTS
Initial nodes: 1025
END *)

theorem sn3_appls_bind:
 \forall (b: B).((not (eq B b Abst)) \to (\forall (c: C).(\forall (u: 
T).((sn3 c u) \to (\forall (vs: TList).(\forall (t: T).((sn3 (CHead c (Bind 
b) u) (THeads (Flat Appl) (lifts (S O) O vs) t)) \to (sn3 c (THeads (Flat 
Appl) vs (THead (Bind b) u t))))))))))
\def
 \lambda (b: B).(\lambda (H: (not (eq B b Abst))).(\lambda (c: C).(\lambda 
(u: T).(\lambda (H0: (sn3 c u)).(\lambda (vs: TList).(TList_ind (\lambda (t: 
TList).(\forall (t0: T).((sn3 (CHead c (Bind b) u) (THeads (Flat Appl) (lifts 
(S O) O t) t0)) \to (sn3 c (THeads (Flat Appl) t (THead (Bind b) u t0)))))) 
(\lambda (t: T).(\lambda (H1: (sn3 (CHead c (Bind b) u) t)).(sn3_bind b c u 
H0 t H1))) (\lambda (v: T).(\lambda (vs0: TList).(TList_ind (\lambda (t: 
TList).(((\forall (t0: T).((sn3 (CHead c (Bind b) u) (THeads (Flat Appl) 
(lifts (S O) O t) t0)) \to (sn3 c (THeads (Flat Appl) t (THead (Bind b) u 
t0)))))) \to (\forall (t0: T).((sn3 (CHead c (Bind b) u) (THead (Flat Appl) 
(lift (S O) O v) (THeads (Flat Appl) (lifts (S O) O t) t0))) \to (sn3 c 
(THead (Flat Appl) v (THeads (Flat Appl) t (THead (Bind b) u t0)))))))) 
(\lambda (_: ((\forall (t: T).((sn3 (CHead c (Bind b) u) (THeads (Flat Appl) 
(lifts (S O) O TNil) t)) \to (sn3 c (THeads (Flat Appl) TNil (THead (Bind b) 
u t))))))).(\lambda (t: T).(\lambda (H2: (sn3 (CHead c (Bind b) u) (THead 
(Flat Appl) (lift (S O) O v) (THeads (Flat Appl) (lifts (S O) O TNil) 
t)))).(sn3_appl_bind b H c u H0 t v H2)))) (\lambda (t: T).(\lambda (t0: 
TList).(\lambda (_: ((((\forall (t1: T).((sn3 (CHead c (Bind b) u) (THeads 
(Flat Appl) (lifts (S O) O t0) t1)) \to (sn3 c (THeads (Flat Appl) t0 (THead 
(Bind b) u t1)))))) \to (\forall (t1: T).((sn3 (CHead c (Bind b) u) (THead 
(Flat Appl) (lift (S O) O v) (THeads (Flat Appl) (lifts (S O) O t0) t1))) \to 
(sn3 c (THead (Flat Appl) v (THeads (Flat Appl) t0 (THead (Bind b) u 
t1))))))))).(\lambda (H2: ((\forall (t1: T).((sn3 (CHead c (Bind b) u) 
(THeads (Flat Appl) (lifts (S O) O (TCons t t0)) t1)) \to (sn3 c (THeads 
(Flat Appl) (TCons t t0) (THead (Bind b) u t1))))))).(\lambda (t1: 
T).(\lambda (H3: (sn3 (CHead c (Bind b) u) (THead (Flat Appl) (lift (S O) O 
v) (THeads (Flat Appl) (lifts (S O) O (TCons t t0)) t1)))).(let H_x \def 
(sn3_gen_flat Appl (CHead c (Bind b) u) (lift (S O) O v) (THeads (Flat Appl) 
(lifts (S O) O (TCons t t0)) t1) H3) in (let H4 \def H_x in (land_ind (sn3 
(CHead c (Bind b) u) (lift (S O) O v)) (sn3 (CHead c (Bind b) u) (THead (Flat 
Appl) (lift (S O) O t) (THeads (Flat Appl) (lifts (S O) O t0) t1))) (sn3 c 
(THead (Flat Appl) v (THeads (Flat Appl) (TCons t t0) (THead (Bind b) u 
t1)))) (\lambda (H5: (sn3 (CHead c (Bind b) u) (lift (S O) O v))).(\lambda 
(H6: (sn3 (CHead c (Bind b) u) (THead (Flat Appl) (lift (S O) O t) (THeads 
(Flat Appl) (lifts (S O) O t0) t1)))).(let H_y \def (sn3_gen_lift (CHead c 
(Bind b) u) v (S O) O H5 c) in (sn3_appl_appls t (THead (Bind b) u t1) t0 c 
(H2 t1 H6) v (H_y (drop_drop (Bind b) O c c (drop_refl c) u)) (\lambda (u2: 
T).(\lambda (H7: (pr3 c (THeads (Flat Appl) (TCons t t0) (THead (Bind b) u 
t1)) u2)).(\lambda (H8: (((iso (THeads (Flat Appl) (TCons t t0) (THead (Bind 
b) u t1)) u2) \to (\forall (P: Prop).P)))).(let H9 \def (pr3_iso_appls_bind b 
H (TCons t t0) u t1 c u2 H7 H8) in (sn3_pr3_trans c (THead (Flat Appl) v 
(THead (Bind b) u (THeads (Flat Appl) (lifts (S O) O (TCons t t0)) t1))) 
(sn3_appl_bind b H c u H0 (THeads (Flat Appl) (lifts (S O) O (TCons t t0)) 
t1) v H3) (THead (Flat Appl) v u2) (pr3_flat c v v (pr3_refl c v) (THead 
(Bind b) u (THeads (Flat Appl) (lifts (S O) O (TCons t t0)) t1)) u2 H9 
Appl)))))))))) H4))))))))) vs0))) vs)))))).
(* COMMENTS
Initial nodes: 1143
END *)

theorem sn3_appls_beta:
 \forall (c: C).(\forall (v: T).(\forall (t: T).(\forall (us: TList).((sn3 c 
(THeads (Flat Appl) us (THead (Bind Abbr) v t))) \to (\forall (w: T).((sn3 c 
w) \to (sn3 c (THeads (Flat Appl) us (THead (Flat Appl) v (THead (Bind Abst) 
w t))))))))))
\def
 \lambda (c: C).(\lambda (v: T).(\lambda (t: T).(\lambda (us: 
TList).(TList_ind (\lambda (t0: TList).((sn3 c (THeads (Flat Appl) t0 (THead 
(Bind Abbr) v t))) \to (\forall (w: T).((sn3 c w) \to (sn3 c (THeads (Flat 
Appl) t0 (THead (Flat Appl) v (THead (Bind Abst) w t)))))))) (\lambda (H: 
(sn3 c (THead (Bind Abbr) v t))).(\lambda (w: T).(\lambda (H0: (sn3 c 
w)).(sn3_beta c v t H w H0)))) (\lambda (u: T).(\lambda (us0: 
TList).(TList_ind (\lambda (t0: TList).((((sn3 c (THeads (Flat Appl) t0 
(THead (Bind Abbr) v t))) \to (\forall (w: T).((sn3 c w) \to (sn3 c (THeads 
(Flat Appl) t0 (THead (Flat Appl) v (THead (Bind Abst) w t)))))))) \to ((sn3 
c (THead (Flat Appl) u (THeads (Flat Appl) t0 (THead (Bind Abbr) v t)))) \to 
(\forall (w: T).((sn3 c w) \to (sn3 c (THead (Flat Appl) u (THeads (Flat 
Appl) t0 (THead (Flat Appl) v (THead (Bind Abst) w t)))))))))) (\lambda (_: 
(((sn3 c (THeads (Flat Appl) TNil (THead (Bind Abbr) v t))) \to (\forall (w: 
T).((sn3 c w) \to (sn3 c (THeads (Flat Appl) TNil (THead (Flat Appl) v (THead 
(Bind Abst) w t))))))))).(\lambda (H0: (sn3 c (THead (Flat Appl) u (THeads 
(Flat Appl) TNil (THead (Bind Abbr) v t))))).(\lambda (w: T).(\lambda (H1: 
(sn3 c w)).(sn3_appl_beta c u v t H0 w H1))))) (\lambda (t0: T).(\lambda (t1: 
TList).(\lambda (_: (((((sn3 c (THeads (Flat Appl) t1 (THead (Bind Abbr) v 
t))) \to (\forall (w: T).((sn3 c w) \to (sn3 c (THeads (Flat Appl) t1 (THead 
(Flat Appl) v (THead (Bind Abst) w t)))))))) \to ((sn3 c (THead (Flat Appl) u 
(THeads (Flat Appl) t1 (THead (Bind Abbr) v t)))) \to (\forall (w: T).((sn3 c 
w) \to (sn3 c (THead (Flat Appl) u (THeads (Flat Appl) t1 (THead (Flat Appl) 
v (THead (Bind Abst) w t))))))))))).(\lambda (H0: (((sn3 c (THeads (Flat 
Appl) (TCons t0 t1) (THead (Bind Abbr) v t))) \to (\forall (w: T).((sn3 c w) 
\to (sn3 c (THeads (Flat Appl) (TCons t0 t1) (THead (Flat Appl) v (THead 
(Bind Abst) w t))))))))).(\lambda (H1: (sn3 c (THead (Flat Appl) u (THeads 
(Flat Appl) (TCons t0 t1) (THead (Bind Abbr) v t))))).(\lambda (w: 
T).(\lambda (H2: (sn3 c w)).(let H_x \def (sn3_gen_flat Appl c u (THeads 
(Flat Appl) (TCons t0 t1) (THead (Bind Abbr) v t)) H1) in (let H3 \def H_x in 
(land_ind (sn3 c u) (sn3 c (THead (Flat Appl) t0 (THeads (Flat Appl) t1 
(THead (Bind Abbr) v t)))) (sn3 c (THead (Flat Appl) u (THeads (Flat Appl) 
(TCons t0 t1) (THead (Flat Appl) v (THead (Bind Abst) w t))))) (\lambda (H4: 
(sn3 c u)).(\lambda (H5: (sn3 c (THead (Flat Appl) t0 (THeads (Flat Appl) t1 
(THead (Bind Abbr) v t))))).(sn3_appl_appls t0 (THead (Flat Appl) v (THead 
(Bind Abst) w t)) t1 c (H0 H5 w H2) u H4 (\lambda (u2: T).(\lambda (H6: (pr3 
c (THeads (Flat Appl) (TCons t0 t1) (THead (Flat Appl) v (THead (Bind Abst) w 
t))) u2)).(\lambda (H7: (((iso (THeads (Flat Appl) (TCons t0 t1) (THead (Flat 
Appl) v (THead (Bind Abst) w t))) u2) \to (\forall (P: Prop).P)))).(let H8 
\def (pr3_iso_appls_beta (TCons t0 t1) v w t c u2 H6 H7) in (sn3_pr3_trans c 
(THead (Flat Appl) u (THeads (Flat Appl) (TCons t0 t1) (THead (Bind Abbr) v 
t))) H1 (THead (Flat Appl) u u2) (pr3_thin_dx c (THeads (Flat Appl) (TCons t0 
t1) (THead (Bind Abbr) v t)) u2 H8 u Appl))))))))) H3)))))))))) us0))) us)))).
(* COMMENTS
Initial nodes: 987
END *)

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
(* COMMENTS
Initial nodes: 439
END *)

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
(* COMMENTS
Initial nodes: 743
END *)

theorem sn3_appls_abbr:
 \forall (c: C).(\forall (d: C).(\forall (w: T).(\forall (i: nat).((getl i c 
(CHead d (Bind Abbr) w)) \to (\forall (vs: TList).((sn3 c (THeads (Flat Appl) 
vs (lift (S i) O w))) \to (sn3 c (THeads (Flat Appl) vs (TLRef i)))))))))
\def
 \lambda (c: C).(\lambda (d: C).(\lambda (w: T).(\lambda (i: nat).(\lambda 
(H: (getl i c (CHead d (Bind Abbr) w))).(\lambda (vs: TList).(TList_ind 
(\lambda (t: TList).((sn3 c (THeads (Flat Appl) t (lift (S i) O w))) \to (sn3 
c (THeads (Flat Appl) t (TLRef i))))) (\lambda (H0: (sn3 c (lift (S i) O 
w))).(let H_y \def (sn3_gen_lift c w (S i) O H0 d (getl_drop Abbr c d w i H)) 
in (sn3_abbr c d w i H H_y))) (\lambda (v: T).(\lambda (vs0: 
TList).(TList_ind (\lambda (t: TList).((((sn3 c (THeads (Flat Appl) t (lift 
(S i) O w))) \to (sn3 c (THeads (Flat Appl) t (TLRef i))))) \to ((sn3 c 
(THead (Flat Appl) v (THeads (Flat Appl) t (lift (S i) O w)))) \to (sn3 c 
(THead (Flat Appl) v (THeads (Flat Appl) t (TLRef i))))))) (\lambda (_: 
(((sn3 c (THeads (Flat Appl) TNil (lift (S i) O w))) \to (sn3 c (THeads (Flat 
Appl) TNil (TLRef i)))))).(\lambda (H1: (sn3 c (THead (Flat Appl) v (THeads 
(Flat Appl) TNil (lift (S i) O w))))).(sn3_appl_abbr c d w i H v H1))) 
(\lambda (t: T).(\lambda (t0: TList).(\lambda (_: (((((sn3 c (THeads (Flat 
Appl) t0 (lift (S i) O w))) \to (sn3 c (THeads (Flat Appl) t0 (TLRef i))))) 
\to ((sn3 c (THead (Flat Appl) v (THeads (Flat Appl) t0 (lift (S i) O w)))) 
\to (sn3 c (THead (Flat Appl) v (THeads (Flat Appl) t0 (TLRef 
i)))))))).(\lambda (H1: (((sn3 c (THeads (Flat Appl) (TCons t t0) (lift (S i) 
O w))) \to (sn3 c (THeads (Flat Appl) (TCons t t0) (TLRef i)))))).(\lambda 
(H2: (sn3 c (THead (Flat Appl) v (THeads (Flat Appl) (TCons t t0) (lift (S i) 
O w))))).(let H_x \def (sn3_gen_flat Appl c v (THeads (Flat Appl) (TCons t 
t0) (lift (S i) O w)) H2) in (let H3 \def H_x in (land_ind (sn3 c v) (sn3 c 
(THead (Flat Appl) t (THeads (Flat Appl) t0 (lift (S i) O w)))) (sn3 c (THead 
(Flat Appl) v (THeads (Flat Appl) (TCons t t0) (TLRef i)))) (\lambda (H4: 
(sn3 c v)).(\lambda (H5: (sn3 c (THead (Flat Appl) t (THeads (Flat Appl) t0 
(lift (S i) O w))))).(sn3_appl_appls t (TLRef i) t0 c (H1 H5) v H4 (\lambda 
(u2: T).(\lambda (H6: (pr3 c (THeads (Flat Appl) (TCons t t0) (TLRef i)) 
u2)).(\lambda (H7: (((iso (THeads (Flat Appl) (TCons t t0) (TLRef i)) u2) \to 
(\forall (P: Prop).P)))).(sn3_pr3_trans c (THead (Flat Appl) v (THeads (Flat 
Appl) (TCons t t0) (lift (S i) O w))) H2 (THead (Flat Appl) v u2) 
(pr3_thin_dx c (THeads (Flat Appl) (TCons t t0) (lift (S i) O w)) u2 
(pr3_iso_appls_abbr c d w i H (TCons t t0) u2 H6 H7) v Appl)))))))) 
H3)))))))) vs0))) vs)))))).
(* COMMENTS
Initial nodes: 797
END *)

theorem sns3_lifts:
 \forall (c: C).(\forall (d: C).(\forall (h: nat).(\forall (i: nat).((drop h 
i c d) \to (\forall (ts: TList).((sns3 d ts) \to (sns3 c (lifts h i ts))))))))
\def
 \lambda (c: C).(\lambda (d: C).(\lambda (h: nat).(\lambda (i: nat).(\lambda 
(H: (drop h i c d)).(\lambda (ts: TList).(TList_ind (\lambda (t: 
TList).((sns3 d t) \to (sns3 c (lifts h i t)))) (\lambda (H0: True).H0) 
(\lambda (t: T).(\lambda (t0: TList).(\lambda (H0: (((sns3 d t0) \to (sns3 c 
(lifts h i t0))))).(\lambda (H1: (land (sn3 d t) (sns3 d t0))).(let H2 \def 
H1 in (land_ind (sn3 d t) (sns3 d t0) (land (sn3 c (lift h i t)) (sns3 c 
(lifts h i t0))) (\lambda (H3: (sn3 d t)).(\lambda (H4: (sns3 d t0)).(conj 
(sn3 c (lift h i t)) (sns3 c (lifts h i t0)) (sn3_lift d t H3 c h i H) (H0 
H4)))) H2)))))) ts)))))).
(* COMMENTS
Initial nodes: 185
END *)

