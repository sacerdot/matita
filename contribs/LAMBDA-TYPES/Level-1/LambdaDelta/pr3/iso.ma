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

set "baseuri" "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/pr3/iso".

include "pr3/fwd.ma".

include "iso/fwd.ma".

theorem pr3_iso_appls_cast:
 \forall (c: C).(\forall (v: T).(\forall (t: T).(\forall (vs: TList).(let u1 
\def (THeads (Flat Appl) vs (THead (Flat Cast) v t)) in (\forall (u2: 
T).((pr3 c u1 u2) \to ((((iso u1 u2) \to (\forall (P: Prop).P))) \to (pr3 c 
(THeads (Flat Appl) vs t) u2))))))))
\def
 \lambda (c: C).(\lambda (v: T).(\lambda (t: T).(\lambda (vs: 
TList).(TList_ind (\lambda (t0: TList).(let u1 \def (THeads (Flat Appl) t0 
(THead (Flat Cast) v t)) in (\forall (u2: T).((pr3 c u1 u2) \to ((((iso u1 
u2) \to (\forall (P: Prop).P))) \to (pr3 c (THeads (Flat Appl) t0 t) u2)))))) 
(\lambda (u2: T).(\lambda (H: (pr3 c (THead (Flat Cast) v t) u2)).(\lambda 
(H0: (((iso (THead (Flat Cast) v t) u2) \to (\forall (P: Prop).P)))).(let H1 
\def (pr3_gen_cast c v t u2 H) in (or_ind (ex3_2 T T (\lambda (u3: 
T).(\lambda (t2: T).(eq T u2 (THead (Flat Cast) u3 t2)))) (\lambda (u3: 
T).(\lambda (_: T).(pr3 c v u3))) (\lambda (_: T).(\lambda (t2: T).(pr3 c t 
t2)))) (pr3 c t u2) (pr3 c t u2) (\lambda (H2: (ex3_2 T T (\lambda (u3: 
T).(\lambda (t2: T).(eq T u2 (THead (Flat Cast) u3 t2)))) (\lambda (u3: 
T).(\lambda (_: T).(pr3 c v u3))) (\lambda (_: T).(\lambda (t2: T).(pr3 c t 
t2))))).(ex3_2_ind T T (\lambda (u3: T).(\lambda (t2: T).(eq T u2 (THead 
(Flat Cast) u3 t2)))) (\lambda (u3: T).(\lambda (_: T).(pr3 c v u3))) 
(\lambda (_: T).(\lambda (t2: T).(pr3 c t t2))) (pr3 c t u2) (\lambda (x0: 
T).(\lambda (x1: T).(\lambda (H3: (eq T u2 (THead (Flat Cast) x0 
x1))).(\lambda (_: (pr3 c v x0)).(\lambda (_: (pr3 c t x1)).(let H6 \def 
(eq_ind T u2 (\lambda (t0: T).((iso (THead (Flat Cast) v t) t0) \to (\forall 
(P: Prop).P))) H0 (THead (Flat Cast) x0 x1) H3) in (eq_ind_r T (THead (Flat 
Cast) x0 x1) (\lambda (t0: T).(pr3 c t t0)) (H6 (iso_head v x0 t x1 (Flat 
Cast)) (pr3 c t (THead (Flat Cast) x0 x1))) u2 H3))))))) H2)) (\lambda (H2: 
(pr3 c t u2)).H2) H1))))) (\lambda (t0: T).(\lambda (t1: TList).(\lambda (H: 
((\forall (u2: T).((pr3 c (THeads (Flat Appl) t1 (THead (Flat Cast) v t)) u2) 
\to ((((iso (THeads (Flat Appl) t1 (THead (Flat Cast) v t)) u2) \to (\forall 
(P: Prop).P))) \to (pr3 c (THeads (Flat Appl) t1 t) u2)))))).(\lambda (u2: 
T).(\lambda (H0: (pr3 c (THead (Flat Appl) t0 (THeads (Flat Appl) t1 (THead 
(Flat Cast) v t))) u2)).(\lambda (H1: (((iso (THead (Flat Appl) t0 (THeads 
(Flat Appl) t1 (THead (Flat Cast) v t))) u2) \to (\forall (P: 
Prop).P)))).(let H2 \def (pr3_gen_appl c t0 (THeads (Flat Appl) t1 (THead 
(Flat Cast) v t)) u2 H0) in (or3_ind (ex3_2 T T (\lambda (u3: T).(\lambda 
(t2: T).(eq T u2 (THead (Flat Appl) u3 t2)))) (\lambda (u3: T).(\lambda (_: 
T).(pr3 c t0 u3))) (\lambda (_: T).(\lambda (t2: T).(pr3 c (THeads (Flat 
Appl) t1 (THead (Flat Cast) v t)) t2)))) (ex4_4 T T T T (\lambda (_: 
T).(\lambda (_: T).(\lambda (u3: T).(\lambda (t2: T).(pr3 c (THead (Bind 
Abbr) u3 t2) u2))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u3: 
T).(\lambda (_: T).(pr3 c t0 u3))))) (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(pr3 c (THeads (Flat Appl) t1 (THead (Flat 
Cast) v t)) (THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (t2: T).(\forall (b: B).(\forall (u: T).(pr3 
(CHead c (Bind b) u) z1 t2)))))))) (ex6_6 B T T T T T (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(pr3 c (THeads (Flat 
Appl) t1 (THead (Flat Cast) v t)) (THead (Bind b) y1 z1)))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u3: T).(\lambda 
(y2: T).(pr3 c (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u3) z2)) 
u2))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u3: T).(\lambda (_: T).(pr3 c t0 u3))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr3 c y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr3 (CHead c (Bind b) 
y2) z1 z2)))))))) (pr3 c (THead (Flat Appl) t0 (THeads (Flat Appl) t1 t)) u2) 
(\lambda (H3: (ex3_2 T T (\lambda (u3: T).(\lambda (t2: T).(eq T u2 (THead 
(Flat Appl) u3 t2)))) (\lambda (u3: T).(\lambda (_: T).(pr3 c t0 u3))) 
(\lambda (_: T).(\lambda (t2: T).(pr3 c (THeads (Flat Appl) t1 (THead (Flat 
Cast) v t)) t2))))).(ex3_2_ind T T (\lambda (u3: T).(\lambda (t2: T).(eq T u2 
(THead (Flat Appl) u3 t2)))) (\lambda (u3: T).(\lambda (_: T).(pr3 c t0 u3))) 
(\lambda (_: T).(\lambda (t2: T).(pr3 c (THeads (Flat Appl) t1 (THead (Flat 
Cast) v t)) t2))) (pr3 c (THead (Flat Appl) t0 (THeads (Flat Appl) t1 t)) u2) 
(\lambda (x0: T).(\lambda (x1: T).(\lambda (H4: (eq T u2 (THead (Flat Appl) 
x0 x1))).(\lambda (_: (pr3 c t0 x0)).(\lambda (_: (pr3 c (THeads (Flat Appl) 
t1 (THead (Flat Cast) v t)) x1)).(let H7 \def (eq_ind T u2 (\lambda (t2: 
T).((iso (THead (Flat Appl) t0 (THeads (Flat Appl) t1 (THead (Flat Cast) v 
t))) t2) \to (\forall (P: Prop).P))) H1 (THead (Flat Appl) x0 x1) H4) in 
(eq_ind_r T (THead (Flat Appl) x0 x1) (\lambda (t2: T).(pr3 c (THead (Flat 
Appl) t0 (THeads (Flat Appl) t1 t)) t2)) (H7 (iso_head t0 x0 (THeads (Flat 
Appl) t1 (THead (Flat Cast) v t)) x1 (Flat Appl)) (pr3 c (THead (Flat Appl) 
t0 (THeads (Flat Appl) t1 t)) (THead (Flat Appl) x0 x1))) u2 H4))))))) H3)) 
(\lambda (H3: (ex4_4 T T T T (\lambda (_: T).(\lambda (_: T).(\lambda (u3: 
T).(\lambda (t2: T).(pr3 c (THead (Bind Abbr) u3 t2) u2))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u3: T).(\lambda (_: T).(pr3 c t0 u3))))) 
(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(pr3 c 
(THeads (Flat Appl) t1 (THead (Flat Cast) v t)) (THead (Bind Abst) y1 
z1)))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t2: 
T).(\forall (b: B).(\forall (u: T).(pr3 (CHead c (Bind b) u) z1 
t2))))))))).(ex4_4_ind T T T T (\lambda (_: T).(\lambda (_: T).(\lambda (u3: 
T).(\lambda (t2: T).(pr3 c (THead (Bind Abbr) u3 t2) u2))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u3: T).(\lambda (_: T).(pr3 c t0 u3))))) 
(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(pr3 c 
(THeads (Flat Appl) t1 (THead (Flat Cast) v t)) (THead (Bind Abst) y1 
z1)))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t2: 
T).(\forall (b: B).(\forall (u: T).(pr3 (CHead c (Bind b) u) z1 t2))))))) 
(pr3 c (THead (Flat Appl) t0 (THeads (Flat Appl) t1 t)) u2) (\lambda (x0: 
T).(\lambda (x1: T).(\lambda (x2: T).(\lambda (x3: T).(\lambda (H4: (pr3 c 
(THead (Bind Abbr) x2 x3) u2)).(\lambda (H5: (pr3 c t0 x2)).(\lambda (H6: 
(pr3 c (THeads (Flat Appl) t1 (THead (Flat Cast) v t)) (THead (Bind Abst) x0 
x1))).(\lambda (H7: ((\forall (b: B).(\forall (u: T).(pr3 (CHead c (Bind b) 
u) x1 x3))))).(pr3_t (THead (Bind Abbr) t0 x1) (THead (Flat Appl) t0 (THeads 
(Flat Appl) t1 t)) c (pr3_t (THead (Flat Appl) t0 (THead (Bind Abst) x0 x1)) 
(THead (Flat Appl) t0 (THeads (Flat Appl) t1 t)) c (pr3_thin_dx c (THeads 
(Flat Appl) t1 t) (THead (Bind Abst) x0 x1) (H (THead (Bind Abst) x0 x1) H6 
(\lambda (H8: (iso (THeads (Flat Appl) t1 (THead (Flat Cast) v t)) (THead 
(Bind Abst) x0 x1))).(\lambda (P: Prop).(iso_flats_flat_bind_false Appl Cast 
Abst x0 v x1 t t1 H8 P)))) t0 Appl) (THead (Bind Abbr) t0 x1) (pr3_pr2 c 
(THead (Flat Appl) t0 (THead (Bind Abst) x0 x1)) (THead (Bind Abbr) t0 x1) 
(pr2_free c (THead (Flat Appl) t0 (THead (Bind Abst) x0 x1)) (THead (Bind 
Abbr) t0 x1) (pr0_beta x0 t0 t0 (pr0_refl t0) x1 x1 (pr0_refl x1))))) u2 
(pr3_t (THead (Bind Abbr) x2 x3) (THead (Bind Abbr) t0 x1) c (pr3_head_12 c 
t0 x2 H5 (Bind Abbr) x1 x3 (H7 Abbr x2)) u2 H4)))))))))) H3)) (\lambda (H3: 
(ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(pr3 c (THeads (Flat Appl) t1 (THead (Flat Cast) v t)) (THead (Bind b) 
y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: 
T).(\lambda (u3: T).(\lambda (y2: T).(pr3 c (THead (Bind b) y2 (THead (Flat 
Appl) (lift (S O) O u3) z2)) u2))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda (_: T).(pr3 c t0 
u3))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr3 c y1 y2))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr3 (CHead c (Bind b) y2) z1 z2))))))))).(ex6_6_ind B T T T T T 
(\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(pr3 c 
(THeads (Flat Appl) t1 (THead (Flat Cast) v t)) (THead (Bind b) y1 z1)))))))) 
(\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda 
(u3: T).(\lambda (y2: T).(pr3 c (THead (Bind b) y2 (THead (Flat Appl) (lift 
(S O) O u3) z2)) u2))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u3: T).(\lambda (_: T).(pr3 c t0 u3))))))) 
(\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (y2: T).(pr3 c y1 y2))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr3 
(CHead c (Bind b) y2) z1 z2))))))) (pr3 c (THead (Flat Appl) t0 (THeads (Flat 
Appl) t1 t)) u2) (\lambda (x0: B).(\lambda (x1: T).(\lambda (x2: T).(\lambda 
(x3: T).(\lambda (x4: T).(\lambda (x5: T).(\lambda (H4: (not (eq B x0 
Abst))).(\lambda (H5: (pr3 c (THeads (Flat Appl) t1 (THead (Flat Cast) v t)) 
(THead (Bind x0) x1 x2))).(\lambda (H6: (pr3 c (THead (Bind x0) x5 (THead 
(Flat Appl) (lift (S O) O x4) x3)) u2)).(\lambda (H7: (pr3 c t0 x4)).(\lambda 
(H8: (pr3 c x1 x5)).(\lambda (H9: (pr3 (CHead c (Bind x0) x5) x2 x3)).(pr3_t 
(THead (Bind x0) x1 (THead (Flat Appl) (lift (S O) O x4) x2)) (THead (Flat 
Appl) t0 (THeads (Flat Appl) t1 t)) c (pr3_t (THead (Bind x0) x1 (THead (Flat 
Appl) (lift (S O) O t0) x2)) (THead (Flat Appl) t0 (THeads (Flat Appl) t1 t)) 
c (pr3_t (THead (Flat Appl) t0 (THead (Bind x0) x1 x2)) (THead (Flat Appl) t0 
(THeads (Flat Appl) t1 t)) c (pr3_thin_dx c (THeads (Flat Appl) t1 t) (THead 
(Bind x0) x1 x2) (H (THead (Bind x0) x1 x2) H5 (\lambda (H10: (iso (THeads 
(Flat Appl) t1 (THead (Flat Cast) v t)) (THead (Bind x0) x1 x2))).(\lambda 
(P: Prop).(iso_flats_flat_bind_false Appl Cast x0 x1 v x2 t t1 H10 P)))) t0 
Appl) (THead (Bind x0) x1 (THead (Flat Appl) (lift (S O) O t0) x2)) (pr3_pr2 
c (THead (Flat Appl) t0 (THead (Bind x0) x1 x2)) (THead (Bind x0) x1 (THead 
(Flat Appl) (lift (S O) O t0) x2)) (pr2_free c (THead (Flat Appl) t0 (THead 
(Bind x0) x1 x2)) (THead (Bind x0) x1 (THead (Flat Appl) (lift (S O) O t0) 
x2)) (pr0_upsilon x0 H4 t0 t0 (pr0_refl t0) x1 x1 (pr0_refl x1) x2 x2 
(pr0_refl x2))))) (THead (Bind x0) x1 (THead (Flat Appl) (lift (S O) O x4) 
x2)) (pr3_head_12 c x1 x1 (pr3_refl c x1) (Bind x0) (THead (Flat Appl) (lift 
(S O) O t0) x2) (THead (Flat Appl) (lift (S O) O x4) x2) (pr3_head_12 (CHead 
c (Bind x0) x1) (lift (S O) O t0) (lift (S O) O x4) (pr3_lift (CHead c (Bind 
x0) x1) c (S O) O (drop_drop (Bind x0) O c c (drop_refl c) x1) t0 x4 H7) 
(Flat Appl) x2 x2 (pr3_refl (CHead (CHead c (Bind x0) x1) (Flat Appl) (lift 
(S O) O x4)) x2)))) u2 (pr3_t (THead (Bind x0) x5 (THead (Flat Appl) (lift (S 
O) O x4) x3)) (THead (Bind x0) x1 (THead (Flat Appl) (lift (S O) O x4) x2)) c 
(pr3_head_12 c x1 x5 H8 (Bind x0) (THead (Flat Appl) (lift (S O) O x4) x2) 
(THead (Flat Appl) (lift (S O) O x4) x3) (pr3_thin_dx (CHead c (Bind x0) x5) 
x2 x3 H9 (lift (S O) O x4) Appl)) u2 H6)))))))))))))) H3)) H2)))))))) vs)))).

