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

include "Basic-1/pr3/fwd.ma".

include "Basic-1/iso/props.ma".

include "Basic-1/tlist/props.ma".

theorem pr3_iso_appls_abbr:
 \forall (c: C).(\forall (d: C).(\forall (w: T).(\forall (i: nat).((getl i c 
(CHead d (Bind Abbr) w)) \to (\forall (vs: TList).(let u1 \def (THeads (Flat 
Appl) vs (TLRef i)) in (\forall (u2: T).((pr3 c u1 u2) \to ((((iso u1 u2) \to 
(\forall (P: Prop).P))) \to (pr3 c (THeads (Flat Appl) vs (lift (S i) O w)) 
u2))))))))))
\def
 \lambda (c: C).(\lambda (d: C).(\lambda (w: T).(\lambda (i: nat).(\lambda 
(H: (getl i c (CHead d (Bind Abbr) w))).(\lambda (vs: TList).(TList_ind 
(\lambda (t: TList).(let u1 \def (THeads (Flat Appl) t (TLRef i)) in (\forall 
(u2: T).((pr3 c u1 u2) \to ((((iso u1 u2) \to (\forall (P: Prop).P))) \to 
(pr3 c (THeads (Flat Appl) t (lift (S i) O w)) u2)))))) (\lambda (u2: 
T).(\lambda (H0: (pr3 c (TLRef i) u2)).(\lambda (H1: (((iso (TLRef i) u2) \to 
(\forall (P: Prop).P)))).(let H2 \def (pr3_gen_lref c u2 i H0) in (or_ind (eq 
T u2 (TLRef i)) (ex3_3 C T T (\lambda (d0: C).(\lambda (u: T).(\lambda (_: 
T).(getl i c (CHead d0 (Bind Abbr) u))))) (\lambda (d0: C).(\lambda (u: 
T).(\lambda (v: T).(pr3 d0 u v)))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(v: T).(eq T u2 (lift (S i) O v)))))) (pr3 c (lift (S i) O w) u2) (\lambda 
(H3: (eq T u2 (TLRef i))).(let H4 \def (eq_ind T u2 (\lambda (t: T).((iso 
(TLRef i) t) \to (\forall (P: Prop).P))) H1 (TLRef i) H3) in (eq_ind_r T 
(TLRef i) (\lambda (t: T).(pr3 c (lift (S i) O w) t)) (H4 (iso_refl (TLRef 
i)) (pr3 c (lift (S i) O w) (TLRef i))) u2 H3))) (\lambda (H3: (ex3_3 C T T 
(\lambda (d0: C).(\lambda (u: T).(\lambda (_: T).(getl i c (CHead d0 (Bind 
Abbr) u))))) (\lambda (d0: C).(\lambda (u: T).(\lambda (v: T).(pr3 d0 u v)))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (v: T).(eq T u2 (lift (S i) O 
v))))))).(ex3_3_ind C T T (\lambda (d0: C).(\lambda (u: T).(\lambda (_: 
T).(getl i c (CHead d0 (Bind Abbr) u))))) (\lambda (d0: C).(\lambda (u: 
T).(\lambda (v: T).(pr3 d0 u v)))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(v: T).(eq T u2 (lift (S i) O v))))) (pr3 c (lift (S i) O w) u2) (\lambda 
(x0: C).(\lambda (x1: T).(\lambda (x2: T).(\lambda (H4: (getl i c (CHead x0 
(Bind Abbr) x1))).(\lambda (H5: (pr3 x0 x1 x2)).(\lambda (H6: (eq T u2 (lift 
(S i) O x2))).(let H7 \def (eq_ind T u2 (\lambda (t: T).((iso (TLRef i) t) 
\to (\forall (P: Prop).P))) H1 (lift (S i) O x2) H6) in (eq_ind_r T (lift (S 
i) O x2) (\lambda (t: T).(pr3 c (lift (S i) O w) t)) (let H8 \def (eq_ind C 
(CHead d (Bind Abbr) w) (\lambda (c0: C).(getl i c c0)) H (CHead x0 (Bind 
Abbr) x1) (getl_mono c (CHead d (Bind Abbr) w) i H (CHead x0 (Bind Abbr) x1) 
H4)) in (let H9 \def (f_equal C C (\lambda (e: C).(match e in C return 
(\lambda (_: C).C) with [(CSort _) \Rightarrow d | (CHead c0 _ _) \Rightarrow 
c0])) (CHead d (Bind Abbr) w) (CHead x0 (Bind Abbr) x1) (getl_mono c (CHead d 
(Bind Abbr) w) i H (CHead x0 (Bind Abbr) x1) H4)) in ((let H10 \def (f_equal 
C T (\lambda (e: C).(match e in C return (\lambda (_: C).T) with [(CSort _) 
\Rightarrow w | (CHead _ _ t) \Rightarrow t])) (CHead d (Bind Abbr) w) (CHead 
x0 (Bind Abbr) x1) (getl_mono c (CHead d (Bind Abbr) w) i H (CHead x0 (Bind 
Abbr) x1) H4)) in (\lambda (H11: (eq C d x0)).(let H12 \def (eq_ind_r T x1 
(\lambda (t: T).(getl i c (CHead x0 (Bind Abbr) t))) H8 w H10) in (let H13 
\def (eq_ind_r T x1 (\lambda (t: T).(pr3 x0 t x2)) H5 w H10) in (let H14 \def 
(eq_ind_r C x0 (\lambda (c0: C).(getl i c (CHead c0 (Bind Abbr) w))) H12 d 
H11) in (let H15 \def (eq_ind_r C x0 (\lambda (c0: C).(pr3 c0 w x2)) H13 d 
H11) in (pr3_lift c d (S i) O (getl_drop Abbr c d w i H14) w x2 H15))))))) 
H9))) u2 H6)))))))) H3)) H2))))) (\lambda (t: T).(\lambda (t0: 
TList).(\lambda (H0: ((\forall (u2: T).((pr3 c (THeads (Flat Appl) t0 (TLRef 
i)) u2) \to ((((iso (THeads (Flat Appl) t0 (TLRef i)) u2) \to (\forall (P: 
Prop).P))) \to (pr3 c (THeads (Flat Appl) t0 (lift (S i) O w)) 
u2)))))).(\lambda (u2: T).(\lambda (H1: (pr3 c (THead (Flat Appl) t (THeads 
(Flat Appl) t0 (TLRef i))) u2)).(\lambda (H2: (((iso (THead (Flat Appl) t 
(THeads (Flat Appl) t0 (TLRef i))) u2) \to (\forall (P: Prop).P)))).(let H3 
\def (pr3_gen_appl c t (THeads (Flat Appl) t0 (TLRef i)) u2 H1) in (or3_ind 
(ex3_2 T T (\lambda (u3: T).(\lambda (t2: T).(eq T u2 (THead (Flat Appl) u3 
t2)))) (\lambda (u3: T).(\lambda (_: T).(pr3 c t u3))) (\lambda (_: 
T).(\lambda (t2: T).(pr3 c (THeads (Flat Appl) t0 (TLRef i)) t2)))) (ex4_4 T 
T T T (\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda (t2: T).(pr3 
c (THead (Bind Abbr) u3 t2) u2))))) (\lambda (_: T).(\lambda (_: T).(\lambda 
(u3: T).(\lambda (_: T).(pr3 c t u3))))) (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(pr3 c (THeads (Flat Appl) t0 (TLRef i)) 
(THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t2: T).(\forall (b: B).(\forall (u: T).(pr3 (CHead c (Bind b) u) 
z1 t2)))))))) (ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) 
(\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(pr3 c (THeads (Flat Appl) t0 (TLRef i)) (THead (Bind 
b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(z2: T).(\lambda (u3: T).(\lambda (y2: T).(pr3 c (THead (Bind b) y2 (THead 
(Flat Appl) (lift (S O) O u3) z2)) u2))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda (_: T).(pr3 c t 
u3))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr3 c y1 y2))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr3 (CHead c (Bind b) y2) z1 z2)))))))) (pr3 c (THead (Flat Appl) t 
(THeads (Flat Appl) t0 (lift (S i) O w))) u2) (\lambda (H4: (ex3_2 T T 
(\lambda (u3: T).(\lambda (t2: T).(eq T u2 (THead (Flat Appl) u3 t2)))) 
(\lambda (u3: T).(\lambda (_: T).(pr3 c t u3))) (\lambda (_: T).(\lambda (t2: 
T).(pr3 c (THeads (Flat Appl) t0 (TLRef i)) t2))))).(ex3_2_ind T T (\lambda 
(u3: T).(\lambda (t2: T).(eq T u2 (THead (Flat Appl) u3 t2)))) (\lambda (u3: 
T).(\lambda (_: T).(pr3 c t u3))) (\lambda (_: T).(\lambda (t2: T).(pr3 c 
(THeads (Flat Appl) t0 (TLRef i)) t2))) (pr3 c (THead (Flat Appl) t (THeads 
(Flat Appl) t0 (lift (S i) O w))) u2) (\lambda (x0: T).(\lambda (x1: 
T).(\lambda (H5: (eq T u2 (THead (Flat Appl) x0 x1))).(\lambda (_: (pr3 c t 
x0)).(\lambda (_: (pr3 c (THeads (Flat Appl) t0 (TLRef i)) x1)).(let H8 \def 
(eq_ind T u2 (\lambda (t1: T).((iso (THead (Flat Appl) t (THeads (Flat Appl) 
t0 (TLRef i))) t1) \to (\forall (P: Prop).P))) H2 (THead (Flat Appl) x0 x1) 
H5) in (eq_ind_r T (THead (Flat Appl) x0 x1) (\lambda (t1: T).(pr3 c (THead 
(Flat Appl) t (THeads (Flat Appl) t0 (lift (S i) O w))) t1)) (H8 (iso_head t 
x0 (THeads (Flat Appl) t0 (TLRef i)) x1 (Flat Appl)) (pr3 c (THead (Flat 
Appl) t (THeads (Flat Appl) t0 (lift (S i) O w))) (THead (Flat Appl) x0 x1))) 
u2 H5))))))) H4)) (\lambda (H4: (ex4_4 T T T T (\lambda (_: T).(\lambda (_: 
T).(\lambda (u3: T).(\lambda (t2: T).(pr3 c (THead (Bind Abbr) u3 t2) u2))))) 
(\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda (_: T).(pr3 c t 
u3))))) (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: 
T).(pr3 c (THeads (Flat Appl) t0 (TLRef i)) (THead (Bind Abst) y1 z1)))))) 
(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t2: T).(\forall 
(b: B).(\forall (u: T).(pr3 (CHead c (Bind b) u) z1 t2))))))))).(ex4_4_ind T 
T T T (\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda (t2: T).(pr3 
c (THead (Bind Abbr) u3 t2) u2))))) (\lambda (_: T).(\lambda (_: T).(\lambda 
(u3: T).(\lambda (_: T).(pr3 c t u3))))) (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(pr3 c (THeads (Flat Appl) t0 (TLRef i)) 
(THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t2: T).(\forall (b: B).(\forall (u: T).(pr3 (CHead c (Bind b) u) 
z1 t2))))))) (pr3 c (THead (Flat Appl) t (THeads (Flat Appl) t0 (lift (S i) O 
w))) u2) (\lambda (x0: T).(\lambda (x1: T).(\lambda (x2: T).(\lambda (x3: 
T).(\lambda (H5: (pr3 c (THead (Bind Abbr) x2 x3) u2)).(\lambda (H6: (pr3 c t 
x2)).(\lambda (H7: (pr3 c (THeads (Flat Appl) t0 (TLRef i)) (THead (Bind 
Abst) x0 x1))).(\lambda (H8: ((\forall (b: B).(\forall (u: T).(pr3 (CHead c 
(Bind b) u) x1 x3))))).(pr3_t (THead (Bind Abbr) t x1) (THead (Flat Appl) t 
(THeads (Flat Appl) t0 (lift (S i) O w))) c (pr3_t (THead (Flat Appl) t 
(THead (Bind Abst) x0 x1)) (THead (Flat Appl) t (THeads (Flat Appl) t0 (lift 
(S i) O w))) c (pr3_thin_dx c (THeads (Flat Appl) t0 (lift (S i) O w)) (THead 
(Bind Abst) x0 x1) (H0 (THead (Bind Abst) x0 x1) H7 (\lambda (H9: (iso 
(THeads (Flat Appl) t0 (TLRef i)) (THead (Bind Abst) x0 x1))).(\lambda (P: 
Prop).(iso_flats_lref_bind_false Appl Abst i x0 x1 t0 H9 P)))) t Appl) (THead 
(Bind Abbr) t x1) (pr3_pr2 c (THead (Flat Appl) t (THead (Bind Abst) x0 x1)) 
(THead (Bind Abbr) t x1) (pr2_free c (THead (Flat Appl) t (THead (Bind Abst) 
x0 x1)) (THead (Bind Abbr) t x1) (pr0_beta x0 t t (pr0_refl t) x1 x1 
(pr0_refl x1))))) u2 (pr3_t (THead (Bind Abbr) x2 x3) (THead (Bind Abbr) t 
x1) c (pr3_head_12 c t x2 H6 (Bind Abbr) x1 x3 (H8 Abbr x2)) u2 H5)))))))))) 
H4)) (\lambda (H4: (ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B 
b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(pr3 c (THeads (Flat Appl) t0 (TLRef i)) 
(THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (z2: T).(\lambda (u3: T).(\lambda (y2: T).(pr3 c (THead (Bind b) 
y2 (THead (Flat Appl) (lift (S O) O u3) z2)) u2))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda 
(_: T).(pr3 c t u3))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr3 c y1 y2))))))) 
(\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda 
(_: T).(\lambda (y2: T).(pr3 (CHead c (Bind b) y2) z1 z2))))))))).(ex6_6_ind 
B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(pr3 c (THeads (Flat Appl) t0 (TLRef i)) (THead (Bind b) y1 z1)))))))) 
(\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda 
(u3: T).(\lambda (y2: T).(pr3 c (THead (Bind b) y2 (THead (Flat Appl) (lift 
(S O) O u3) z2)) u2))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u3: T).(\lambda (_: T).(pr3 c t u3))))))) 
(\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (y2: T).(pr3 c y1 y2))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr3 
(CHead c (Bind b) y2) z1 z2))))))) (pr3 c (THead (Flat Appl) t (THeads (Flat 
Appl) t0 (lift (S i) O w))) u2) (\lambda (x0: B).(\lambda (x1: T).(\lambda 
(x2: T).(\lambda (x3: T).(\lambda (x4: T).(\lambda (x5: T).(\lambda (H5: (not 
(eq B x0 Abst))).(\lambda (H6: (pr3 c (THeads (Flat Appl) t0 (TLRef i)) 
(THead (Bind x0) x1 x2))).(\lambda (H7: (pr3 c (THead (Bind x0) x5 (THead 
(Flat Appl) (lift (S O) O x4) x3)) u2)).(\lambda (H8: (pr3 c t x4)).(\lambda 
(H9: (pr3 c x1 x5)).(\lambda (H10: (pr3 (CHead c (Bind x0) x5) x2 x3)).(pr3_t 
(THead (Bind x0) x1 (THead (Flat Appl) (lift (S O) O x4) x2)) (THead (Flat 
Appl) t (THeads (Flat Appl) t0 (lift (S i) O w))) c (pr3_t (THead (Bind x0) 
x1 (THead (Flat Appl) (lift (S O) O t) x2)) (THead (Flat Appl) t (THeads 
(Flat Appl) t0 (lift (S i) O w))) c (pr3_t (THead (Flat Appl) t (THead (Bind 
x0) x1 x2)) (THead (Flat Appl) t (THeads (Flat Appl) t0 (lift (S i) O w))) c 
(pr3_thin_dx c (THeads (Flat Appl) t0 (lift (S i) O w)) (THead (Bind x0) x1 
x2) (H0 (THead (Bind x0) x1 x2) H6 (\lambda (H11: (iso (THeads (Flat Appl) t0 
(TLRef i)) (THead (Bind x0) x1 x2))).(\lambda (P: 
Prop).(iso_flats_lref_bind_false Appl x0 i x1 x2 t0 H11 P)))) t Appl) (THead 
(Bind x0) x1 (THead (Flat Appl) (lift (S O) O t) x2)) (pr3_pr2 c (THead (Flat 
Appl) t (THead (Bind x0) x1 x2)) (THead (Bind x0) x1 (THead (Flat Appl) (lift 
(S O) O t) x2)) (pr2_free c (THead (Flat Appl) t (THead (Bind x0) x1 x2)) 
(THead (Bind x0) x1 (THead (Flat Appl) (lift (S O) O t) x2)) (pr0_upsilon x0 
H5 t t (pr0_refl t) x1 x1 (pr0_refl x1) x2 x2 (pr0_refl x2))))) (THead (Bind 
x0) x1 (THead (Flat Appl) (lift (S O) O x4) x2)) (pr3_head_12 c x1 x1 
(pr3_refl c x1) (Bind x0) (THead (Flat Appl) (lift (S O) O t) x2) (THead 
(Flat Appl) (lift (S O) O x4) x2) (pr3_head_12 (CHead c (Bind x0) x1) (lift 
(S O) O t) (lift (S O) O x4) (pr3_lift (CHead c (Bind x0) x1) c (S O) O 
(drop_drop (Bind x0) O c c (drop_refl c) x1) t x4 H8) (Flat Appl) x2 x2 
(pr3_refl (CHead (CHead c (Bind x0) x1) (Flat Appl) (lift (S O) O x4)) x2)))) 
u2 (pr3_t (THead (Bind x0) x5 (THead (Flat Appl) (lift (S O) O x4) x3)) 
(THead (Bind x0) x1 (THead (Flat Appl) (lift (S O) O x4) x2)) c (pr3_head_12 
c x1 x5 H9 (Bind x0) (THead (Flat Appl) (lift (S O) O x4) x2) (THead (Flat 
Appl) (lift (S O) O x4) x3) (pr3_thin_dx (CHead c (Bind x0) x5) x2 x3 H10 
(lift (S O) O x4) Appl)) u2 H7)))))))))))))) H4)) H3)))))))) vs)))))).
(* COMMENTS
Initial nodes: 3759
END *)

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
(* COMMENTS
Initial nodes: 3297
END *)

theorem pr3_iso_appl_bind:
 \forall (b: B).((not (eq B b Abst)) \to (\forall (v1: T).(\forall (v2: 
T).(\forall (t: T).(let u1 \def (THead (Flat Appl) v1 (THead (Bind b) v2 t)) 
in (\forall (c: C).(\forall (u2: T).((pr3 c u1 u2) \to ((((iso u1 u2) \to 
(\forall (P: Prop).P))) \to (pr3 c (THead (Bind b) v2 (THead (Flat Appl) 
(lift (S O) O v1) t)) u2))))))))))
\def
 \lambda (b: B).(\lambda (H: (not (eq B b Abst))).(\lambda (v1: T).(\lambda 
(v2: T).(\lambda (t: T).(\lambda (c: C).(\lambda (u2: T).(\lambda (H0: (pr3 c 
(THead (Flat Appl) v1 (THead (Bind b) v2 t)) u2)).(\lambda (H1: (((iso (THead 
(Flat Appl) v1 (THead (Bind b) v2 t)) u2) \to (\forall (P: Prop).P)))).(let 
H2 \def (pr3_gen_appl c v1 (THead (Bind b) v2 t) u2 H0) in (or3_ind (ex3_2 T 
T (\lambda (u3: T).(\lambda (t2: T).(eq T u2 (THead (Flat Appl) u3 t2)))) 
(\lambda (u3: T).(\lambda (_: T).(pr3 c v1 u3))) (\lambda (_: T).(\lambda 
(t2: T).(pr3 c (THead (Bind b) v2 t) t2)))) (ex4_4 T T T T (\lambda (_: 
T).(\lambda (_: T).(\lambda (u3: T).(\lambda (t2: T).(pr3 c (THead (Bind 
Abbr) u3 t2) u2))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u3: 
T).(\lambda (_: T).(pr3 c v1 u3))))) (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(pr3 c (THead (Bind b) v2 t) (THead (Bind 
Abst) y1 z1)))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda 
(t2: T).(\forall (b0: B).(\forall (u: T).(pr3 (CHead c (Bind b0) u) z1 
t2)))))))) (ex6_6 B T T T T T (\lambda (b0: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b0 Abst)))))))) 
(\lambda (b0: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(pr3 c (THead (Bind b) v2 t) (THead (Bind b0) y1 
z1)))))))) (\lambda (b0: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: 
T).(\lambda (u3: T).(\lambda (y2: T).(pr3 c (THead (Bind b0) y2 (THead (Flat 
Appl) (lift (S O) O u3) z2)) u2))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda (_: T).(pr3 c v1 
u3))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr3 c y1 y2))))))) (\lambda (b0: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr3 (CHead c (Bind b0) y2) z1 z2)))))))) (pr3 c (THead (Bind b) v2 
(THead (Flat Appl) (lift (S O) O v1) t)) u2) (\lambda (H3: (ex3_2 T T 
(\lambda (u3: T).(\lambda (t2: T).(eq T u2 (THead (Flat Appl) u3 t2)))) 
(\lambda (u3: T).(\lambda (_: T).(pr3 c v1 u3))) (\lambda (_: T).(\lambda 
(t2: T).(pr3 c (THead (Bind b) v2 t) t2))))).(ex3_2_ind T T (\lambda (u3: 
T).(\lambda (t2: T).(eq T u2 (THead (Flat Appl) u3 t2)))) (\lambda (u3: 
T).(\lambda (_: T).(pr3 c v1 u3))) (\lambda (_: T).(\lambda (t2: T).(pr3 c 
(THead (Bind b) v2 t) t2))) (pr3 c (THead (Bind b) v2 (THead (Flat Appl) 
(lift (S O) O v1) t)) u2) (\lambda (x0: T).(\lambda (x1: T).(\lambda (H4: (eq 
T u2 (THead (Flat Appl) x0 x1))).(\lambda (_: (pr3 c v1 x0)).(\lambda (_: 
(pr3 c (THead (Bind b) v2 t) x1)).(let H7 \def (eq_ind T u2 (\lambda (t0: 
T).((iso (THead (Flat Appl) v1 (THead (Bind b) v2 t)) t0) \to (\forall (P: 
Prop).P))) H1 (THead (Flat Appl) x0 x1) H4) in (eq_ind_r T (THead (Flat Appl) 
x0 x1) (\lambda (t0: T).(pr3 c (THead (Bind b) v2 (THead (Flat Appl) (lift (S 
O) O v1) t)) t0)) (H7 (iso_head v1 x0 (THead (Bind b) v2 t) x1 (Flat Appl)) 
(pr3 c (THead (Bind b) v2 (THead (Flat Appl) (lift (S O) O v1) t)) (THead 
(Flat Appl) x0 x1))) u2 H4))))))) H3)) (\lambda (H3: (ex4_4 T T T T (\lambda 
(_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda (t2: T).(pr3 c (THead (Bind 
Abbr) u3 t2) u2))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u3: 
T).(\lambda (_: T).(pr3 c v1 u3))))) (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(pr3 c (THead (Bind b) v2 t) (THead (Bind 
Abst) y1 z1)))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda 
(t2: T).(\forall (b0: B).(\forall (u: T).(pr3 (CHead c (Bind b0) u) z1 
t2))))))))).(ex4_4_ind T T T T (\lambda (_: T).(\lambda (_: T).(\lambda (u3: 
T).(\lambda (t2: T).(pr3 c (THead (Bind Abbr) u3 t2) u2))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u3: T).(\lambda (_: T).(pr3 c v1 u3))))) 
(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(pr3 c 
(THead (Bind b) v2 t) (THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (t2: T).(\forall (b0: B).(\forall (u: 
T).(pr3 (CHead c (Bind b0) u) z1 t2))))))) (pr3 c (THead (Bind b) v2 (THead 
(Flat Appl) (lift (S O) O v1) t)) u2) (\lambda (x0: T).(\lambda (x1: 
T).(\lambda (x2: T).(\lambda (x3: T).(\lambda (H4: (pr3 c (THead (Bind Abbr) 
x2 x3) u2)).(\lambda (H5: (pr3 c v1 x2)).(\lambda (H6: (pr3 c (THead (Bind b) 
v2 t) (THead (Bind Abst) x0 x1))).(\lambda (H7: ((\forall (b0: B).(\forall 
(u: T).(pr3 (CHead c (Bind b0) u) x1 x3))))).(pr3_t (THead (Bind Abbr) x2 x3) 
(THead (Bind b) v2 (THead (Flat Appl) (lift (S O) O v1) t)) c (let H_x \def 
(pr3_gen_bind b H c v2 t (THead (Bind Abst) x0 x1) H6) in (let H8 \def H_x in 
(or_ind (ex3_2 T T (\lambda (u3: T).(\lambda (t2: T).(eq T (THead (Bind Abst) 
x0 x1) (THead (Bind b) u3 t2)))) (\lambda (u3: T).(\lambda (_: T).(pr3 c v2 
u3))) (\lambda (_: T).(\lambda (t2: T).(pr3 (CHead c (Bind b) v2) t t2)))) 
(pr3 (CHead c (Bind b) v2) t (lift (S O) O (THead (Bind Abst) x0 x1))) (pr3 c 
(THead (Bind b) v2 (THead (Flat Appl) (lift (S O) O v1) t)) (THead (Bind 
Abbr) x2 x3)) (\lambda (H9: (ex3_2 T T (\lambda (u3: T).(\lambda (t2: T).(eq 
T (THead (Bind Abst) x0 x1) (THead (Bind b) u3 t2)))) (\lambda (u3: 
T).(\lambda (_: T).(pr3 c v2 u3))) (\lambda (_: T).(\lambda (t2: T).(pr3 
(CHead c (Bind b) v2) t t2))))).(ex3_2_ind T T (\lambda (u3: T).(\lambda (t2: 
T).(eq T (THead (Bind Abst) x0 x1) (THead (Bind b) u3 t2)))) (\lambda (u3: 
T).(\lambda (_: T).(pr3 c v2 u3))) (\lambda (_: T).(\lambda (t2: T).(pr3 
(CHead c (Bind b) v2) t t2))) (pr3 c (THead (Bind b) v2 (THead (Flat Appl) 
(lift (S O) O v1) t)) (THead (Bind Abbr) x2 x3)) (\lambda (x4: T).(\lambda 
(x5: T).(\lambda (H10: (eq T (THead (Bind Abst) x0 x1) (THead (Bind b) x4 
x5))).(\lambda (H11: (pr3 c v2 x4)).(\lambda (H12: (pr3 (CHead c (Bind b) v2) 
t x5)).(let H13 \def (f_equal T B (\lambda (e: T).(match e in T return 
(\lambda (_: T).B) with [(TSort _) \Rightarrow Abst | (TLRef _) \Rightarrow 
Abst | (THead k _ _) \Rightarrow (match k in K return (\lambda (_: K).B) with 
[(Bind b0) \Rightarrow b0 | (Flat _) \Rightarrow Abst])])) (THead (Bind Abst) 
x0 x1) (THead (Bind b) x4 x5) H10) in ((let H14 \def (f_equal T T (\lambda 
(e: T).(match e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow x0 
| (TLRef _) \Rightarrow x0 | (THead _ t0 _) \Rightarrow t0])) (THead (Bind 
Abst) x0 x1) (THead (Bind b) x4 x5) H10) in ((let H15 \def (f_equal T T 
(\lambda (e: T).(match e in T return (\lambda (_: T).T) with [(TSort _) 
\Rightarrow x1 | (TLRef _) \Rightarrow x1 | (THead _ _ t0) \Rightarrow t0])) 
(THead (Bind Abst) x0 x1) (THead (Bind b) x4 x5) H10) in (\lambda (H16: (eq T 
x0 x4)).(\lambda (H17: (eq B Abst b)).(let H18 \def (eq_ind_r T x5 (\lambda 
(t0: T).(pr3 (CHead c (Bind b) v2) t t0)) H12 x1 H15) in (let H19 \def 
(eq_ind_r T x4 (\lambda (t0: T).(pr3 c v2 t0)) H11 x0 H16) in (let H20 \def 
(eq_ind_r B b (\lambda (b0: B).(pr3 (CHead c (Bind b0) v2) t x1)) H18 Abst 
H17) in (let H21 \def (eq_ind_r B b (\lambda (b0: B).(not (eq B b0 Abst))) H 
Abst H17) in (eq_ind B Abst (\lambda (b0: B).(pr3 c (THead (Bind b0) v2 
(THead (Flat Appl) (lift (S O) O v1) t)) (THead (Bind Abbr) x2 x3))) (let H22 
\def (match (H21 (refl_equal B Abst)) in False return (\lambda (_: 
False).(pr3 c (THead (Bind Abst) v2 (THead (Flat Appl) (lift (S O) O v1) t)) 
(THead (Bind Abbr) x2 x3))) with []) in H22) b H17)))))))) H14)) H13))))))) 
H9)) (\lambda (H9: (pr3 (CHead c (Bind b) v2) t (lift (S O) O (THead (Bind 
Abst) x0 x1)))).(pr3_t (THead (Bind b) v2 (THead (Flat Appl) (lift (S O) O 
x2) (lift (S O) O (THead (Bind Abst) x0 x1)))) (THead (Bind b) v2 (THead 
(Flat Appl) (lift (S O) O v1) t)) c (pr3_head_2 c v2 (THead (Flat Appl) (lift 
(S O) O v1) t) (THead (Flat Appl) (lift (S O) O x2) (lift (S O) O (THead 
(Bind Abst) x0 x1))) (Bind b) (pr3_flat (CHead c (Bind b) v2) (lift (S O) O 
v1) (lift (S O) O x2) (pr3_lift (CHead c (Bind b) v2) c (S O) O (drop_drop 
(Bind b) O c c (drop_refl c) v2) v1 x2 H5) t (lift (S O) O (THead (Bind Abst) 
x0 x1)) H9 Appl)) (THead (Bind Abbr) x2 x3) (eq_ind T (lift (S O) O (THead 
(Flat Appl) x2 (THead (Bind Abst) x0 x1))) (\lambda (t0: T).(pr3 c (THead 
(Bind b) v2 t0) (THead (Bind Abbr) x2 x3))) (pr3_sing c (THead (Bind Abbr) x2 
x1) (THead (Bind b) v2 (lift (S O) O (THead (Flat Appl) x2 (THead (Bind Abst) 
x0 x1)))) (pr2_free c (THead (Bind b) v2 (lift (S O) O (THead (Flat Appl) x2 
(THead (Bind Abst) x0 x1)))) (THead (Bind Abbr) x2 x1) (pr0_zeta b H (THead 
(Flat Appl) x2 (THead (Bind Abst) x0 x1)) (THead (Bind Abbr) x2 x1) (pr0_beta 
x0 x2 x2 (pr0_refl x2) x1 x1 (pr0_refl x1)) v2)) (THead (Bind Abbr) x2 x3) 
(pr3_head_12 c x2 x2 (pr3_refl c x2) (Bind Abbr) x1 x3 (H7 Abbr x2))) (THead 
(Flat Appl) (lift (S O) O x2) (lift (S O) O (THead (Bind Abst) x0 x1))) 
(lift_flat Appl x2 (THead (Bind Abst) x0 x1) (S O) O)))) H8))) u2 H4))))))))) 
H3)) (\lambda (H3: (ex6_6 B T T T T T (\lambda (b0: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B 
b0 Abst)))))))) (\lambda (b0: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(pr3 c (THead (Bind b) v2 t) (THead 
(Bind b0) y1 z1)))))))) (\lambda (b0: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (z2: T).(\lambda (u3: T).(\lambda (y2: T).(pr3 c (THead (Bind b0) 
y2 (THead (Flat Appl) (lift (S O) O u3) z2)) u2))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda 
(_: T).(pr3 c v1 u3))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr3 c y1 y2))))))) 
(\lambda (b0: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda 
(_: T).(\lambda (y2: T).(pr3 (CHead c (Bind b0) y2) z1 z2))))))))).(ex6_6_ind 
B T T T T T (\lambda (b0: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(not (eq B b0 Abst)))))))) (\lambda (b0: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(pr3 c (THead (Bind b) v2 t) (THead (Bind b0) y1 z1)))))))) (\lambda 
(b0: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u3: 
T).(\lambda (y2: T).(pr3 c (THead (Bind b0) y2 (THead (Flat Appl) (lift (S O) 
O u3) z2)) u2))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (u3: T).(\lambda (_: T).(pr3 c v1 u3))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr3 c y1 y2))))))) (\lambda (b0: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr3 (CHead c (Bind b0) 
y2) z1 z2))))))) (pr3 c (THead (Bind b) v2 (THead (Flat Appl) (lift (S O) O 
v1) t)) u2) (\lambda (x0: B).(\lambda (x1: T).(\lambda (x2: T).(\lambda (x3: 
T).(\lambda (x4: T).(\lambda (x5: T).(\lambda (H4: (not (eq B x0 
Abst))).(\lambda (H5: (pr3 c (THead (Bind b) v2 t) (THead (Bind x0) x1 
x2))).(\lambda (H6: (pr3 c (THead (Bind x0) x5 (THead (Flat Appl) (lift (S O) 
O x4) x3)) u2)).(\lambda (H7: (pr3 c v1 x4)).(\lambda (H8: (pr3 c x1 
x5)).(\lambda (H9: (pr3 (CHead c (Bind x0) x5) x2 x3)).(pr3_t (THead (Bind 
x0) x5 (THead (Flat Appl) (lift (S O) O x4) x3)) (THead (Bind b) v2 (THead 
(Flat Appl) (lift (S O) O v1) t)) c (let H_x \def (pr3_gen_bind b H c v2 t 
(THead (Bind x0) x1 x2) H5) in (let H10 \def H_x in (or_ind (ex3_2 T T 
(\lambda (u3: T).(\lambda (t2: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind 
b) u3 t2)))) (\lambda (u3: T).(\lambda (_: T).(pr3 c v2 u3))) (\lambda (_: 
T).(\lambda (t2: T).(pr3 (CHead c (Bind b) v2) t t2)))) (pr3 (CHead c (Bind 
b) v2) t (lift (S O) O (THead (Bind x0) x1 x2))) (pr3 c (THead (Bind b) v2 
(THead (Flat Appl) (lift (S O) O v1) t)) (THead (Bind x0) x5 (THead (Flat 
Appl) (lift (S O) O x4) x3))) (\lambda (H11: (ex3_2 T T (\lambda (u3: 
T).(\lambda (t2: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind b) u3 t2)))) 
(\lambda (u3: T).(\lambda (_: T).(pr3 c v2 u3))) (\lambda (_: T).(\lambda 
(t2: T).(pr3 (CHead c (Bind b) v2) t t2))))).(ex3_2_ind T T (\lambda (u3: 
T).(\lambda (t2: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind b) u3 t2)))) 
(\lambda (u3: T).(\lambda (_: T).(pr3 c v2 u3))) (\lambda (_: T).(\lambda 
(t2: T).(pr3 (CHead c (Bind b) v2) t t2))) (pr3 c (THead (Bind b) v2 (THead 
(Flat Appl) (lift (S O) O v1) t)) (THead (Bind x0) x5 (THead (Flat Appl) 
(lift (S O) O x4) x3))) (\lambda (x6: T).(\lambda (x7: T).(\lambda (H12: (eq 
T (THead (Bind x0) x1 x2) (THead (Bind b) x6 x7))).(\lambda (H13: (pr3 c v2 
x6)).(\lambda (H14: (pr3 (CHead c (Bind b) v2) t x7)).(let H15 \def (f_equal 
T B (\lambda (e: T).(match e in T return (\lambda (_: T).B) with [(TSort _) 
\Rightarrow x0 | (TLRef _) \Rightarrow x0 | (THead k _ _) \Rightarrow (match 
k in K return (\lambda (_: K).B) with [(Bind b0) \Rightarrow b0 | (Flat _) 
\Rightarrow x0])])) (THead (Bind x0) x1 x2) (THead (Bind b) x6 x7) H12) in 
((let H16 \def (f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: 
T).T) with [(TSort _) \Rightarrow x1 | (TLRef _) \Rightarrow x1 | (THead _ t0 
_) \Rightarrow t0])) (THead (Bind x0) x1 x2) (THead (Bind b) x6 x7) H12) in 
((let H17 \def (f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: 
T).T) with [(TSort _) \Rightarrow x2 | (TLRef _) \Rightarrow x2 | (THead _ _ 
t0) \Rightarrow t0])) (THead (Bind x0) x1 x2) (THead (Bind b) x6 x7) H12) in 
(\lambda (H18: (eq T x1 x6)).(\lambda (H19: (eq B x0 b)).(let H20 \def 
(eq_ind_r T x7 (\lambda (t0: T).(pr3 (CHead c (Bind b) v2) t t0)) H14 x2 H17) 
in (let H21 \def (eq_ind_r T x6 (\lambda (t0: T).(pr3 c v2 t0)) H13 x1 H18) 
in (let H22 \def (eq_ind B x0 (\lambda (b0: B).(pr3 (CHead c (Bind b0) x5) x2 
x3)) H9 b H19) in (let H23 \def (eq_ind B x0 (\lambda (b0: B).(not (eq B b0 
Abst))) H4 b H19) in (eq_ind_r B b (\lambda (b0: B).(pr3 c (THead (Bind b) v2 
(THead (Flat Appl) (lift (S O) O v1) t)) (THead (Bind b0) x5 (THead (Flat 
Appl) (lift (S O) O x4) x3)))) (pr3_head_21 c v2 x5 (pr3_t x1 v2 c H21 x5 H8) 
(Bind b) (THead (Flat Appl) (lift (S O) O v1) t) (THead (Flat Appl) (lift (S 
O) O x4) x3) (pr3_flat (CHead c (Bind b) v2) (lift (S O) O v1) (lift (S O) O 
x4) (pr3_lift (CHead c (Bind b) v2) c (S O) O (drop_drop (Bind b) O c c 
(drop_refl c) v2) v1 x4 H7) t x3 (pr3_t x2 t (CHead c (Bind b) v2) H20 x3 
(pr3_pr3_pr3_t c v2 x1 H21 x2 x3 (Bind b) (pr3_pr3_pr3_t c x1 x5 H8 x2 x3 
(Bind b) H22))) Appl)) x0 H19)))))))) H16)) H15))))))) H11)) (\lambda (H11: 
(pr3 (CHead c (Bind b) v2) t (lift (S O) O (THead (Bind x0) x1 x2)))).(pr3_t 
(THead (Bind b) v2 (THead (Flat Appl) (lift (S O) O x4) (lift (S O) O (THead 
(Bind x0) x1 x2)))) (THead (Bind b) v2 (THead (Flat Appl) (lift (S O) O v1) 
t)) c (pr3_head_2 c v2 (THead (Flat Appl) (lift (S O) O v1) t) (THead (Flat 
Appl) (lift (S O) O x4) (lift (S O) O (THead (Bind x0) x1 x2))) (Bind b) 
(pr3_flat (CHead c (Bind b) v2) (lift (S O) O v1) (lift (S O) O x4) (pr3_lift 
(CHead c (Bind b) v2) c (S O) O (drop_drop (Bind b) O c c (drop_refl c) v2) 
v1 x4 H7) t (lift (S O) O (THead (Bind x0) x1 x2)) H11 Appl)) (THead (Bind 
x0) x5 (THead (Flat Appl) (lift (S O) O x4) x3)) (eq_ind T (lift (S O) O 
(THead (Flat Appl) x4 (THead (Bind x0) x1 x2))) (\lambda (t0: T).(pr3 c 
(THead (Bind b) v2 t0) (THead (Bind x0) x5 (THead (Flat Appl) (lift (S O) O 
x4) x3)))) (pr3_sing c (THead (Bind x0) x1 (THead (Flat Appl) (lift (S O) O 
x4) x2)) (THead (Bind b) v2 (lift (S O) O (THead (Flat Appl) x4 (THead (Bind 
x0) x1 x2)))) (pr2_free c (THead (Bind b) v2 (lift (S O) O (THead (Flat Appl) 
x4 (THead (Bind x0) x1 x2)))) (THead (Bind x0) x1 (THead (Flat Appl) (lift (S 
O) O x4) x2)) (pr0_zeta b H (THead (Flat Appl) x4 (THead (Bind x0) x1 x2)) 
(THead (Bind x0) x1 (THead (Flat Appl) (lift (S O) O x4) x2)) (pr0_upsilon x0 
H4 x4 x4 (pr0_refl x4) x1 x1 (pr0_refl x1) x2 x2 (pr0_refl x2)) v2)) (THead 
(Bind x0) x5 (THead (Flat Appl) (lift (S O) O x4) x3)) (pr3_head_12 c x1 x5 
H8 (Bind x0) (THead (Flat Appl) (lift (S O) O x4) x2) (THead (Flat Appl) 
(lift (S O) O x4) x3) (pr3_thin_dx (CHead c (Bind x0) x5) x2 x3 H9 (lift (S 
O) O x4) Appl))) (THead (Flat Appl) (lift (S O) O x4) (lift (S O) O (THead 
(Bind x0) x1 x2))) (lift_flat Appl x4 (THead (Bind x0) x1 x2) (S O) O)))) 
H10))) u2 H6))))))))))))) H3)) H2)))))))))).
(* COMMENTS
Initial nodes: 4805
END *)

theorem pr3_iso_appls_appl_bind:
 \forall (b: B).((not (eq B b Abst)) \to (\forall (v: T).(\forall (u: 
T).(\forall (t: T).(\forall (vs: TList).(let u1 \def (THeads (Flat Appl) vs 
(THead (Flat Appl) v (THead (Bind b) u t))) in (\forall (c: C).(\forall (u2: 
T).((pr3 c u1 u2) \to ((((iso u1 u2) \to (\forall (P: Prop).P))) \to (pr3 c 
(THeads (Flat Appl) vs (THead (Bind b) u (THead (Flat Appl) (lift (S O) O v) 
t))) u2)))))))))))
\def
 \lambda (b: B).(\lambda (H: (not (eq B b Abst))).(\lambda (v: T).(\lambda 
(u: T).(\lambda (t: T).(\lambda (vs: TList).(TList_ind (\lambda (t0: 
TList).(let u1 \def (THeads (Flat Appl) t0 (THead (Flat Appl) v (THead (Bind 
b) u t))) in (\forall (c: C).(\forall (u2: T).((pr3 c u1 u2) \to ((((iso u1 
u2) \to (\forall (P: Prop).P))) \to (pr3 c (THeads (Flat Appl) t0 (THead 
(Bind b) u (THead (Flat Appl) (lift (S O) O v) t))) u2))))))) (\lambda (c: 
C).(\lambda (u2: T).(\lambda (H0: (pr3 c (THead (Flat Appl) v (THead (Bind b) 
u t)) u2)).(\lambda (H1: (((iso (THead (Flat Appl) v (THead (Bind b) u t)) 
u2) \to (\forall (P: Prop).P)))).(pr3_iso_appl_bind b H v u t c u2 H0 H1))))) 
(\lambda (t0: T).(\lambda (t1: TList).(\lambda (H0: ((\forall (c: C).(\forall 
(u2: T).((pr3 c (THeads (Flat Appl) t1 (THead (Flat Appl) v (THead (Bind b) u 
t))) u2) \to ((((iso (THeads (Flat Appl) t1 (THead (Flat Appl) v (THead (Bind 
b) u t))) u2) \to (\forall (P: Prop).P))) \to (pr3 c (THeads (Flat Appl) t1 
(THead (Bind b) u (THead (Flat Appl) (lift (S O) O v) t))) u2))))))).(\lambda 
(c: C).(\lambda (u2: T).(\lambda (H1: (pr3 c (THead (Flat Appl) t0 (THeads 
(Flat Appl) t1 (THead (Flat Appl) v (THead (Bind b) u t)))) u2)).(\lambda 
(H2: (((iso (THead (Flat Appl) t0 (THeads (Flat Appl) t1 (THead (Flat Appl) v 
(THead (Bind b) u t)))) u2) \to (\forall (P: Prop).P)))).(let H3 \def 
(pr3_gen_appl c t0 (THeads (Flat Appl) t1 (THead (Flat Appl) v (THead (Bind 
b) u t))) u2 H1) in (or3_ind (ex3_2 T T (\lambda (u3: T).(\lambda (t2: T).(eq 
T u2 (THead (Flat Appl) u3 t2)))) (\lambda (u3: T).(\lambda (_: T).(pr3 c t0 
u3))) (\lambda (_: T).(\lambda (t2: T).(pr3 c (THeads (Flat Appl) t1 (THead 
(Flat Appl) v (THead (Bind b) u t))) t2)))) (ex4_4 T T T T (\lambda (_: 
T).(\lambda (_: T).(\lambda (u3: T).(\lambda (t2: T).(pr3 c (THead (Bind 
Abbr) u3 t2) u2))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u3: 
T).(\lambda (_: T).(pr3 c t0 u3))))) (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(pr3 c (THeads (Flat Appl) t1 (THead (Flat 
Appl) v (THead (Bind b) u t))) (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t2: T).(\forall (b0: 
B).(\forall (u0: T).(pr3 (CHead c (Bind b0) u0) z1 t2)))))))) (ex6_6 B T T T 
T T (\lambda (b0: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(not (eq B b0 Abst)))))))) (\lambda (b0: B).(\lambda 
(y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(pr3 
c (THeads (Flat Appl) t1 (THead (Flat Appl) v (THead (Bind b) u t))) (THead 
(Bind b0) y1 z1)))))))) (\lambda (b0: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (z2: T).(\lambda (u3: T).(\lambda (y2: T).(pr3 c (THead (Bind b0) 
y2 (THead (Flat Appl) (lift (S O) O u3) z2)) u2))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda 
(_: T).(pr3 c t0 u3))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr3 c y1 y2))))))) 
(\lambda (b0: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda 
(_: T).(\lambda (y2: T).(pr3 (CHead c (Bind b0) y2) z1 z2)))))))) (pr3 c 
(THead (Flat Appl) t0 (THeads (Flat Appl) t1 (THead (Bind b) u (THead (Flat 
Appl) (lift (S O) O v) t)))) u2) (\lambda (H4: (ex3_2 T T (\lambda (u3: 
T).(\lambda (t2: T).(eq T u2 (THead (Flat Appl) u3 t2)))) (\lambda (u3: 
T).(\lambda (_: T).(pr3 c t0 u3))) (\lambda (_: T).(\lambda (t2: T).(pr3 c 
(THeads (Flat Appl) t1 (THead (Flat Appl) v (THead (Bind b) u t))) 
t2))))).(ex3_2_ind T T (\lambda (u3: T).(\lambda (t2: T).(eq T u2 (THead 
(Flat Appl) u3 t2)))) (\lambda (u3: T).(\lambda (_: T).(pr3 c t0 u3))) 
(\lambda (_: T).(\lambda (t2: T).(pr3 c (THeads (Flat Appl) t1 (THead (Flat 
Appl) v (THead (Bind b) u t))) t2))) (pr3 c (THead (Flat Appl) t0 (THeads 
(Flat Appl) t1 (THead (Bind b) u (THead (Flat Appl) (lift (S O) O v) t)))) 
u2) (\lambda (x0: T).(\lambda (x1: T).(\lambda (H5: (eq T u2 (THead (Flat 
Appl) x0 x1))).(\lambda (_: (pr3 c t0 x0)).(\lambda (_: (pr3 c (THeads (Flat 
Appl) t1 (THead (Flat Appl) v (THead (Bind b) u t))) x1)).(let H8 \def 
(eq_ind T u2 (\lambda (t2: T).((iso (THead (Flat Appl) t0 (THeads (Flat Appl) 
t1 (THead (Flat Appl) v (THead (Bind b) u t)))) t2) \to (\forall (P: 
Prop).P))) H2 (THead (Flat Appl) x0 x1) H5) in (eq_ind_r T (THead (Flat Appl) 
x0 x1) (\lambda (t2: T).(pr3 c (THead (Flat Appl) t0 (THeads (Flat Appl) t1 
(THead (Bind b) u (THead (Flat Appl) (lift (S O) O v) t)))) t2)) (H8 
(iso_head t0 x0 (THeads (Flat Appl) t1 (THead (Flat Appl) v (THead (Bind b) u 
t))) x1 (Flat Appl)) (pr3 c (THead (Flat Appl) t0 (THeads (Flat Appl) t1 
(THead (Bind b) u (THead (Flat Appl) (lift (S O) O v) t)))) (THead (Flat 
Appl) x0 x1))) u2 H5))))))) H4)) (\lambda (H4: (ex4_4 T T T T (\lambda (_: 
T).(\lambda (_: T).(\lambda (u3: T).(\lambda (t2: T).(pr3 c (THead (Bind 
Abbr) u3 t2) u2))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u3: 
T).(\lambda (_: T).(pr3 c t0 u3))))) (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(pr3 c (THeads (Flat Appl) t1 (THead (Flat 
Appl) v (THead (Bind b) u t))) (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t2: T).(\forall (b0: 
B).(\forall (u0: T).(pr3 (CHead c (Bind b0) u0) z1 t2))))))))).(ex4_4_ind T T 
T T (\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda (t2: T).(pr3 c 
(THead (Bind Abbr) u3 t2) u2))))) (\lambda (_: T).(\lambda (_: T).(\lambda 
(u3: T).(\lambda (_: T).(pr3 c t0 u3))))) (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(pr3 c (THeads (Flat Appl) t1 (THead (Flat 
Appl) v (THead (Bind b) u t))) (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t2: T).(\forall (b0: 
B).(\forall (u0: T).(pr3 (CHead c (Bind b0) u0) z1 t2))))))) (pr3 c (THead 
(Flat Appl) t0 (THeads (Flat Appl) t1 (THead (Bind b) u (THead (Flat Appl) 
(lift (S O) O v) t)))) u2) (\lambda (x0: T).(\lambda (x1: T).(\lambda (x2: 
T).(\lambda (x3: T).(\lambda (H5: (pr3 c (THead (Bind Abbr) x2 x3) 
u2)).(\lambda (H6: (pr3 c t0 x2)).(\lambda (H7: (pr3 c (THeads (Flat Appl) t1 
(THead (Flat Appl) v (THead (Bind b) u t))) (THead (Bind Abst) x0 
x1))).(\lambda (H8: ((\forall (b0: B).(\forall (u0: T).(pr3 (CHead c (Bind 
b0) u0) x1 x3))))).(pr3_t (THead (Bind Abbr) t0 x1) (THead (Flat Appl) t0 
(THeads (Flat Appl) t1 (THead (Bind b) u (THead (Flat Appl) (lift (S O) O v) 
t)))) c (pr3_t (THead (Flat Appl) t0 (THead (Bind Abst) x0 x1)) (THead (Flat 
Appl) t0 (THeads (Flat Appl) t1 (THead (Bind b) u (THead (Flat Appl) (lift (S 
O) O v) t)))) c (pr3_thin_dx c (THeads (Flat Appl) t1 (THead (Bind b) u 
(THead (Flat Appl) (lift (S O) O v) t))) (THead (Bind Abst) x0 x1) (H0 c 
(THead (Bind Abst) x0 x1) H7 (\lambda (H9: (iso (THeads (Flat Appl) t1 (THead 
(Flat Appl) v (THead (Bind b) u t))) (THead (Bind Abst) x0 x1))).(\lambda (P: 
Prop).(iso_flats_flat_bind_false Appl Appl Abst x0 v x1 (THead (Bind b) u t) 
t1 H9 P)))) t0 Appl) (THead (Bind Abbr) t0 x1) (pr3_pr2 c (THead (Flat Appl) 
t0 (THead (Bind Abst) x0 x1)) (THead (Bind Abbr) t0 x1) (pr2_free c (THead 
(Flat Appl) t0 (THead (Bind Abst) x0 x1)) (THead (Bind Abbr) t0 x1) (pr0_beta 
x0 t0 t0 (pr0_refl t0) x1 x1 (pr0_refl x1))))) u2 (pr3_t (THead (Bind Abbr) 
x2 x3) (THead (Bind Abbr) t0 x1) c (pr3_head_12 c t0 x2 H6 (Bind Abbr) x1 x3 
(H8 Abbr x2)) u2 H5)))))))))) H4)) (\lambda (H4: (ex6_6 B T T T T T (\lambda 
(b0: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b0 Abst)))))))) (\lambda (b0: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(pr3 c 
(THeads (Flat Appl) t1 (THead (Flat Appl) v (THead (Bind b) u t))) (THead 
(Bind b0) y1 z1)))))))) (\lambda (b0: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (z2: T).(\lambda (u3: T).(\lambda (y2: T).(pr3 c (THead (Bind b0) 
y2 (THead (Flat Appl) (lift (S O) O u3) z2)) u2))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda 
(_: T).(pr3 c t0 u3))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr3 c y1 y2))))))) 
(\lambda (b0: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda 
(_: T).(\lambda (y2: T).(pr3 (CHead c (Bind b0) y2) z1 z2))))))))).(ex6_6_ind 
B T T T T T (\lambda (b0: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(not (eq B b0 Abst)))))))) (\lambda (b0: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(pr3 c (THeads (Flat Appl) t1 (THead (Flat Appl) v (THead (Bind b) u 
t))) (THead (Bind b0) y1 z1)))))))) (\lambda (b0: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (z2: T).(\lambda (u3: T).(\lambda (y2: T).(pr3 c (THead (Bind 
b0) y2 (THead (Flat Appl) (lift (S O) O u3) z2)) u2))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda 
(_: T).(pr3 c t0 u3))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr3 c y1 y2))))))) 
(\lambda (b0: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda 
(_: T).(\lambda (y2: T).(pr3 (CHead c (Bind b0) y2) z1 z2))))))) (pr3 c 
(THead (Flat Appl) t0 (THeads (Flat Appl) t1 (THead (Bind b) u (THead (Flat 
Appl) (lift (S O) O v) t)))) u2) (\lambda (x0: B).(\lambda (x1: T).(\lambda 
(x2: T).(\lambda (x3: T).(\lambda (x4: T).(\lambda (x5: T).(\lambda (H5: (not 
(eq B x0 Abst))).(\lambda (H6: (pr3 c (THeads (Flat Appl) t1 (THead (Flat 
Appl) v (THead (Bind b) u t))) (THead (Bind x0) x1 x2))).(\lambda (H7: (pr3 c 
(THead (Bind x0) x5 (THead (Flat Appl) (lift (S O) O x4) x3)) u2)).(\lambda 
(H8: (pr3 c t0 x4)).(\lambda (H9: (pr3 c x1 x5)).(\lambda (H10: (pr3 (CHead c 
(Bind x0) x5) x2 x3)).(pr3_t (THead (Bind x0) x1 (THead (Flat Appl) (lift (S 
O) O x4) x2)) (THead (Flat Appl) t0 (THeads (Flat Appl) t1 (THead (Bind b) u 
(THead (Flat Appl) (lift (S O) O v) t)))) c (pr3_t (THead (Bind x0) x1 (THead 
(Flat Appl) (lift (S O) O t0) x2)) (THead (Flat Appl) t0 (THeads (Flat Appl) 
t1 (THead (Bind b) u (THead (Flat Appl) (lift (S O) O v) t)))) c (pr3_t 
(THead (Flat Appl) t0 (THead (Bind x0) x1 x2)) (THead (Flat Appl) t0 (THeads 
(Flat Appl) t1 (THead (Bind b) u (THead (Flat Appl) (lift (S O) O v) t)))) c 
(pr3_thin_dx c (THeads (Flat Appl) t1 (THead (Bind b) u (THead (Flat Appl) 
(lift (S O) O v) t))) (THead (Bind x0) x1 x2) (H0 c (THead (Bind x0) x1 x2) 
H6 (\lambda (H11: (iso (THeads (Flat Appl) t1 (THead (Flat Appl) v (THead 
(Bind b) u t))) (THead (Bind x0) x1 x2))).(\lambda (P: 
Prop).(iso_flats_flat_bind_false Appl Appl x0 x1 v x2 (THead (Bind b) u t) t1 
H11 P)))) t0 Appl) (THead (Bind x0) x1 (THead (Flat Appl) (lift (S O) O t0) 
x2)) (pr3_pr2 c (THead (Flat Appl) t0 (THead (Bind x0) x1 x2)) (THead (Bind 
x0) x1 (THead (Flat Appl) (lift (S O) O t0) x2)) (pr2_free c (THead (Flat 
Appl) t0 (THead (Bind x0) x1 x2)) (THead (Bind x0) x1 (THead (Flat Appl) 
(lift (S O) O t0) x2)) (pr0_upsilon x0 H5 t0 t0 (pr0_refl t0) x1 x1 (pr0_refl 
x1) x2 x2 (pr0_refl x2))))) (THead (Bind x0) x1 (THead (Flat Appl) (lift (S 
O) O x4) x2)) (pr3_head_12 c x1 x1 (pr3_refl c x1) (Bind x0) (THead (Flat 
Appl) (lift (S O) O t0) x2) (THead (Flat Appl) (lift (S O) O x4) x2) 
(pr3_head_12 (CHead c (Bind x0) x1) (lift (S O) O t0) (lift (S O) O x4) 
(pr3_lift (CHead c (Bind x0) x1) c (S O) O (drop_drop (Bind x0) O c c 
(drop_refl c) x1) t0 x4 H8) (Flat Appl) x2 x2 (pr3_refl (CHead (CHead c (Bind 
x0) x1) (Flat Appl) (lift (S O) O x4)) x2)))) u2 (pr3_t (THead (Bind x0) x5 
(THead (Flat Appl) (lift (S O) O x4) x3)) (THead (Bind x0) x1 (THead (Flat 
Appl) (lift (S O) O x4) x2)) c (pr3_head_12 c x1 x5 H9 (Bind x0) (THead (Flat 
Appl) (lift (S O) O x4) x2) (THead (Flat Appl) (lift (S O) O x4) x3) 
(pr3_thin_dx (CHead c (Bind x0) x5) x2 x3 H10 (lift (S O) O x4) Appl)) u2 
H7)))))))))))))) H4)) H3))))))))) vs)))))).
(* COMMENTS
Initial nodes: 3571
END *)

theorem pr3_iso_appls_bind:
 \forall (b: B).((not (eq B b Abst)) \to (\forall (vs: TList).(\forall (u: 
T).(\forall (t: T).(let u1 \def (THeads (Flat Appl) vs (THead (Bind b) u t)) 
in (\forall (c: C).(\forall (u2: T).((pr3 c u1 u2) \to ((((iso u1 u2) \to 
(\forall (P: Prop).P))) \to (pr3 c (THead (Bind b) u (THeads (Flat Appl) 
(lifts (S O) O vs) t)) u2))))))))))
\def
 \lambda (b: B).(\lambda (H: (not (eq B b Abst))).(\lambda (vs: 
TList).(tlist_ind_rev (\lambda (t: TList).(\forall (u: T).(\forall (t0: 
T).(let u1 \def (THeads (Flat Appl) t (THead (Bind b) u t0)) in (\forall (c: 
C).(\forall (u2: T).((pr3 c u1 u2) \to ((((iso u1 u2) \to (\forall (P: 
Prop).P))) \to (pr3 c (THead (Bind b) u (THeads (Flat Appl) (lifts (S O) O t) 
t0)) u2))))))))) (\lambda (u: T).(\lambda (t: T).(\lambda (c: C).(\lambda 
(u2: T).(\lambda (H0: (pr3 c (THead (Bind b) u t) u2)).(\lambda (_: (((iso 
(THead (Bind b) u t) u2) \to (\forall (P: Prop).P)))).H0)))))) (\lambda (ts: 
TList).(\lambda (t: T).(\lambda (H0: ((\forall (u: T).(\forall (t0: 
T).(\forall (c: C).(\forall (u2: T).((pr3 c (THeads (Flat Appl) ts (THead 
(Bind b) u t0)) u2) \to ((((iso (THeads (Flat Appl) ts (THead (Bind b) u t0)) 
u2) \to (\forall (P: Prop).P))) \to (pr3 c (THead (Bind b) u (THeads (Flat 
Appl) (lifts (S O) O ts) t0)) u2))))))))).(\lambda (u: T).(\lambda (t0: 
T).(\lambda (c: C).(\lambda (u2: T).(\lambda (H1: (pr3 c (THeads (Flat Appl) 
(TApp ts t) (THead (Bind b) u t0)) u2)).(\lambda (H2: (((iso (THeads (Flat 
Appl) (TApp ts t) (THead (Bind b) u t0)) u2) \to (\forall (P: 
Prop).P)))).(eq_ind_r TList (TApp (lifts (S O) O ts) (lift (S O) O t)) 
(\lambda (t1: TList).(pr3 c (THead (Bind b) u (THeads (Flat Appl) t1 t0)) 
u2)) (eq_ind_r T (THeads (Flat Appl) (lifts (S O) O ts) (THead (Flat Appl) 
(lift (S O) O t) t0)) (\lambda (t1: T).(pr3 c (THead (Bind b) u t1) u2)) (let 
H3 \def (eq_ind T (THeads (Flat Appl) (TApp ts t) (THead (Bind b) u t0)) 
(\lambda (t1: T).(pr3 c t1 u2)) H1 (THeads (Flat Appl) ts (THead (Flat Appl) 
t (THead (Bind b) u t0))) (theads_tapp (Flat Appl) t (THead (Bind b) u t0) 
ts)) in (let H4 \def (eq_ind T (THeads (Flat Appl) (TApp ts t) (THead (Bind 
b) u t0)) (\lambda (t1: T).((iso t1 u2) \to (\forall (P: Prop).P))) H2 
(THeads (Flat Appl) ts (THead (Flat Appl) t (THead (Bind b) u t0))) 
(theads_tapp (Flat Appl) t (THead (Bind b) u t0) ts)) in (TList_ind (\lambda 
(t1: TList).(((\forall (u0: T).(\forall (t2: T).(\forall (c0: C).(\forall 
(u3: T).((pr3 c0 (THeads (Flat Appl) t1 (THead (Bind b) u0 t2)) u3) \to 
((((iso (THeads (Flat Appl) t1 (THead (Bind b) u0 t2)) u3) \to (\forall (P: 
Prop).P))) \to (pr3 c0 (THead (Bind b) u0 (THeads (Flat Appl) (lifts (S O) O 
t1) t2)) u3)))))))) \to ((pr3 c (THeads (Flat Appl) t1 (THead (Flat Appl) t 
(THead (Bind b) u t0))) u2) \to ((((iso (THeads (Flat Appl) t1 (THead (Flat 
Appl) t (THead (Bind b) u t0))) u2) \to (\forall (P: Prop).P))) \to (pr3 c 
(THead (Bind b) u (THeads (Flat Appl) (lifts (S O) O t1) (THead (Flat Appl) 
(lift (S O) O t) t0))) u2))))) (\lambda (_: ((\forall (u0: T).(\forall (t1: 
T).(\forall (c0: C).(\forall (u3: T).((pr3 c0 (THeads (Flat Appl) TNil (THead 
(Bind b) u0 t1)) u3) \to ((((iso (THeads (Flat Appl) TNil (THead (Bind b) u0 
t1)) u3) \to (\forall (P: Prop).P))) \to (pr3 c0 (THead (Bind b) u0 (THeads 
(Flat Appl) (lifts (S O) O TNil) t1)) u3))))))))).(\lambda (H6: (pr3 c 
(THeads (Flat Appl) TNil (THead (Flat Appl) t (THead (Bind b) u t0))) 
u2)).(\lambda (H7: (((iso (THeads (Flat Appl) TNil (THead (Flat Appl) t 
(THead (Bind b) u t0))) u2) \to (\forall (P: Prop).P)))).(pr3_iso_appl_bind b 
H t u t0 c u2 H6 H7)))) (\lambda (t1: T).(\lambda (ts0: TList).(\lambda (_: 
((((\forall (u0: T).(\forall (t2: T).(\forall (c0: C).(\forall (u3: T).((pr3 
c0 (THeads (Flat Appl) ts0 (THead (Bind b) u0 t2)) u3) \to ((((iso (THeads 
(Flat Appl) ts0 (THead (Bind b) u0 t2)) u3) \to (\forall (P: Prop).P))) \to 
(pr3 c0 (THead (Bind b) u0 (THeads (Flat Appl) (lifts (S O) O ts0) t2)) 
u3)))))))) \to ((pr3 c (THeads (Flat Appl) ts0 (THead (Flat Appl) t (THead 
(Bind b) u t0))) u2) \to ((((iso (THeads (Flat Appl) ts0 (THead (Flat Appl) t 
(THead (Bind b) u t0))) u2) \to (\forall (P: Prop).P))) \to (pr3 c (THead 
(Bind b) u (THeads (Flat Appl) (lifts (S O) O ts0) (THead (Flat Appl) (lift 
(S O) O t) t0))) u2)))))).(\lambda (H5: ((\forall (u0: T).(\forall (t2: 
T).(\forall (c0: C).(\forall (u3: T).((pr3 c0 (THeads (Flat Appl) (TCons t1 
ts0) (THead (Bind b) u0 t2)) u3) \to ((((iso (THeads (Flat Appl) (TCons t1 
ts0) (THead (Bind b) u0 t2)) u3) \to (\forall (P: Prop).P))) \to (pr3 c0 
(THead (Bind b) u0 (THeads (Flat Appl) (lifts (S O) O (TCons t1 ts0)) t2)) 
u3))))))))).(\lambda (H6: (pr3 c (THeads (Flat Appl) (TCons t1 ts0) (THead 
(Flat Appl) t (THead (Bind b) u t0))) u2)).(\lambda (H7: (((iso (THeads (Flat 
Appl) (TCons t1 ts0) (THead (Flat Appl) t (THead (Bind b) u t0))) u2) \to 
(\forall (P: Prop).P)))).(H5 u (THead (Flat Appl) (lift (S O) O t) t0) c u2 
(pr3_iso_appls_appl_bind b H t u t0 (TCons t1 ts0) c u2 H6 H7) (\lambda (H8: 
(iso (THeads (Flat Appl) (TCons t1 ts0) (THead (Bind b) u (THead (Flat Appl) 
(lift (S O) O t) t0))) u2)).(\lambda (P: Prop).(H7 (iso_trans (THeads (Flat 
Appl) (TCons t1 ts0) (THead (Flat Appl) t (THead (Bind b) u t0))) (THeads 
(Flat Appl) (TCons t1 ts0) (THead (Bind b) u (THead (Flat Appl) (lift (S O) O 
t) t0))) (iso_head t1 t1 (THeads (Flat Appl) ts0 (THead (Flat Appl) t (THead 
(Bind b) u t0))) (THeads (Flat Appl) ts0 (THead (Bind b) u (THead (Flat Appl) 
(lift (S O) O t) t0))) (Flat Appl)) u2 H8) P)))))))))) ts H0 H3 H4))) (THeads 
(Flat Appl) (TApp (lifts (S O) O ts) (lift (S O) O t)) t0) (theads_tapp (Flat 
Appl) (lift (S O) O t) t0 (lifts (S O) O ts))) (lifts (S O) O (TApp ts t)) 
(lifts_tapp (S O) O t ts))))))))))) vs))).
(* COMMENTS
Initial nodes: 1681
END *)

theorem pr3_iso_beta:
 \forall (v: T).(\forall (w: T).(\forall (t: T).(let u1 \def (THead (Flat 
Appl) v (THead (Bind Abst) w t)) in (\forall (c: C).(\forall (u2: T).((pr3 c 
u1 u2) \to ((((iso u1 u2) \to (\forall (P: Prop).P))) \to (pr3 c (THead (Bind 
Abbr) v t) u2))))))))
\def
 \lambda (v: T).(\lambda (w: T).(\lambda (t: T).(\lambda (c: C).(\lambda (u2: 
T).(\lambda (H: (pr3 c (THead (Flat Appl) v (THead (Bind Abst) w t)) 
u2)).(\lambda (H0: (((iso (THead (Flat Appl) v (THead (Bind Abst) w t)) u2) 
\to (\forall (P: Prop).P)))).(let H1 \def (pr3_gen_appl c v (THead (Bind 
Abst) w t) u2 H) in (or3_ind (ex3_2 T T (\lambda (u3: T).(\lambda (t2: T).(eq 
T u2 (THead (Flat Appl) u3 t2)))) (\lambda (u3: T).(\lambda (_: T).(pr3 c v 
u3))) (\lambda (_: T).(\lambda (t2: T).(pr3 c (THead (Bind Abst) w t) t2)))) 
(ex4_4 T T T T (\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda (t2: 
T).(pr3 c (THead (Bind Abbr) u3 t2) u2))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u3: T).(\lambda (_: T).(pr3 c v u3))))) (\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(pr3 c (THead (Bind Abst) 
w t) (THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (z1: T).(\lambda 
(_: T).(\lambda (t2: T).(\forall (b: B).(\forall (u: T).(pr3 (CHead c (Bind 
b) u) z1 t2)))))))) (ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B 
b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(pr3 c (THead (Bind Abst) w t) (THead 
(Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (z2: T).(\lambda (u3: T).(\lambda (y2: T).(pr3 c (THead (Bind b) 
y2 (THead (Flat Appl) (lift (S O) O u3) z2)) u2))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda 
(_: T).(pr3 c v u3))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr3 c y1 y2))))))) 
(\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda 
(_: T).(\lambda (y2: T).(pr3 (CHead c (Bind b) y2) z1 z2)))))))) (pr3 c 
(THead (Bind Abbr) v t) u2) (\lambda (H2: (ex3_2 T T (\lambda (u3: 
T).(\lambda (t2: T).(eq T u2 (THead (Flat Appl) u3 t2)))) (\lambda (u3: 
T).(\lambda (_: T).(pr3 c v u3))) (\lambda (_: T).(\lambda (t2: T).(pr3 c 
(THead (Bind Abst) w t) t2))))).(ex3_2_ind T T (\lambda (u3: T).(\lambda (t2: 
T).(eq T u2 (THead (Flat Appl) u3 t2)))) (\lambda (u3: T).(\lambda (_: 
T).(pr3 c v u3))) (\lambda (_: T).(\lambda (t2: T).(pr3 c (THead (Bind Abst) 
w t) t2))) (pr3 c (THead (Bind Abbr) v t) u2) (\lambda (x0: T).(\lambda (x1: 
T).(\lambda (H3: (eq T u2 (THead (Flat Appl) x0 x1))).(\lambda (_: (pr3 c v 
x0)).(\lambda (_: (pr3 c (THead (Bind Abst) w t) x1)).(let H6 \def (eq_ind T 
u2 (\lambda (t0: T).((iso (THead (Flat Appl) v (THead (Bind Abst) w t)) t0) 
\to (\forall (P: Prop).P))) H0 (THead (Flat Appl) x0 x1) H3) in (eq_ind_r T 
(THead (Flat Appl) x0 x1) (\lambda (t0: T).(pr3 c (THead (Bind Abbr) v t) 
t0)) (H6 (iso_head v x0 (THead (Bind Abst) w t) x1 (Flat Appl)) (pr3 c (THead 
(Bind Abbr) v t) (THead (Flat Appl) x0 x1))) u2 H3))))))) H2)) (\lambda (H2: 
(ex4_4 T T T T (\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda (t2: 
T).(pr3 c (THead (Bind Abbr) u3 t2) u2))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u3: T).(\lambda (_: T).(pr3 c v u3))))) (\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(pr3 c (THead (Bind Abst) 
w t) (THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (z1: T).(\lambda 
(_: T).(\lambda (t2: T).(\forall (b: B).(\forall (u: T).(pr3 (CHead c (Bind 
b) u) z1 t2))))))))).(ex4_4_ind T T T T (\lambda (_: T).(\lambda (_: 
T).(\lambda (u3: T).(\lambda (t2: T).(pr3 c (THead (Bind Abbr) u3 t2) u2))))) 
(\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda (_: T).(pr3 c v 
u3))))) (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: 
T).(pr3 c (THead (Bind Abst) w t) (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t2: T).(\forall (b: B).(\forall 
(u: T).(pr3 (CHead c (Bind b) u) z1 t2))))))) (pr3 c (THead (Bind Abbr) v t) 
u2) (\lambda (x0: T).(\lambda (x1: T).(\lambda (x2: T).(\lambda (x3: 
T).(\lambda (H3: (pr3 c (THead (Bind Abbr) x2 x3) u2)).(\lambda (H4: (pr3 c v 
x2)).(\lambda (H5: (pr3 c (THead (Bind Abst) w t) (THead (Bind Abst) x0 
x1))).(\lambda (H6: ((\forall (b: B).(\forall (u: T).(pr3 (CHead c (Bind b) 
u) x1 x3))))).(let H7 \def (pr3_gen_abst c w t (THead (Bind Abst) x0 x1) H5) 
in (ex3_2_ind T T (\lambda (u3: T).(\lambda (t2: T).(eq T (THead (Bind Abst) 
x0 x1) (THead (Bind Abst) u3 t2)))) (\lambda (u3: T).(\lambda (_: T).(pr3 c w 
u3))) (\lambda (_: T).(\lambda (t2: T).(\forall (b: B).(\forall (u: T).(pr3 
(CHead c (Bind b) u) t t2))))) (pr3 c (THead (Bind Abbr) v t) u2) (\lambda 
(x4: T).(\lambda (x5: T).(\lambda (H8: (eq T (THead (Bind Abst) x0 x1) (THead 
(Bind Abst) x4 x5))).(\lambda (H9: (pr3 c w x4)).(\lambda (H10: ((\forall (b: 
B).(\forall (u: T).(pr3 (CHead c (Bind b) u) t x5))))).(let H11 \def (f_equal 
T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) with [(TSort _) 
\Rightarrow x0 | (TLRef _) \Rightarrow x0 | (THead _ t0 _) \Rightarrow t0])) 
(THead (Bind Abst) x0 x1) (THead (Bind Abst) x4 x5) H8) in ((let H12 \def 
(f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) with 
[(TSort _) \Rightarrow x1 | (TLRef _) \Rightarrow x1 | (THead _ _ t0) 
\Rightarrow t0])) (THead (Bind Abst) x0 x1) (THead (Bind Abst) x4 x5) H8) in 
(\lambda (H13: (eq T x0 x4)).(let H14 \def (eq_ind_r T x5 (\lambda (t0: 
T).(\forall (b: B).(\forall (u: T).(pr3 (CHead c (Bind b) u) t t0)))) H10 x1 
H12) in (let H15 \def (eq_ind_r T x4 (\lambda (t0: T).(pr3 c w t0)) H9 x0 
H13) in (pr3_t (THead (Bind Abbr) x2 x3) (THead (Bind Abbr) v t) c 
(pr3_head_12 c v x2 H4 (Bind Abbr) t x3 (pr3_t x1 t (CHead c (Bind Abbr) x2) 
(H14 Abbr x2) x3 (H6 Abbr x2))) u2 H3))))) H11))))))) H7)))))))))) H2)) 
(\lambda (H2: (ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) 
(\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(pr3 c (THead (Bind Abst) w t) (THead (Bind b) y1 
z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: 
T).(\lambda (u3: T).(\lambda (y2: T).(pr3 c (THead (Bind b) y2 (THead (Flat 
Appl) (lift (S O) O u3) z2)) u2))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda (_: T).(pr3 c v 
u3))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr3 c y1 y2))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr3 (CHead c (Bind b) y2) z1 z2))))))))).(ex6_6_ind B T T T T T 
(\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(pr3 c 
(THead (Bind Abst) w t) (THead (Bind b) y1 z1)))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u3: T).(\lambda 
(y2: T).(pr3 c (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u3) z2)) 
u2))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u3: T).(\lambda (_: T).(pr3 c v u3))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr3 c y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr3 (CHead c (Bind b) 
y2) z1 z2))))))) (pr3 c (THead (Bind Abbr) v t) u2) (\lambda (x0: B).(\lambda 
(x1: T).(\lambda (x2: T).(\lambda (x3: T).(\lambda (x4: T).(\lambda (x5: 
T).(\lambda (H3: (not (eq B x0 Abst))).(\lambda (H4: (pr3 c (THead (Bind 
Abst) w t) (THead (Bind x0) x1 x2))).(\lambda (H5: (pr3 c (THead (Bind x0) x5 
(THead (Flat Appl) (lift (S O) O x4) x3)) u2)).(\lambda (_: (pr3 c v 
x4)).(\lambda (_: (pr3 c x1 x5)).(\lambda (H8: (pr3 (CHead c (Bind x0) x5) x2 
x3)).(let H9 \def (pr3_gen_abst c w t (THead (Bind x0) x1 x2) H4) in 
(ex3_2_ind T T (\lambda (u3: T).(\lambda (t2: T).(eq T (THead (Bind x0) x1 
x2) (THead (Bind Abst) u3 t2)))) (\lambda (u3: T).(\lambda (_: T).(pr3 c w 
u3))) (\lambda (_: T).(\lambda (t2: T).(\forall (b: B).(\forall (u: T).(pr3 
(CHead c (Bind b) u) t t2))))) (pr3 c (THead (Bind Abbr) v t) u2) (\lambda 
(x6: T).(\lambda (x7: T).(\lambda (H10: (eq T (THead (Bind x0) x1 x2) (THead 
(Bind Abst) x6 x7))).(\lambda (H11: (pr3 c w x6)).(\lambda (H12: ((\forall 
(b: B).(\forall (u: T).(pr3 (CHead c (Bind b) u) t x7))))).(let H13 \def 
(f_equal T B (\lambda (e: T).(match e in T return (\lambda (_: T).B) with 
[(TSort _) \Rightarrow x0 | (TLRef _) \Rightarrow x0 | (THead k _ _) 
\Rightarrow (match k in K return (\lambda (_: K).B) with [(Bind b) 
\Rightarrow b | (Flat _) \Rightarrow x0])])) (THead (Bind x0) x1 x2) (THead 
(Bind Abst) x6 x7) H10) in ((let H14 \def (f_equal T T (\lambda (e: T).(match 
e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow x1 | (TLRef _) 
\Rightarrow x1 | (THead _ t0 _) \Rightarrow t0])) (THead (Bind x0) x1 x2) 
(THead (Bind Abst) x6 x7) H10) in ((let H15 \def (f_equal T T (\lambda (e: 
T).(match e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow x2 | 
(TLRef _) \Rightarrow x2 | (THead _ _ t0) \Rightarrow t0])) (THead (Bind x0) 
x1 x2) (THead (Bind Abst) x6 x7) H10) in (\lambda (H16: (eq T x1 
x6)).(\lambda (H17: (eq B x0 Abst)).(let H18 \def (eq_ind_r T x7 (\lambda 
(t0: T).(\forall (b: B).(\forall (u: T).(pr3 (CHead c (Bind b) u) t t0)))) 
H12 x2 H15) in (let H19 \def (eq_ind_r T x6 (\lambda (t0: T).(pr3 c w t0)) 
H11 x1 H16) in (let H20 \def (eq_ind B x0 (\lambda (b: B).(pr3 (CHead c (Bind 
b) x5) x2 x3)) H8 Abst H17) in (let H21 \def (eq_ind B x0 (\lambda (b: 
B).(pr3 c (THead (Bind b) x5 (THead (Flat Appl) (lift (S O) O x4) x3)) u2)) 
H5 Abst H17) in (let H22 \def (eq_ind B x0 (\lambda (b: B).(not (eq B b 
Abst))) H3 Abst H17) in (let H23 \def (match (H22 (refl_equal B Abst)) in 
False return (\lambda (_: False).(pr3 c (THead (Bind Abbr) v t) u2)) with []) 
in H23))))))))) H14)) H13))))))) H9)))))))))))))) H2)) H1)))))))).
(* COMMENTS
Initial nodes: 2459
END *)

theorem pr3_iso_appls_beta:
 \forall (us: TList).(\forall (v: T).(\forall (w: T).(\forall (t: T).(let u1 
\def (THeads (Flat Appl) us (THead (Flat Appl) v (THead (Bind Abst) w t))) in 
(\forall (c: C).(\forall (u2: T).((pr3 c u1 u2) \to ((((iso u1 u2) \to 
(\forall (P: Prop).P))) \to (pr3 c (THeads (Flat Appl) us (THead (Bind Abbr) 
v t)) u2)))))))))
\def
 \lambda (us: TList).(TList_ind (\lambda (t: TList).(\forall (v: T).(\forall 
(w: T).(\forall (t0: T).(let u1 \def (THeads (Flat Appl) t (THead (Flat Appl) 
v (THead (Bind Abst) w t0))) in (\forall (c: C).(\forall (u2: T).((pr3 c u1 
u2) \to ((((iso u1 u2) \to (\forall (P: Prop).P))) \to (pr3 c (THeads (Flat 
Appl) t (THead (Bind Abbr) v t0)) u2)))))))))) (\lambda (v: T).(\lambda (w: 
T).(\lambda (t: T).(\lambda (c: C).(\lambda (u2: T).(\lambda (H: (pr3 c 
(THead (Flat Appl) v (THead (Bind Abst) w t)) u2)).(\lambda (H0: (((iso 
(THead (Flat Appl) v (THead (Bind Abst) w t)) u2) \to (\forall (P: 
Prop).P)))).(pr3_iso_beta v w t c u2 H H0)))))))) (\lambda (t: T).(\lambda 
(t0: TList).(\lambda (H: ((\forall (v: T).(\forall (w: T).(\forall (t1: 
T).(\forall (c: C).(\forall (u2: T).((pr3 c (THeads (Flat Appl) t0 (THead 
(Flat Appl) v (THead (Bind Abst) w t1))) u2) \to ((((iso (THeads (Flat Appl) 
t0 (THead (Flat Appl) v (THead (Bind Abst) w t1))) u2) \to (\forall (P: 
Prop).P))) \to (pr3 c (THeads (Flat Appl) t0 (THead (Bind Abbr) v t1)) 
u2)))))))))).(\lambda (v: T).(\lambda (w: T).(\lambda (t1: T).(\lambda (c: 
C).(\lambda (u2: T).(\lambda (H0: (pr3 c (THead (Flat Appl) t (THeads (Flat 
Appl) t0 (THead (Flat Appl) v (THead (Bind Abst) w t1)))) u2)).(\lambda (H1: 
(((iso (THead (Flat Appl) t (THeads (Flat Appl) t0 (THead (Flat Appl) v 
(THead (Bind Abst) w t1)))) u2) \to (\forall (P: Prop).P)))).(let H2 \def 
(pr3_gen_appl c t (THeads (Flat Appl) t0 (THead (Flat Appl) v (THead (Bind 
Abst) w t1))) u2 H0) in (or3_ind (ex3_2 T T (\lambda (u3: T).(\lambda (t2: 
T).(eq T u2 (THead (Flat Appl) u3 t2)))) (\lambda (u3: T).(\lambda (_: 
T).(pr3 c t u3))) (\lambda (_: T).(\lambda (t2: T).(pr3 c (THeads (Flat Appl) 
t0 (THead (Flat Appl) v (THead (Bind Abst) w t1))) t2)))) (ex4_4 T T T T 
(\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda (t2: T).(pr3 c 
(THead (Bind Abbr) u3 t2) u2))))) (\lambda (_: T).(\lambda (_: T).(\lambda 
(u3: T).(\lambda (_: T).(pr3 c t u3))))) (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(pr3 c (THeads (Flat Appl) t0 (THead (Flat 
Appl) v (THead (Bind Abst) w t1))) (THead (Bind Abst) y1 z1)))))) (\lambda 
(_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t2: T).(\forall (b: 
B).(\forall (u: T).(pr3 (CHead c (Bind b) u) z1 t2)))))))) (ex6_6 B T T T T T 
(\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(pr3 c 
(THeads (Flat Appl) t0 (THead (Flat Appl) v (THead (Bind Abst) w t1))) (THead 
(Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (z2: T).(\lambda (u3: T).(\lambda (y2: T).(pr3 c (THead (Bind b) 
y2 (THead (Flat Appl) (lift (S O) O u3) z2)) u2))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda 
(_: T).(pr3 c t u3))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr3 c y1 y2))))))) 
(\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda 
(_: T).(\lambda (y2: T).(pr3 (CHead c (Bind b) y2) z1 z2)))))))) (pr3 c 
(THead (Flat Appl) t (THeads (Flat Appl) t0 (THead (Bind Abbr) v t1))) u2) 
(\lambda (H3: (ex3_2 T T (\lambda (u3: T).(\lambda (t2: T).(eq T u2 (THead 
(Flat Appl) u3 t2)))) (\lambda (u3: T).(\lambda (_: T).(pr3 c t u3))) 
(\lambda (_: T).(\lambda (t2: T).(pr3 c (THeads (Flat Appl) t0 (THead (Flat 
Appl) v (THead (Bind Abst) w t1))) t2))))).(ex3_2_ind T T (\lambda (u3: 
T).(\lambda (t2: T).(eq T u2 (THead (Flat Appl) u3 t2)))) (\lambda (u3: 
T).(\lambda (_: T).(pr3 c t u3))) (\lambda (_: T).(\lambda (t2: T).(pr3 c 
(THeads (Flat Appl) t0 (THead (Flat Appl) v (THead (Bind Abst) w t1))) t2))) 
(pr3 c (THead (Flat Appl) t (THeads (Flat Appl) t0 (THead (Bind Abbr) v t1))) 
u2) (\lambda (x0: T).(\lambda (x1: T).(\lambda (H4: (eq T u2 (THead (Flat 
Appl) x0 x1))).(\lambda (_: (pr3 c t x0)).(\lambda (_: (pr3 c (THeads (Flat 
Appl) t0 (THead (Flat Appl) v (THead (Bind Abst) w t1))) x1)).(let H7 \def 
(eq_ind T u2 (\lambda (t2: T).((iso (THead (Flat Appl) t (THeads (Flat Appl) 
t0 (THead (Flat Appl) v (THead (Bind Abst) w t1)))) t2) \to (\forall (P: 
Prop).P))) H1 (THead (Flat Appl) x0 x1) H4) in (eq_ind_r T (THead (Flat Appl) 
x0 x1) (\lambda (t2: T).(pr3 c (THead (Flat Appl) t (THeads (Flat Appl) t0 
(THead (Bind Abbr) v t1))) t2)) (H7 (iso_head t x0 (THeads (Flat Appl) t0 
(THead (Flat Appl) v (THead (Bind Abst) w t1))) x1 (Flat Appl)) (pr3 c (THead 
(Flat Appl) t (THeads (Flat Appl) t0 (THead (Bind Abbr) v t1))) (THead (Flat 
Appl) x0 x1))) u2 H4))))))) H3)) (\lambda (H3: (ex4_4 T T T T (\lambda (_: 
T).(\lambda (_: T).(\lambda (u3: T).(\lambda (t2: T).(pr3 c (THead (Bind 
Abbr) u3 t2) u2))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u3: 
T).(\lambda (_: T).(pr3 c t u3))))) (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(pr3 c (THeads (Flat Appl) t0 (THead (Flat 
Appl) v (THead (Bind Abst) w t1))) (THead (Bind Abst) y1 z1)))))) (\lambda 
(_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t2: T).(\forall (b: 
B).(\forall (u: T).(pr3 (CHead c (Bind b) u) z1 t2))))))))).(ex4_4_ind T T T 
T (\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda (t2: T).(pr3 c 
(THead (Bind Abbr) u3 t2) u2))))) (\lambda (_: T).(\lambda (_: T).(\lambda 
(u3: T).(\lambda (_: T).(pr3 c t u3))))) (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(pr3 c (THeads (Flat Appl) t0 (THead (Flat 
Appl) v (THead (Bind Abst) w t1))) (THead (Bind Abst) y1 z1)))))) (\lambda 
(_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t2: T).(\forall (b: 
B).(\forall (u: T).(pr3 (CHead c (Bind b) u) z1 t2))))))) (pr3 c (THead (Flat 
Appl) t (THeads (Flat Appl) t0 (THead (Bind Abbr) v t1))) u2) (\lambda (x0: 
T).(\lambda (x1: T).(\lambda (x2: T).(\lambda (x3: T).(\lambda (H4: (pr3 c 
(THead (Bind Abbr) x2 x3) u2)).(\lambda (H5: (pr3 c t x2)).(\lambda (H6: (pr3 
c (THeads (Flat Appl) t0 (THead (Flat Appl) v (THead (Bind Abst) w t1))) 
(THead (Bind Abst) x0 x1))).(\lambda (H7: ((\forall (b: B).(\forall (u: 
T).(pr3 (CHead c (Bind b) u) x1 x3))))).(pr3_t (THead (Bind Abbr) t x1) 
(THead (Flat Appl) t (THeads (Flat Appl) t0 (THead (Bind Abbr) v t1))) c 
(pr3_t (THead (Flat Appl) t (THead (Bind Abst) x0 x1)) (THead (Flat Appl) t 
(THeads (Flat Appl) t0 (THead (Bind Abbr) v t1))) c (pr3_thin_dx c (THeads 
(Flat Appl) t0 (THead (Bind Abbr) v t1)) (THead (Bind Abst) x0 x1) (H v w t1 
c (THead (Bind Abst) x0 x1) H6 (\lambda (H8: (iso (THeads (Flat Appl) t0 
(THead (Flat Appl) v (THead (Bind Abst) w t1))) (THead (Bind Abst) x0 
x1))).(\lambda (P: Prop).(iso_flats_flat_bind_false Appl Appl Abst x0 v x1 
(THead (Bind Abst) w t1) t0 H8 P)))) t Appl) (THead (Bind Abbr) t x1) 
(pr3_pr2 c (THead (Flat Appl) t (THead (Bind Abst) x0 x1)) (THead (Bind Abbr) 
t x1) (pr2_free c (THead (Flat Appl) t (THead (Bind Abst) x0 x1)) (THead 
(Bind Abbr) t x1) (pr0_beta x0 t t (pr0_refl t) x1 x1 (pr0_refl x1))))) u2 
(pr3_t (THead (Bind Abbr) x2 x3) (THead (Bind Abbr) t x1) c (pr3_head_12 c t 
x2 H5 (Bind Abbr) x1 x3 (H7 Abbr x2)) u2 H4)))))))))) H3)) (\lambda (H3: 
(ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(pr3 c (THeads (Flat Appl) t0 (THead (Flat Appl) v (THead (Bind Abst) 
w t1))) (THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u3: T).(\lambda (y2: T).(pr3 c 
(THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u3) z2)) u2))))))) 
(\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u3: 
T).(\lambda (_: T).(pr3 c t u3))))))) (\lambda (_: B).(\lambda (y1: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr3 c y1 
y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: 
T).(\lambda (_: T).(\lambda (y2: T).(pr3 (CHead c (Bind b) y2) z1 
z2))))))))).(ex6_6_ind B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b 
Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(pr3 c (THeads (Flat Appl) t0 (THead (Flat 
Appl) v (THead (Bind Abst) w t1))) (THead (Bind b) y1 z1)))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u3: T).(\lambda 
(y2: T).(pr3 c (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u3) z2)) 
u2))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u3: T).(\lambda (_: T).(pr3 c t u3))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr3 c y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr3 (CHead c (Bind b) 
y2) z1 z2))))))) (pr3 c (THead (Flat Appl) t (THeads (Flat Appl) t0 (THead 
(Bind Abbr) v t1))) u2) (\lambda (x0: B).(\lambda (x1: T).(\lambda (x2: 
T).(\lambda (x3: T).(\lambda (x4: T).(\lambda (x5: T).(\lambda (H4: (not (eq 
B x0 Abst))).(\lambda (H5: (pr3 c (THeads (Flat Appl) t0 (THead (Flat Appl) v 
(THead (Bind Abst) w t1))) (THead (Bind x0) x1 x2))).(\lambda (H6: (pr3 c 
(THead (Bind x0) x5 (THead (Flat Appl) (lift (S O) O x4) x3)) u2)).(\lambda 
(H7: (pr3 c t x4)).(\lambda (H8: (pr3 c x1 x5)).(\lambda (H9: (pr3 (CHead c 
(Bind x0) x5) x2 x3)).(pr3_t (THead (Bind x0) x1 (THead (Flat Appl) (lift (S 
O) O x4) x2)) (THead (Flat Appl) t (THeads (Flat Appl) t0 (THead (Bind Abbr) 
v t1))) c (pr3_t (THead (Bind x0) x1 (THead (Flat Appl) (lift (S O) O t) x2)) 
(THead (Flat Appl) t (THeads (Flat Appl) t0 (THead (Bind Abbr) v t1))) c 
(pr3_t (THead (Flat Appl) t (THead (Bind x0) x1 x2)) (THead (Flat Appl) t 
(THeads (Flat Appl) t0 (THead (Bind Abbr) v t1))) c (pr3_thin_dx c (THeads 
(Flat Appl) t0 (THead (Bind Abbr) v t1)) (THead (Bind x0) x1 x2) (H v w t1 c 
(THead (Bind x0) x1 x2) H5 (\lambda (H10: (iso (THeads (Flat Appl) t0 (THead 
(Flat Appl) v (THead (Bind Abst) w t1))) (THead (Bind x0) x1 x2))).(\lambda 
(P: Prop).(iso_flats_flat_bind_false Appl Appl x0 x1 v x2 (THead (Bind Abst) 
w t1) t0 H10 P)))) t Appl) (THead (Bind x0) x1 (THead (Flat Appl) (lift (S O) 
O t) x2)) (pr3_pr2 c (THead (Flat Appl) t (THead (Bind x0) x1 x2)) (THead 
(Bind x0) x1 (THead (Flat Appl) (lift (S O) O t) x2)) (pr2_free c (THead 
(Flat Appl) t (THead (Bind x0) x1 x2)) (THead (Bind x0) x1 (THead (Flat Appl) 
(lift (S O) O t) x2)) (pr0_upsilon x0 H4 t t (pr0_refl t) x1 x1 (pr0_refl x1) 
x2 x2 (pr0_refl x2))))) (THead (Bind x0) x1 (THead (Flat Appl) (lift (S O) O 
x4) x2)) (pr3_head_12 c x1 x1 (pr3_refl c x1) (Bind x0) (THead (Flat Appl) 
(lift (S O) O t) x2) (THead (Flat Appl) (lift (S O) O x4) x2) (pr3_head_12 
(CHead c (Bind x0) x1) (lift (S O) O t) (lift (S O) O x4) (pr3_lift (CHead c 
(Bind x0) x1) c (S O) O (drop_drop (Bind x0) O c c (drop_refl c) x1) t x4 H7) 
(Flat Appl) x2 x2 (pr3_refl (CHead (CHead c (Bind x0) x1) (Flat Appl) (lift 
(S O) O x4)) x2)))) u2 (pr3_t (THead (Bind x0) x5 (THead (Flat Appl) (lift (S 
O) O x4) x3)) (THead (Bind x0) x1 (THead (Flat Appl) (lift (S O) O x4) x2)) c 
(pr3_head_12 c x1 x5 H8 (Bind x0) (THead (Flat Appl) (lift (S O) O x4) x2) 
(THead (Flat Appl) (lift (S O) O x4) x3) (pr3_thin_dx (CHead c (Bind x0) x5) 
x2 x3 H9 (lift (S O) O x4) Appl)) u2 H6)))))))))))))) H3)) H2)))))))))))) us).
(* COMMENTS
Initial nodes: 3345
END *)

