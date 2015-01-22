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

include "Basic-1/nf2/pr3.ma".

include "Basic-1/pr3/fwd.ma".

include "Basic-1/iso/props.ma".

theorem nf2_iso_appls_lref:
 \forall (c: C).(\forall (i: nat).((nf2 c (TLRef i)) \to (\forall (vs: 
TList).(\forall (u: T).((pr3 c (THeads (Flat Appl) vs (TLRef i)) u) \to (iso 
(THeads (Flat Appl) vs (TLRef i)) u))))))
\def
 \lambda (c: C).(\lambda (i: nat).(\lambda (H: (nf2 c (TLRef i))).(\lambda 
(vs: TList).(TList_ind (\lambda (t: TList).(\forall (u: T).((pr3 c (THeads 
(Flat Appl) t (TLRef i)) u) \to (iso (THeads (Flat Appl) t (TLRef i)) u)))) 
(\lambda (u: T).(\lambda (H0: (pr3 c (TLRef i) u)).(let H_y \def 
(nf2_pr3_unfold c (TLRef i) u H0 H) in (let H1 \def (eq_ind_r T u (\lambda 
(t: T).(pr3 c (TLRef i) t)) H0 (TLRef i) H_y) in (eq_ind T (TLRef i) (\lambda 
(t: T).(iso (TLRef i) t)) (iso_refl (TLRef i)) u H_y))))) (\lambda (t: 
T).(\lambda (t0: TList).(\lambda (H0: ((\forall (u: T).((pr3 c (THeads (Flat 
Appl) t0 (TLRef i)) u) \to (iso (THeads (Flat Appl) t0 (TLRef i)) 
u))))).(\lambda (u: T).(\lambda (H1: (pr3 c (THead (Flat Appl) t (THeads 
(Flat Appl) t0 (TLRef i))) u)).(let H2 \def (pr3_gen_appl c t (THeads (Flat 
Appl) t0 (TLRef i)) u H1) in (or3_ind (ex3_2 T T (\lambda (u2: T).(\lambda 
(t2: T).(eq T u (THead (Flat Appl) u2 t2)))) (\lambda (u2: T).(\lambda (_: 
T).(pr3 c t u2))) (\lambda (_: T).(\lambda (t2: T).(pr3 c (THeads (Flat Appl) 
t0 (TLRef i)) t2)))) (ex4_4 T T T T (\lambda (_: T).(\lambda (_: T).(\lambda 
(u2: T).(\lambda (t2: T).(pr3 c (THead (Bind Abbr) u2 t2) u))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr3 c t u2))))) (\lambda 
(y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(pr3 c (THeads (Flat 
Appl) t0 (TLRef i)) (THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (t2: T).(\forall (b: B).(\forall (u0: 
T).(pr3 (CHead c (Bind b) u0) z1 t2)))))))) (ex6_6 B T T T T T (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(pr3 c (THeads (Flat 
Appl) t0 (TLRef i)) (THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda 
(_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: 
T).(pr3 c (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) z2)) 
u))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr3 c t u2))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr3 c y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr3 (CHead c (Bind b) 
y2) z1 z2)))))))) (iso (THead (Flat Appl) t (THeads (Flat Appl) t0 (TLRef 
i))) u) (\lambda (H3: (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T u 
(THead (Flat Appl) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c t u2))) 
(\lambda (_: T).(\lambda (t2: T).(pr3 c (THeads (Flat Appl) t0 (TLRef i)) 
t2))))).(ex3_2_ind T T (\lambda (u2: T).(\lambda (t2: T).(eq T u (THead (Flat 
Appl) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c t u2))) (\lambda (_: 
T).(\lambda (t2: T).(pr3 c (THeads (Flat Appl) t0 (TLRef i)) t2))) (iso 
(THead (Flat Appl) t (THeads (Flat Appl) t0 (TLRef i))) u) (\lambda (x0: 
T).(\lambda (x1: T).(\lambda (H4: (eq T u (THead (Flat Appl) x0 
x1))).(\lambda (_: (pr3 c t x0)).(\lambda (_: (pr3 c (THeads (Flat Appl) t0 
(TLRef i)) x1)).(eq_ind_r T (THead (Flat Appl) x0 x1) (\lambda (t1: T).(iso 
(THead (Flat Appl) t (THeads (Flat Appl) t0 (TLRef i))) t1)) (iso_head t x0 
(THeads (Flat Appl) t0 (TLRef i)) x1 (Flat Appl)) u H4)))))) H3)) (\lambda 
(H3: (ex4_4 T T T T (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(t2: T).(pr3 c (THead (Bind Abbr) u2 t2) u))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr3 c t u2))))) (\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(pr3 c (THeads (Flat 
Appl) t0 (TLRef i)) (THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (t2: T).(\forall (b: B).(\forall (u0: 
T).(pr3 (CHead c (Bind b) u0) z1 t2))))))))).(ex4_4_ind T T T T (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t2: T).(pr3 c (THead (Bind 
Abbr) u2 t2) u))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr3 c t u2))))) (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(pr3 c (THeads (Flat Appl) t0 (TLRef i)) (THead (Bind 
Abst) y1 z1)))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda 
(t2: T).(\forall (b: B).(\forall (u0: T).(pr3 (CHead c (Bind b) u0) z1 
t2))))))) (iso (THead (Flat Appl) t (THeads (Flat Appl) t0 (TLRef i))) u) 
(\lambda (x0: T).(\lambda (x1: T).(\lambda (x2: T).(\lambda (x3: T).(\lambda 
(_: (pr3 c (THead (Bind Abbr) x2 x3) u)).(\lambda (_: (pr3 c t x2)).(\lambda 
(H6: (pr3 c (THeads (Flat Appl) t0 (TLRef i)) (THead (Bind Abst) x0 
x1))).(\lambda (_: ((\forall (b: B).(\forall (u0: T).(pr3 (CHead c (Bind b) 
u0) x1 x3))))).(let H_y \def (H0 (THead (Bind Abst) x0 x1) H6) in 
(iso_flats_lref_bind_false Appl Abst i x0 x1 t0 H_y (iso (THead (Flat Appl) t 
(THeads (Flat Appl) t0 (TLRef i))) u))))))))))) H3)) (\lambda (H3: (ex6_6 B T 
T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(pr3 c (THeads (Flat Appl) t0 (TLRef i)) (THead (Bind b) y1 z1)))))))) 
(\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda 
(u2: T).(\lambda (y2: T).(pr3 c (THead (Bind b) y2 (THead (Flat Appl) (lift 
(S O) O u2) z2)) u))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr3 c t u2))))))) 
(\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (y2: T).(pr3 c y1 y2))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr3 
(CHead c (Bind b) y2) z1 z2))))))))).(ex6_6_ind B T T T T T (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(pr3 c (THeads (Flat 
Appl) t0 (TLRef i)) (THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda 
(_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: 
T).(pr3 c (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) z2)) 
u))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr3 c t u2))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr3 c y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr3 (CHead c (Bind b) 
y2) z1 z2))))))) (iso (THead (Flat Appl) t (THeads (Flat Appl) t0 (TLRef i))) 
u) (\lambda (x0: B).(\lambda (x1: T).(\lambda (x2: T).(\lambda (x3: 
T).(\lambda (x4: T).(\lambda (x5: T).(\lambda (_: (not (eq B x0 
Abst))).(\lambda (H5: (pr3 c (THeads (Flat Appl) t0 (TLRef i)) (THead (Bind 
x0) x1 x2))).(\lambda (_: (pr3 c (THead (Bind x0) x5 (THead (Flat Appl) (lift 
(S O) O x4) x3)) u)).(\lambda (_: (pr3 c t x4)).(\lambda (_: (pr3 c x1 
x5)).(\lambda (_: (pr3 (CHead c (Bind x0) x5) x2 x3)).(let H_y \def (H0 
(THead (Bind x0) x1 x2) H5) in (iso_flats_lref_bind_false Appl x0 i x1 x2 t0 
H_y (iso (THead (Flat Appl) t (THeads (Flat Appl) t0 (TLRef i))) 
u))))))))))))))) H3)) H2))))))) vs)))).
(* COMMENTS
Initial nodes: 1817
END *)

