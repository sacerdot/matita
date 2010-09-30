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

include "Basic-1/arity/defs.ma".

include "Basic-1/cimp/props.ma".

theorem arity_cimp_conf:
 \forall (g: G).(\forall (c1: C).(\forall (t: T).(\forall (a: A).((arity g c1 
t a) \to (\forall (c2: C).((cimp c1 c2) \to (arity g c2 t a)))))))
\def
 \lambda (g: G).(\lambda (c1: C).(\lambda (t: T).(\lambda (a: A).(\lambda (H: 
(arity g c1 t a)).(arity_ind g (\lambda (c: C).(\lambda (t0: T).(\lambda (a0: 
A).(\forall (c2: C).((cimp c c2) \to (arity g c2 t0 a0)))))) (\lambda (c: 
C).(\lambda (n: nat).(\lambda (c2: C).(\lambda (_: (cimp c c2)).(arity_sort g 
c2 n))))) (\lambda (c: C).(\lambda (d: C).(\lambda (u: T).(\lambda (i: 
nat).(\lambda (H0: (getl i c (CHead d (Bind Abbr) u))).(\lambda (a0: 
A).(\lambda (_: (arity g d u a0)).(\lambda (H2: ((\forall (c2: C).((cimp d 
c2) \to (arity g c2 u a0))))).(\lambda (c2: C).(\lambda (H3: (cimp c 
c2)).(let H_x \def (H3 Abbr d u i H0) in (let H4 \def H_x in (ex_ind C 
(\lambda (d2: C).(getl i c2 (CHead d2 (Bind Abbr) u))) (arity g c2 (TLRef i) 
a0) (\lambda (x: C).(\lambda (H5: (getl i c2 (CHead x (Bind Abbr) u))).(let 
H_x0 \def (cimp_getl_conf c c2 H3 Abbr d u i H0) in (let H6 \def H_x0 in 
(ex2_ind C (\lambda (d2: C).(cimp d d2)) (\lambda (d2: C).(getl i c2 (CHead 
d2 (Bind Abbr) u))) (arity g c2 (TLRef i) a0) (\lambda (x0: C).(\lambda (H7: 
(cimp d x0)).(\lambda (H8: (getl i c2 (CHead x0 (Bind Abbr) u))).(let H9 \def 
(eq_ind C (CHead x (Bind Abbr) u) (\lambda (c0: C).(getl i c2 c0)) H5 (CHead 
x0 (Bind Abbr) u) (getl_mono c2 (CHead x (Bind Abbr) u) i H5 (CHead x0 (Bind 
Abbr) u) H8)) in (let H10 \def (f_equal C C (\lambda (e: C).(match e in C 
return (\lambda (_: C).C) with [(CSort _) \Rightarrow x | (CHead c0 _ _) 
\Rightarrow c0])) (CHead x (Bind Abbr) u) (CHead x0 (Bind Abbr) u) (getl_mono 
c2 (CHead x (Bind Abbr) u) i H5 (CHead x0 (Bind Abbr) u) H8)) in (let H11 
\def (eq_ind_r C x0 (\lambda (c0: C).(getl i c2 (CHead c0 (Bind Abbr) u))) H9 
x H10) in (let H12 \def (eq_ind_r C x0 (\lambda (c0: C).(cimp d c0)) H7 x 
H10) in (arity_abbr g c2 x u i H11 a0 (H2 x H12))))))))) H6))))) 
H4))))))))))))) (\lambda (c: C).(\lambda (d: C).(\lambda (u: T).(\lambda (i: 
nat).(\lambda (H0: (getl i c (CHead d (Bind Abst) u))).(\lambda (a0: 
A).(\lambda (_: (arity g d u (asucc g a0))).(\lambda (H2: ((\forall (c2: 
C).((cimp d c2) \to (arity g c2 u (asucc g a0)))))).(\lambda (c2: C).(\lambda 
(H3: (cimp c c2)).(let H_x \def (H3 Abst d u i H0) in (let H4 \def H_x in 
(ex_ind C (\lambda (d2: C).(getl i c2 (CHead d2 (Bind Abst) u))) (arity g c2 
(TLRef i) a0) (\lambda (x: C).(\lambda (H5: (getl i c2 (CHead x (Bind Abst) 
u))).(let H_x0 \def (cimp_getl_conf c c2 H3 Abst d u i H0) in (let H6 \def 
H_x0 in (ex2_ind C (\lambda (d2: C).(cimp d d2)) (\lambda (d2: C).(getl i c2 
(CHead d2 (Bind Abst) u))) (arity g c2 (TLRef i) a0) (\lambda (x0: 
C).(\lambda (H7: (cimp d x0)).(\lambda (H8: (getl i c2 (CHead x0 (Bind Abst) 
u))).(let H9 \def (eq_ind C (CHead x (Bind Abst) u) (\lambda (c0: C).(getl i 
c2 c0)) H5 (CHead x0 (Bind Abst) u) (getl_mono c2 (CHead x (Bind Abst) u) i 
H5 (CHead x0 (Bind Abst) u) H8)) in (let H10 \def (f_equal C C (\lambda (e: 
C).(match e in C return (\lambda (_: C).C) with [(CSort _) \Rightarrow x | 
(CHead c0 _ _) \Rightarrow c0])) (CHead x (Bind Abst) u) (CHead x0 (Bind 
Abst) u) (getl_mono c2 (CHead x (Bind Abst) u) i H5 (CHead x0 (Bind Abst) u) 
H8)) in (let H11 \def (eq_ind_r C x0 (\lambda (c0: C).(getl i c2 (CHead c0 
(Bind Abst) u))) H9 x H10) in (let H12 \def (eq_ind_r C x0 (\lambda (c0: 
C).(cimp d c0)) H7 x H10) in (arity_abst g c2 x u i H11 a0 (H2 x H12))))))))) 
H6))))) H4))))))))))))) (\lambda (b: B).(\lambda (H0: (not (eq B b 
Abst))).(\lambda (c: C).(\lambda (u: T).(\lambda (a1: A).(\lambda (_: (arity 
g c u a1)).(\lambda (H2: ((\forall (c2: C).((cimp c c2) \to (arity g c2 u 
a1))))).(\lambda (t0: T).(\lambda (a2: A).(\lambda (_: (arity g (CHead c 
(Bind b) u) t0 a2)).(\lambda (H4: ((\forall (c2: C).((cimp (CHead c (Bind b) 
u) c2) \to (arity g c2 t0 a2))))).(\lambda (c2: C).(\lambda (H5: (cimp c 
c2)).(arity_bind g b H0 c2 u a1 (H2 c2 H5) t0 a2 (H4 (CHead c2 (Bind b) u) 
(cimp_bind c c2 H5 b u)))))))))))))))) (\lambda (c: C).(\lambda (u: 
T).(\lambda (a1: A).(\lambda (_: (arity g c u (asucc g a1))).(\lambda (H1: 
((\forall (c2: C).((cimp c c2) \to (arity g c2 u (asucc g a1)))))).(\lambda 
(t0: T).(\lambda (a2: A).(\lambda (_: (arity g (CHead c (Bind Abst) u) t0 
a2)).(\lambda (H3: ((\forall (c2: C).((cimp (CHead c (Bind Abst) u) c2) \to 
(arity g c2 t0 a2))))).(\lambda (c2: C).(\lambda (H4: (cimp c 
c2)).(arity_head g c2 u a1 (H1 c2 H4) t0 a2 (H3 (CHead c2 (Bind Abst) u) 
(cimp_bind c c2 H4 Abst u)))))))))))))) (\lambda (c: C).(\lambda (u: 
T).(\lambda (a1: A).(\lambda (_: (arity g c u a1)).(\lambda (H1: ((\forall 
(c2: C).((cimp c c2) \to (arity g c2 u a1))))).(\lambda (t0: T).(\lambda (a2: 
A).(\lambda (_: (arity g c t0 (AHead a1 a2))).(\lambda (H3: ((\forall (c2: 
C).((cimp c c2) \to (arity g c2 t0 (AHead a1 a2)))))).(\lambda (c2: 
C).(\lambda (H4: (cimp c c2)).(arity_appl g c2 u a1 (H1 c2 H4) t0 a2 (H3 c2 
H4))))))))))))) (\lambda (c: C).(\lambda (u: T).(\lambda (a0: A).(\lambda (_: 
(arity g c u (asucc g a0))).(\lambda (H1: ((\forall (c2: C).((cimp c c2) \to 
(arity g c2 u (asucc g a0)))))).(\lambda (t0: T).(\lambda (_: (arity g c t0 
a0)).(\lambda (H3: ((\forall (c2: C).((cimp c c2) \to (arity g c2 t0 
a0))))).(\lambda (c2: C).(\lambda (H4: (cimp c c2)).(arity_cast g c2 u a0 (H1 
c2 H4) t0 (H3 c2 H4)))))))))))) (\lambda (c: C).(\lambda (t0: T).(\lambda 
(a1: A).(\lambda (_: (arity g c t0 a1)).(\lambda (H1: ((\forall (c2: 
C).((cimp c c2) \to (arity g c2 t0 a1))))).(\lambda (a2: A).(\lambda (H2: 
(leq g a1 a2)).(\lambda (c2: C).(\lambda (H3: (cimp c c2)).(arity_repl g c2 
t0 a1 (H1 c2 H3) a2 H2)))))))))) c1 t a H))))).
(* COMMENTS
Initial nodes: 1505
END *)

