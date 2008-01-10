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



include "csuba/getl.ma".

include "csuba/props.ma".

include "arity/props.ma".

include "T/props.ma".

theorem csuba_arity:
 \forall (g: G).(\forall (c1: C).(\forall (t: T).(\forall (a: A).((arity g c1 
t a) \to (\forall (c2: C).((csuba g c1 c2) \to (arity g c2 t a)))))))
\def
 \lambda (g: G).(\lambda (c1: C).(\lambda (t: T).(\lambda (a: A).(\lambda (H: 
(arity g c1 t a)).(arity_ind g (\lambda (c: C).(\lambda (t0: T).(\lambda (a0: 
A).(\forall (c2: C).((csuba g c c2) \to (arity g c2 t0 a0)))))) (\lambda (c: 
C).(\lambda (n: nat).(\lambda (c2: C).(\lambda (_: (csuba g c 
c2)).(arity_sort g c2 n))))) (\lambda (c: C).(\lambda (d: C).(\lambda (u: 
T).(\lambda (i: nat).(\lambda (H0: (getl i c (CHead d (Bind Abbr) 
u))).(\lambda (a0: A).(\lambda (_: (arity g d u a0)).(\lambda (H2: ((\forall 
(c2: C).((csuba g d c2) \to (arity g c2 u a0))))).(\lambda (c2: C).(\lambda 
(H3: (csuba g c c2)).(let H4 \def (csuba_getl_abbr g c d u i H0 c2 H3) in 
(ex2_ind C (\lambda (d2: C).(getl i c2 (CHead d2 (Bind Abbr) u))) (\lambda 
(d2: C).(csuba g d d2)) (arity g c2 (TLRef i) a0) (\lambda (x: C).(\lambda 
(H5: (getl i c2 (CHead x (Bind Abbr) u))).(\lambda (H6: (csuba g d 
x)).(arity_abbr g c2 x u i H5 a0 (H2 x H6))))) H4)))))))))))) (\lambda (c: 
C).(\lambda (d: C).(\lambda (u: T).(\lambda (i: nat).(\lambda (H0: (getl i c 
(CHead d (Bind Abst) u))).(\lambda (a0: A).(\lambda (H1: (arity g d u (asucc 
g a0))).(\lambda (H2: ((\forall (c2: C).((csuba g d c2) \to (arity g c2 u 
(asucc g a0)))))).(\lambda (c2: C).(\lambda (H3: (csuba g c c2)).(let H4 \def 
(csuba_getl_abst g c d u i H0 c2 H3) in (or_ind (ex2 C (\lambda (d2: C).(getl 
i c2 (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d d2))) (ex4_3 C T 
A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(getl i c2 (CHead d2 
(Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g 
d d2)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a1: A).(arity g d u (asucc 
g a1))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a1: A).(arity g d2 u2 
a1))))) (arity g c2 (TLRef i) a0) (\lambda (H5: (ex2 C (\lambda (d2: C).(getl 
i c2 (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d d2)))).(ex2_ind C 
(\lambda (d2: C).(getl i c2 (CHead d2 (Bind Abst) u))) (\lambda (d2: 
C).(csuba g d d2)) (arity g c2 (TLRef i) a0) (\lambda (x: C).(\lambda (H6: 
(getl i c2 (CHead x (Bind Abst) u))).(\lambda (H7: (csuba g d x)).(arity_abst 
g c2 x u i H6 a0 (H2 x H7))))) H5)) (\lambda (H5: (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(getl i c2 (CHead d2 (Bind Abbr) u2))))) 
(\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d d2)))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a1: A).(arity g d u (asucc g a1))))) 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (a1: A).(arity g d2 u2 
a1)))))).(ex4_3_ind C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: 
A).(getl i c2 (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d d2)))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a1: A).(arity g d u (asucc g a1))))) (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (a1: A).(arity g d2 u2 a1)))) (arity g c2 (TLRef i) a0) (\lambda 
(x0: C).(\lambda (x1: T).(\lambda (x2: A).(\lambda (H6: (getl i c2 (CHead x0 
(Bind Abbr) x1))).(\lambda (_: (csuba g d x0)).(\lambda (H8: (arity g d u 
(asucc g x2))).(\lambda (H9: (arity g x0 x1 x2)).(arity_repl g c2 (TLRef i) 
x2 (arity_abbr g c2 x0 x1 i H6 x2 H9) a0 (asucc_inj g x2 a0 (arity_mono g d u 
(asucc g x2) H8 (asucc g a0) H1)))))))))) H5)) H4)))))))))))) (\lambda (b: 
B).(\lambda (H0: (not (eq B b Abst))).(\lambda (c: C).(\lambda (u: 
T).(\lambda (a1: A).(\lambda (_: (arity g c u a1)).(\lambda (H2: ((\forall 
(c2: C).((csuba g c c2) \to (arity g c2 u a1))))).(\lambda (t0: T).(\lambda 
(a2: A).(\lambda (_: (arity g (CHead c (Bind b) u) t0 a2)).(\lambda (H4: 
((\forall (c2: C).((csuba g (CHead c (Bind b) u) c2) \to (arity g c2 t0 
a2))))).(\lambda (c2: C).(\lambda (H5: (csuba g c c2)).(arity_bind g b H0 c2 
u a1 (H2 c2 H5) t0 a2 (H4 (CHead c2 (Bind b) u) (csuba_head g c c2 H5 (Bind 
b) u)))))))))))))))) (\lambda (c: C).(\lambda (u: T).(\lambda (a1: 
A).(\lambda (_: (arity g c u (asucc g a1))).(\lambda (H1: ((\forall (c2: 
C).((csuba g c c2) \to (arity g c2 u (asucc g a1)))))).(\lambda (t0: 
T).(\lambda (a2: A).(\lambda (_: (arity g (CHead c (Bind Abst) u) t0 
a2)).(\lambda (H3: ((\forall (c2: C).((csuba g (CHead c (Bind Abst) u) c2) 
\to (arity g c2 t0 a2))))).(\lambda (c2: C).(\lambda (H4: (csuba g c 
c2)).(arity_head g c2 u a1 (H1 c2 H4) t0 a2 (H3 (CHead c2 (Bind Abst) u) 
(csuba_head g c c2 H4 (Bind Abst) u)))))))))))))) (\lambda (c: C).(\lambda 
(u: T).(\lambda (a1: A).(\lambda (_: (arity g c u a1)).(\lambda (H1: 
((\forall (c2: C).((csuba g c c2) \to (arity g c2 u a1))))).(\lambda (t0: 
T).(\lambda (a2: A).(\lambda (_: (arity g c t0 (AHead a1 a2))).(\lambda (H3: 
((\forall (c2: C).((csuba g c c2) \to (arity g c2 t0 (AHead a1 
a2)))))).(\lambda (c2: C).(\lambda (H4: (csuba g c c2)).(arity_appl g c2 u a1 
(H1 c2 H4) t0 a2 (H3 c2 H4))))))))))))) (\lambda (c: C).(\lambda (u: 
T).(\lambda (a0: A).(\lambda (_: (arity g c u (asucc g a0))).(\lambda (H1: 
((\forall (c2: C).((csuba g c c2) \to (arity g c2 u (asucc g 
a0)))))).(\lambda (t0: T).(\lambda (_: (arity g c t0 a0)).(\lambda (H3: 
((\forall (c2: C).((csuba g c c2) \to (arity g c2 t0 a0))))).(\lambda (c2: 
C).(\lambda (H4: (csuba g c c2)).(arity_cast g c2 u a0 (H1 c2 H4) t0 (H3 c2 
H4)))))))))))) (\lambda (c: C).(\lambda (t0: T).(\lambda (a1: A).(\lambda (_: 
(arity g c t0 a1)).(\lambda (H1: ((\forall (c2: C).((csuba g c c2) \to (arity 
g c2 t0 a1))))).(\lambda (a2: A).(\lambda (H2: (leq g a1 a2)).(\lambda (c2: 
C).(\lambda (H3: (csuba g c c2)).(arity_repl g c2 t0 a1 (H1 c2 H3) a2 
H2)))))))))) c1 t a H))))).

theorem csuba_arity_rev:
 \forall (g: G).(\forall (c1: C).(\forall (t: T).(\forall (a: A).((arity g c1 
t a) \to (\forall (c2: C).((csuba g c2 c1) \to (arity g c2 t a)))))))
\def
 \lambda (g: G).(\lambda (c1: C).(\lambda (t: T).(\lambda (a: A).(\lambda (H: 
(arity g c1 t a)).(arity_ind g (\lambda (c: C).(\lambda (t0: T).(\lambda (a0: 
A).(\forall (c2: C).((csuba g c2 c) \to (arity g c2 t0 a0)))))) (\lambda (c: 
C).(\lambda (n: nat).(\lambda (c2: C).(\lambda (_: (csuba g c2 
c)).(arity_sort g c2 n))))) (\lambda (c: C).(\lambda (d: C).(\lambda (u: 
T).(\lambda (i: nat).(\lambda (H0: (getl i c (CHead d (Bind Abbr) 
u))).(\lambda (a0: A).(\lambda (H1: (arity g d u a0)).(\lambda (H2: ((\forall 
(c2: C).((csuba g c2 d) \to (arity g c2 u a0))))).(\lambda (c2: C).(\lambda 
(H3: (csuba g c2 c)).(let H4 \def (csuba_getl_abbr_rev g c d u i H0 c2 H3) in 
(or_ind (ex2 C (\lambda (d2: C).(getl i c2 (CHead d2 (Bind Abbr) u))) 
(\lambda (d2: C).(csuba g d2 d))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (_: A).(getl i c2 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: 
C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d)))) (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (a1: A).(arity g d2 u2 (asucc g a1))))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a1: A).(arity g d u a1))))) (arity g c2 
(TLRef i) a0) (\lambda (H5: (ex2 C (\lambda (d2: C).(getl i c2 (CHead d2 
(Bind Abbr) u))) (\lambda (d2: C).(csuba g d2 d)))).(ex2_ind C (\lambda (d2: 
C).(getl i c2 (CHead d2 (Bind Abbr) u))) (\lambda (d2: C).(csuba g d2 d)) 
(arity g c2 (TLRef i) a0) (\lambda (x: C).(\lambda (H6: (getl i c2 (CHead x 
(Bind Abbr) u))).(\lambda (H7: (csuba g x d)).(arity_abbr g c2 x u i H6 a0 
(H2 x H7))))) H5)) (\lambda (H5: (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (_: A).(getl i c2 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: 
C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d)))) (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (a1: A).(arity g d2 u2 (asucc g a1))))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a1: A).(arity g d u a1)))))).(ex4_3_ind C T 
A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(getl i c2 (CHead d2 
(Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g 
d2 d)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a1: A).(arity g d2 u2 
(asucc g a1))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a1: A).(arity g d 
u a1)))) (arity g c2 (TLRef i) a0) (\lambda (x0: C).(\lambda (x1: T).(\lambda 
(x2: A).(\lambda (H6: (getl i c2 (CHead x0 (Bind Abst) x1))).(\lambda (_: 
(csuba g x0 d)).(\lambda (H8: (arity g x0 x1 (asucc g x2))).(\lambda (H9: 
(arity g d u x2)).(arity_repl g c2 (TLRef i) x2 (arity_abst g c2 x0 x1 i H6 
x2 H8) a0 (arity_mono g d u x2 H9 a0 H1))))))))) H5)) H4)))))))))))) (\lambda 
(c: C).(\lambda (d: C).(\lambda (u: T).(\lambda (i: nat).(\lambda (H0: (getl 
i c (CHead d (Bind Abst) u))).(\lambda (a0: A).(\lambda (_: (arity g d u 
(asucc g a0))).(\lambda (H2: ((\forall (c2: C).((csuba g c2 d) \to (arity g 
c2 u (asucc g a0)))))).(\lambda (c2: C).(\lambda (H3: (csuba g c2 c)).(let H4 
\def (csuba_getl_abst_rev g c d u i H0 c2 H3) in (ex2_ind C (\lambda (d2: 
C).(getl i c2 (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d)) 
(arity g c2 (TLRef i) a0) (\lambda (x: C).(\lambda (H5: (getl i c2 (CHead x 
(Bind Abst) u))).(\lambda (H6: (csuba g x d)).(arity_abst g c2 x u i H5 a0 
(H2 x H6))))) H4)))))))))))) (\lambda (b: B).(\lambda (H0: (not (eq B b 
Abst))).(\lambda (c: C).(\lambda (u: T).(\lambda (a1: A).(\lambda (_: (arity 
g c u a1)).(\lambda (H2: ((\forall (c2: C).((csuba g c2 c) \to (arity g c2 u 
a1))))).(\lambda (t0: T).(\lambda (a2: A).(\lambda (_: (arity g (CHead c 
(Bind b) u) t0 a2)).(\lambda (H4: ((\forall (c2: C).((csuba g c2 (CHead c 
(Bind b) u)) \to (arity g c2 t0 a2))))).(\lambda (c2: C).(\lambda (H5: (csuba 
g c2 c)).(arity_bind g b H0 c2 u a1 (H2 c2 H5) t0 a2 (H4 (CHead c2 (Bind b) 
u) (csuba_head g c2 c H5 (Bind b) u)))))))))))))))) (\lambda (c: C).(\lambda 
(u: T).(\lambda (a1: A).(\lambda (_: (arity g c u (asucc g a1))).(\lambda 
(H1: ((\forall (c2: C).((csuba g c2 c) \to (arity g c2 u (asucc g 
a1)))))).(\lambda (t0: T).(\lambda (a2: A).(\lambda (_: (arity g (CHead c 
(Bind Abst) u) t0 a2)).(\lambda (H3: ((\forall (c2: C).((csuba g c2 (CHead c 
(Bind Abst) u)) \to (arity g c2 t0 a2))))).(\lambda (c2: C).(\lambda (H4: 
(csuba g c2 c)).(arity_head g c2 u a1 (H1 c2 H4) t0 a2 (H3 (CHead c2 (Bind 
Abst) u) (csuba_head g c2 c H4 (Bind Abst) u)))))))))))))) (\lambda (c: 
C).(\lambda (u: T).(\lambda (a1: A).(\lambda (_: (arity g c u a1)).(\lambda 
(H1: ((\forall (c2: C).((csuba g c2 c) \to (arity g c2 u a1))))).(\lambda 
(t0: T).(\lambda (a2: A).(\lambda (_: (arity g c t0 (AHead a1 a2))).(\lambda 
(H3: ((\forall (c2: C).((csuba g c2 c) \to (arity g c2 t0 (AHead a1 
a2)))))).(\lambda (c2: C).(\lambda (H4: (csuba g c2 c)).(arity_appl g c2 u a1 
(H1 c2 H4) t0 a2 (H3 c2 H4))))))))))))) (\lambda (c: C).(\lambda (u: 
T).(\lambda (a0: A).(\lambda (_: (arity g c u (asucc g a0))).(\lambda (H1: 
((\forall (c2: C).((csuba g c2 c) \to (arity g c2 u (asucc g 
a0)))))).(\lambda (t0: T).(\lambda (_: (arity g c t0 a0)).(\lambda (H3: 
((\forall (c2: C).((csuba g c2 c) \to (arity g c2 t0 a0))))).(\lambda (c2: 
C).(\lambda (H4: (csuba g c2 c)).(arity_cast g c2 u a0 (H1 c2 H4) t0 (H3 c2 
H4)))))))))))) (\lambda (c: C).(\lambda (t0: T).(\lambda (a1: A).(\lambda (_: 
(arity g c t0 a1)).(\lambda (H1: ((\forall (c2: C).((csuba g c2 c) \to (arity 
g c2 t0 a1))))).(\lambda (a2: A).(\lambda (H2: (leq g a1 a2)).(\lambda (c2: 
C).(\lambda (H3: (csuba g c2 c)).(arity_repl g c2 t0 a1 (H1 c2 H3) a2 
H2)))))))))) c1 t a H))))).

theorem arity_appls_appl:
 \forall (g: G).(\forall (c: C).(\forall (v: T).(\forall (a1: A).((arity g c 
v a1) \to (\forall (u: T).((arity g c u (asucc g a1)) \to (\forall (t: 
T).(\forall (vs: TList).(\forall (a2: A).((arity g c (THeads (Flat Appl) vs 
(THead (Bind Abbr) v t)) a2) \to (arity g c (THeads (Flat Appl) vs (THead 
(Flat Appl) v (THead (Bind Abst) u t))) a2)))))))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (v: T).(\lambda (a1: A).(\lambda (H: 
(arity g c v a1)).(\lambda (u: T).(\lambda (H0: (arity g c u (asucc g 
a1))).(\lambda (t: T).(\lambda (vs: TList).(TList_ind (\lambda (t0: 
TList).(\forall (a2: A).((arity g c (THeads (Flat Appl) t0 (THead (Bind Abbr) 
v t)) a2) \to (arity g c (THeads (Flat Appl) t0 (THead (Flat Appl) v (THead 
(Bind Abst) u t))) a2)))) (\lambda (a2: A).(\lambda (H1: (arity g c (THead 
(Bind Abbr) v t) a2)).(let H_x \def (arity_gen_bind Abbr (\lambda (H2: (eq B 
Abbr Abst)).(not_abbr_abst H2)) g c v t a2 H1) in (let H2 \def H_x in 
(ex2_ind A (\lambda (a3: A).(arity g c v a3)) (\lambda (_: A).(arity g (CHead 
c (Bind Abbr) v) t a2)) (arity g c (THead (Flat Appl) v (THead (Bind Abst) u 
t)) a2) (\lambda (x: A).(\lambda (_: (arity g c v x)).(\lambda (H4: (arity g 
(CHead c (Bind Abbr) v) t a2)).(arity_appl g c v a1 H (THead (Bind Abst) u t) 
a2 (arity_head g c u a1 H0 t a2 (csuba_arity_rev g (CHead c (Bind Abbr) v) t 
a2 H4 (CHead c (Bind Abst) u) (csuba_abst g c c (csuba_refl g c) u a1 H0 v 
H))))))) H2))))) (\lambda (t0: T).(\lambda (t1: TList).(\lambda (H1: 
((\forall (a2: A).((arity g c (THeads (Flat Appl) t1 (THead (Bind Abbr) v t)) 
a2) \to (arity g c (THeads (Flat Appl) t1 (THead (Flat Appl) v (THead (Bind 
Abst) u t))) a2))))).(\lambda (a2: A).(\lambda (H2: (arity g c (THead (Flat 
Appl) t0 (THeads (Flat Appl) t1 (THead (Bind Abbr) v t))) a2)).(let H3 \def 
(arity_gen_appl g c t0 (THeads (Flat Appl) t1 (THead (Bind Abbr) v t)) a2 H2) 
in (ex2_ind A (\lambda (a3: A).(arity g c t0 a3)) (\lambda (a3: A).(arity g c 
(THeads (Flat Appl) t1 (THead (Bind Abbr) v t)) (AHead a3 a2))) (arity g c 
(THead (Flat Appl) t0 (THeads (Flat Appl) t1 (THead (Flat Appl) v (THead 
(Bind Abst) u t)))) a2) (\lambda (x: A).(\lambda (H4: (arity g c t0 
x)).(\lambda (H5: (arity g c (THeads (Flat Appl) t1 (THead (Bind Abbr) v t)) 
(AHead x a2))).(arity_appl g c t0 x H4 (THeads (Flat Appl) t1 (THead (Flat 
Appl) v (THead (Bind Abst) u t))) a2 (H1 (AHead x a2) H5))))) H3))))))) 
vs))))))))).

