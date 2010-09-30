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

include "Basic-1/leq/asucc.ma".

include "Basic-1/getl/drop.ma".

theorem arity_gen_sort:
 \forall (g: G).(\forall (c: C).(\forall (n: nat).(\forall (a: A).((arity g c 
(TSort n) a) \to (leq g a (ASort O n))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (n: nat).(\lambda (a: A).(\lambda 
(H: (arity g c (TSort n) a)).(insert_eq T (TSort n) (\lambda (t: T).(arity g 
c t a)) (\lambda (_: T).(leq g a (ASort O n))) (\lambda (y: T).(\lambda (H0: 
(arity g c y a)).(arity_ind g (\lambda (_: C).(\lambda (t: T).(\lambda (a0: 
A).((eq T t (TSort n)) \to (leq g a0 (ASort O n)))))) (\lambda (_: 
C).(\lambda (n0: nat).(\lambda (H1: (eq T (TSort n0) (TSort n))).(let H2 \def 
(f_equal T nat (\lambda (e: T).(match e in T return (\lambda (_: T).nat) with 
[(TSort n1) \Rightarrow n1 | (TLRef _) \Rightarrow n0 | (THead _ _ _) 
\Rightarrow n0])) (TSort n0) (TSort n) H1) in (eq_ind_r nat n (\lambda (n1: 
nat).(leq g (ASort O n1) (ASort O n))) (leq_refl g (ASort O n)) n0 H2))))) 
(\lambda (c0: C).(\lambda (d: C).(\lambda (u: T).(\lambda (i: nat).(\lambda 
(_: (getl i c0 (CHead d (Bind Abbr) u))).(\lambda (a0: A).(\lambda (_: (arity 
g d u a0)).(\lambda (_: (((eq T u (TSort n)) \to (leq g a0 (ASort O 
n))))).(\lambda (H4: (eq T (TLRef i) (TSort n))).(let H5 \def (eq_ind T 
(TLRef i) (\lambda (ee: T).(match ee in T return (\lambda (_: T).Prop) with 
[(TSort _) \Rightarrow False | (TLRef _) \Rightarrow True | (THead _ _ _) 
\Rightarrow False])) I (TSort n) H4) in (False_ind (leq g a0 (ASort O n)) 
H5))))))))))) (\lambda (c0: C).(\lambda (d: C).(\lambda (u: T).(\lambda (i: 
nat).(\lambda (_: (getl i c0 (CHead d (Bind Abst) u))).(\lambda (a0: 
A).(\lambda (_: (arity g d u (asucc g a0))).(\lambda (_: (((eq T u (TSort n)) 
\to (leq g (asucc g a0) (ASort O n))))).(\lambda (H4: (eq T (TLRef i) (TSort 
n))).(let H5 \def (eq_ind T (TLRef i) (\lambda (ee: T).(match ee in T return 
(\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow True | (THead _ _ _) \Rightarrow False])) I (TSort n) H4) in 
(False_ind (leq g a0 (ASort O n)) H5))))))))))) (\lambda (b: B).(\lambda (_: 
(not (eq B b Abst))).(\lambda (c0: C).(\lambda (u: T).(\lambda (a1: 
A).(\lambda (_: (arity g c0 u a1)).(\lambda (_: (((eq T u (TSort n)) \to (leq 
g a1 (ASort O n))))).(\lambda (t: T).(\lambda (a2: A).(\lambda (_: (arity g 
(CHead c0 (Bind b) u) t a2)).(\lambda (_: (((eq T t (TSort n)) \to (leq g a2 
(ASort O n))))).(\lambda (H6: (eq T (THead (Bind b) u t) (TSort n))).(let H7 
\def (eq_ind T (THead (Bind b) u t) (\lambda (ee: T).(match ee in T return 
(\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow False | (THead _ _ _) \Rightarrow True])) I (TSort n) H6) in 
(False_ind (leq g a2 (ASort O n)) H7)))))))))))))) (\lambda (c0: C).(\lambda 
(u: T).(\lambda (a1: A).(\lambda (_: (arity g c0 u (asucc g a1))).(\lambda 
(_: (((eq T u (TSort n)) \to (leq g (asucc g a1) (ASort O n))))).(\lambda (t: 
T).(\lambda (a2: A).(\lambda (_: (arity g (CHead c0 (Bind Abst) u) t 
a2)).(\lambda (_: (((eq T t (TSort n)) \to (leq g a2 (ASort O n))))).(\lambda 
(H5: (eq T (THead (Bind Abst) u t) (TSort n))).(let H6 \def (eq_ind T (THead 
(Bind Abst) u t) (\lambda (ee: T).(match ee in T return (\lambda (_: T).Prop) 
with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | (THead _ _ 
_) \Rightarrow True])) I (TSort n) H5) in (False_ind (leq g (AHead a1 a2) 
(ASort O n)) H6)))))))))))) (\lambda (c0: C).(\lambda (u: T).(\lambda (a1: 
A).(\lambda (_: (arity g c0 u a1)).(\lambda (_: (((eq T u (TSort n)) \to (leq 
g a1 (ASort O n))))).(\lambda (t: T).(\lambda (a2: A).(\lambda (_: (arity g 
c0 t (AHead a1 a2))).(\lambda (_: (((eq T t (TSort n)) \to (leq g (AHead a1 
a2) (ASort O n))))).(\lambda (H5: (eq T (THead (Flat Appl) u t) (TSort 
n))).(let H6 \def (eq_ind T (THead (Flat Appl) u t) (\lambda (ee: T).(match 
ee in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | 
(TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow True])) I (TSort n) 
H5) in (False_ind (leq g a2 (ASort O n)) H6)))))))))))) (\lambda (c0: 
C).(\lambda (u: T).(\lambda (a0: A).(\lambda (_: (arity g c0 u (asucc g 
a0))).(\lambda (_: (((eq T u (TSort n)) \to (leq g (asucc g a0) (ASort O 
n))))).(\lambda (t: T).(\lambda (_: (arity g c0 t a0)).(\lambda (_: (((eq T t 
(TSort n)) \to (leq g a0 (ASort O n))))).(\lambda (H5: (eq T (THead (Flat 
Cast) u t) (TSort n))).(let H6 \def (eq_ind T (THead (Flat Cast) u t) 
(\lambda (ee: T).(match ee in T return (\lambda (_: T).Prop) with [(TSort _) 
\Rightarrow False | (TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow 
True])) I (TSort n) H5) in (False_ind (leq g a0 (ASort O n)) H6))))))))))) 
(\lambda (c0: C).(\lambda (t: T).(\lambda (a1: A).(\lambda (H1: (arity g c0 t 
a1)).(\lambda (H2: (((eq T t (TSort n)) \to (leq g a1 (ASort O 
n))))).(\lambda (a2: A).(\lambda (H3: (leq g a1 a2)).(\lambda (H4: (eq T t 
(TSort n))).(let H5 \def (f_equal T T (\lambda (e: T).e) t (TSort n) H4) in 
(let H6 \def (eq_ind T t (\lambda (t0: T).((eq T t0 (TSort n)) \to (leq g a1 
(ASort O n)))) H2 (TSort n) H5) in (let H7 \def (eq_ind T t (\lambda (t0: 
T).(arity g c0 t0 a1)) H1 (TSort n) H5) in (leq_trans g a2 a1 (leq_sym g a1 
a2 H3) (ASort O n) (H6 (refl_equal T (TSort n))))))))))))))) c y a H0))) 
H))))).
(* COMMENTS
Initial nodes: 1235
END *)

theorem arity_gen_lref:
 \forall (g: G).(\forall (c: C).(\forall (i: nat).(\forall (a: A).((arity g c 
(TLRef i) a) \to (or (ex2_2 C T (\lambda (d: C).(\lambda (u: T).(getl i c 
(CHead d (Bind Abbr) u)))) (\lambda (d: C).(\lambda (u: T).(arity g d u a)))) 
(ex2_2 C T (\lambda (d: C).(\lambda (u: T).(getl i c (CHead d (Bind Abst) 
u)))) (\lambda (d: C).(\lambda (u: T).(arity g d u (asucc g a))))))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (i: nat).(\lambda (a: A).(\lambda 
(H: (arity g c (TLRef i) a)).(insert_eq T (TLRef i) (\lambda (t: T).(arity g 
c t a)) (\lambda (_: T).(or (ex2_2 C T (\lambda (d: C).(\lambda (u: T).(getl 
i c (CHead d (Bind Abbr) u)))) (\lambda (d: C).(\lambda (u: T).(arity g d u 
a)))) (ex2_2 C T (\lambda (d: C).(\lambda (u: T).(getl i c (CHead d (Bind 
Abst) u)))) (\lambda (d: C).(\lambda (u: T).(arity g d u (asucc g a))))))) 
(\lambda (y: T).(\lambda (H0: (arity g c y a)).(arity_ind g (\lambda (c0: 
C).(\lambda (t: T).(\lambda (a0: A).((eq T t (TLRef i)) \to (or (ex2_2 C T 
(\lambda (d: C).(\lambda (u: T).(getl i c0 (CHead d (Bind Abbr) u)))) 
(\lambda (d: C).(\lambda (u: T).(arity g d u a0)))) (ex2_2 C T (\lambda (d: 
C).(\lambda (u: T).(getl i c0 (CHead d (Bind Abst) u)))) (\lambda (d: 
C).(\lambda (u: T).(arity g d u (asucc g a0)))))))))) (\lambda (c0: 
C).(\lambda (n: nat).(\lambda (H1: (eq T (TSort n) (TLRef i))).(let H2 \def 
(eq_ind T (TSort n) (\lambda (ee: T).(match ee in T return (\lambda (_: 
T).Prop) with [(TSort _) \Rightarrow True | (TLRef _) \Rightarrow False | 
(THead _ _ _) \Rightarrow False])) I (TLRef i) H1) in (False_ind (or (ex2_2 C 
T (\lambda (d: C).(\lambda (u: T).(getl i c0 (CHead d (Bind Abbr) u)))) 
(\lambda (d: C).(\lambda (u: T).(arity g d u (ASort O n))))) (ex2_2 C T 
(\lambda (d: C).(\lambda (u: T).(getl i c0 (CHead d (Bind Abst) u)))) 
(\lambda (d: C).(\lambda (u: T).(arity g d u (asucc g (ASort O n))))))) 
H2))))) (\lambda (c0: C).(\lambda (d: C).(\lambda (u: T).(\lambda (i0: 
nat).(\lambda (H1: (getl i0 c0 (CHead d (Bind Abbr) u))).(\lambda (a0: 
A).(\lambda (H2: (arity g d u a0)).(\lambda (_: (((eq T u (TLRef i)) \to (or 
(ex2_2 C T (\lambda (d0: C).(\lambda (u0: T).(getl i d (CHead d0 (Bind Abbr) 
u0)))) (\lambda (d0: C).(\lambda (u0: T).(arity g d0 u0 a0)))) (ex2_2 C T 
(\lambda (d0: C).(\lambda (u0: T).(getl i d (CHead d0 (Bind Abst) u0)))) 
(\lambda (d0: C).(\lambda (u0: T).(arity g d0 u0 (asucc g 
a0))))))))).(\lambda (H4: (eq T (TLRef i0) (TLRef i))).(let H5 \def (f_equal 
T nat (\lambda (e: T).(match e in T return (\lambda (_: T).nat) with [(TSort 
_) \Rightarrow i0 | (TLRef n) \Rightarrow n | (THead _ _ _) \Rightarrow i0])) 
(TLRef i0) (TLRef i) H4) in (let H6 \def (eq_ind nat i0 (\lambda (n: 
nat).(getl n c0 (CHead d (Bind Abbr) u))) H1 i H5) in (or_introl (ex2_2 C T 
(\lambda (d0: C).(\lambda (u0: T).(getl i c0 (CHead d0 (Bind Abbr) u0)))) 
(\lambda (d0: C).(\lambda (u0: T).(arity g d0 u0 a0)))) (ex2_2 C T (\lambda 
(d0: C).(\lambda (u0: T).(getl i c0 (CHead d0 (Bind Abst) u0)))) (\lambda 
(d0: C).(\lambda (u0: T).(arity g d0 u0 (asucc g a0))))) (ex2_2_intro C T 
(\lambda (d0: C).(\lambda (u0: T).(getl i c0 (CHead d0 (Bind Abbr) u0)))) 
(\lambda (d0: C).(\lambda (u0: T).(arity g d0 u0 a0))) d u H6 H2))))))))))))) 
(\lambda (c0: C).(\lambda (d: C).(\lambda (u: T).(\lambda (i0: nat).(\lambda 
(H1: (getl i0 c0 (CHead d (Bind Abst) u))).(\lambda (a0: A).(\lambda (H2: 
(arity g d u (asucc g a0))).(\lambda (_: (((eq T u (TLRef i)) \to (or (ex2_2 
C T (\lambda (d0: C).(\lambda (u0: T).(getl i d (CHead d0 (Bind Abbr) u0)))) 
(\lambda (d0: C).(\lambda (u0: T).(arity g d0 u0 (asucc g a0))))) (ex2_2 C T 
(\lambda (d0: C).(\lambda (u0: T).(getl i d (CHead d0 (Bind Abst) u0)))) 
(\lambda (d0: C).(\lambda (u0: T).(arity g d0 u0 (asucc g (asucc g 
a0)))))))))).(\lambda (H4: (eq T (TLRef i0) (TLRef i))).(let H5 \def (f_equal 
T nat (\lambda (e: T).(match e in T return (\lambda (_: T).nat) with [(TSort 
_) \Rightarrow i0 | (TLRef n) \Rightarrow n | (THead _ _ _) \Rightarrow i0])) 
(TLRef i0) (TLRef i) H4) in (let H6 \def (eq_ind nat i0 (\lambda (n: 
nat).(getl n c0 (CHead d (Bind Abst) u))) H1 i H5) in (or_intror (ex2_2 C T 
(\lambda (d0: C).(\lambda (u0: T).(getl i c0 (CHead d0 (Bind Abbr) u0)))) 
(\lambda (d0: C).(\lambda (u0: T).(arity g d0 u0 a0)))) (ex2_2 C T (\lambda 
(d0: C).(\lambda (u0: T).(getl i c0 (CHead d0 (Bind Abst) u0)))) (\lambda 
(d0: C).(\lambda (u0: T).(arity g d0 u0 (asucc g a0))))) (ex2_2_intro C T 
(\lambda (d0: C).(\lambda (u0: T).(getl i c0 (CHead d0 (Bind Abst) u0)))) 
(\lambda (d0: C).(\lambda (u0: T).(arity g d0 u0 (asucc g a0)))) d u H6 
H2))))))))))))) (\lambda (b: B).(\lambda (_: (not (eq B b Abst))).(\lambda 
(c0: C).(\lambda (u: T).(\lambda (a1: A).(\lambda (_: (arity g c0 u 
a1)).(\lambda (_: (((eq T u (TLRef i)) \to (or (ex2_2 C T (\lambda (d: 
C).(\lambda (u0: T).(getl i c0 (CHead d (Bind Abbr) u0)))) (\lambda (d: 
C).(\lambda (u0: T).(arity g d u0 a1)))) (ex2_2 C T (\lambda (d: C).(\lambda 
(u0: T).(getl i c0 (CHead d (Bind Abst) u0)))) (\lambda (d: C).(\lambda (u0: 
T).(arity g d u0 (asucc g a1))))))))).(\lambda (t: T).(\lambda (a2: 
A).(\lambda (_: (arity g (CHead c0 (Bind b) u) t a2)).(\lambda (_: (((eq T t 
(TLRef i)) \to (or (ex2_2 C T (\lambda (d: C).(\lambda (u0: T).(getl i (CHead 
c0 (Bind b) u) (CHead d (Bind Abbr) u0)))) (\lambda (d: C).(\lambda (u0: 
T).(arity g d u0 a2)))) (ex2_2 C T (\lambda (d: C).(\lambda (u0: T).(getl i 
(CHead c0 (Bind b) u) (CHead d (Bind Abst) u0)))) (\lambda (d: C).(\lambda 
(u0: T).(arity g d u0 (asucc g a2))))))))).(\lambda (H6: (eq T (THead (Bind 
b) u t) (TLRef i))).(let H7 \def (eq_ind T (THead (Bind b) u t) (\lambda (ee: 
T).(match ee in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow 
False | (TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow True])) I 
(TLRef i) H6) in (False_ind (or (ex2_2 C T (\lambda (d: C).(\lambda (u0: 
T).(getl i c0 (CHead d (Bind Abbr) u0)))) (\lambda (d: C).(\lambda (u0: 
T).(arity g d u0 a2)))) (ex2_2 C T (\lambda (d: C).(\lambda (u0: T).(getl i 
c0 (CHead d (Bind Abst) u0)))) (\lambda (d: C).(\lambda (u0: T).(arity g d u0 
(asucc g a2)))))) H7)))))))))))))) (\lambda (c0: C).(\lambda (u: T).(\lambda 
(a1: A).(\lambda (_: (arity g c0 u (asucc g a1))).(\lambda (_: (((eq T u 
(TLRef i)) \to (or (ex2_2 C T (\lambda (d: C).(\lambda (u0: T).(getl i c0 
(CHead d (Bind Abbr) u0)))) (\lambda (d: C).(\lambda (u0: T).(arity g d u0 
(asucc g a1))))) (ex2_2 C T (\lambda (d: C).(\lambda (u0: T).(getl i c0 
(CHead d (Bind Abst) u0)))) (\lambda (d: C).(\lambda (u0: T).(arity g d u0 
(asucc g (asucc g a1)))))))))).(\lambda (t: T).(\lambda (a2: A).(\lambda (_: 
(arity g (CHead c0 (Bind Abst) u) t a2)).(\lambda (_: (((eq T t (TLRef i)) 
\to (or (ex2_2 C T (\lambda (d: C).(\lambda (u0: T).(getl i (CHead c0 (Bind 
Abst) u) (CHead d (Bind Abbr) u0)))) (\lambda (d: C).(\lambda (u0: T).(arity 
g d u0 a2)))) (ex2_2 C T (\lambda (d: C).(\lambda (u0: T).(getl i (CHead c0 
(Bind Abst) u) (CHead d (Bind Abst) u0)))) (\lambda (d: C).(\lambda (u0: 
T).(arity g d u0 (asucc g a2))))))))).(\lambda (H5: (eq T (THead (Bind Abst) 
u t) (TLRef i))).(let H6 \def (eq_ind T (THead (Bind Abst) u t) (\lambda (ee: 
T).(match ee in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow 
False | (TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow True])) I 
(TLRef i) H5) in (False_ind (or (ex2_2 C T (\lambda (d: C).(\lambda (u0: 
T).(getl i c0 (CHead d (Bind Abbr) u0)))) (\lambda (d: C).(\lambda (u0: 
T).(arity g d u0 (AHead a1 a2))))) (ex2_2 C T (\lambda (d: C).(\lambda (u0: 
T).(getl i c0 (CHead d (Bind Abst) u0)))) (\lambda (d: C).(\lambda (u0: 
T).(arity g d u0 (asucc g (AHead a1 a2))))))) H6)))))))))))) (\lambda (c0: 
C).(\lambda (u: T).(\lambda (a1: A).(\lambda (_: (arity g c0 u a1)).(\lambda 
(_: (((eq T u (TLRef i)) \to (or (ex2_2 C T (\lambda (d: C).(\lambda (u0: 
T).(getl i c0 (CHead d (Bind Abbr) u0)))) (\lambda (d: C).(\lambda (u0: 
T).(arity g d u0 a1)))) (ex2_2 C T (\lambda (d: C).(\lambda (u0: T).(getl i 
c0 (CHead d (Bind Abst) u0)))) (\lambda (d: C).(\lambda (u0: T).(arity g d u0 
(asucc g a1))))))))).(\lambda (t: T).(\lambda (a2: A).(\lambda (_: (arity g 
c0 t (AHead a1 a2))).(\lambda (_: (((eq T t (TLRef i)) \to (or (ex2_2 C T 
(\lambda (d: C).(\lambda (u0: T).(getl i c0 (CHead d (Bind Abbr) u0)))) 
(\lambda (d: C).(\lambda (u0: T).(arity g d u0 (AHead a1 a2))))) (ex2_2 C T 
(\lambda (d: C).(\lambda (u0: T).(getl i c0 (CHead d (Bind Abst) u0)))) 
(\lambda (d: C).(\lambda (u0: T).(arity g d u0 (asucc g (AHead a1 
a2)))))))))).(\lambda (H5: (eq T (THead (Flat Appl) u t) (TLRef i))).(let H6 
\def (eq_ind T (THead (Flat Appl) u t) (\lambda (ee: T).(match ee in T return 
(\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow False | (THead _ _ _) \Rightarrow True])) I (TLRef i) H5) in 
(False_ind (or (ex2_2 C T (\lambda (d: C).(\lambda (u0: T).(getl i c0 (CHead 
d (Bind Abbr) u0)))) (\lambda (d: C).(\lambda (u0: T).(arity g d u0 a2)))) 
(ex2_2 C T (\lambda (d: C).(\lambda (u0: T).(getl i c0 (CHead d (Bind Abst) 
u0)))) (\lambda (d: C).(\lambda (u0: T).(arity g d u0 (asucc g a2)))))) 
H6)))))))))))) (\lambda (c0: C).(\lambda (u: T).(\lambda (a0: A).(\lambda (_: 
(arity g c0 u (asucc g a0))).(\lambda (_: (((eq T u (TLRef i)) \to (or (ex2_2 
C T (\lambda (d: C).(\lambda (u0: T).(getl i c0 (CHead d (Bind Abbr) u0)))) 
(\lambda (d: C).(\lambda (u0: T).(arity g d u0 (asucc g a0))))) (ex2_2 C T 
(\lambda (d: C).(\lambda (u0: T).(getl i c0 (CHead d (Bind Abst) u0)))) 
(\lambda (d: C).(\lambda (u0: T).(arity g d u0 (asucc g (asucc g 
a0)))))))))).(\lambda (t: T).(\lambda (_: (arity g c0 t a0)).(\lambda (_: 
(((eq T t (TLRef i)) \to (or (ex2_2 C T (\lambda (d: C).(\lambda (u0: 
T).(getl i c0 (CHead d (Bind Abbr) u0)))) (\lambda (d: C).(\lambda (u0: 
T).(arity g d u0 a0)))) (ex2_2 C T (\lambda (d: C).(\lambda (u0: T).(getl i 
c0 (CHead d (Bind Abst) u0)))) (\lambda (d: C).(\lambda (u0: T).(arity g d u0 
(asucc g a0))))))))).(\lambda (H5: (eq T (THead (Flat Cast) u t) (TLRef 
i))).(let H6 \def (eq_ind T (THead (Flat Cast) u t) (\lambda (ee: T).(match 
ee in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | 
(TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow True])) I (TLRef i) 
H5) in (False_ind (or (ex2_2 C T (\lambda (d: C).(\lambda (u0: T).(getl i c0 
(CHead d (Bind Abbr) u0)))) (\lambda (d: C).(\lambda (u0: T).(arity g d u0 
a0)))) (ex2_2 C T (\lambda (d: C).(\lambda (u0: T).(getl i c0 (CHead d (Bind 
Abst) u0)))) (\lambda (d: C).(\lambda (u0: T).(arity g d u0 (asucc g a0)))))) 
H6))))))))))) (\lambda (c0: C).(\lambda (t: T).(\lambda (a1: A).(\lambda (H1: 
(arity g c0 t a1)).(\lambda (H2: (((eq T t (TLRef i)) \to (or (ex2_2 C T 
(\lambda (d: C).(\lambda (u: T).(getl i c0 (CHead d (Bind Abbr) u)))) 
(\lambda (d: C).(\lambda (u: T).(arity g d u a1)))) (ex2_2 C T (\lambda (d: 
C).(\lambda (u: T).(getl i c0 (CHead d (Bind Abst) u)))) (\lambda (d: 
C).(\lambda (u: T).(arity g d u (asucc g a1))))))))).(\lambda (a2: 
A).(\lambda (H3: (leq g a1 a2)).(\lambda (H4: (eq T t (TLRef i))).(let H5 
\def (f_equal T T (\lambda (e: T).e) t (TLRef i) H4) in (let H6 \def (eq_ind 
T t (\lambda (t0: T).((eq T t0 (TLRef i)) \to (or (ex2_2 C T (\lambda (d: 
C).(\lambda (u: T).(getl i c0 (CHead d (Bind Abbr) u)))) (\lambda (d: 
C).(\lambda (u: T).(arity g d u a1)))) (ex2_2 C T (\lambda (d: C).(\lambda 
(u: T).(getl i c0 (CHead d (Bind Abst) u)))) (\lambda (d: C).(\lambda (u: 
T).(arity g d u (asucc g a1)))))))) H2 (TLRef i) H5) in (let H7 \def (eq_ind 
T t (\lambda (t0: T).(arity g c0 t0 a1)) H1 (TLRef i) H5) in (let H8 \def (H6 
(refl_equal T (TLRef i))) in (or_ind (ex2_2 C T (\lambda (d: C).(\lambda (u: 
T).(getl i c0 (CHead d (Bind Abbr) u)))) (\lambda (d: C).(\lambda (u: 
T).(arity g d u a1)))) (ex2_2 C T (\lambda (d: C).(\lambda (u: T).(getl i c0 
(CHead d (Bind Abst) u)))) (\lambda (d: C).(\lambda (u: T).(arity g d u 
(asucc g a1))))) (or (ex2_2 C T (\lambda (d: C).(\lambda (u: T).(getl i c0 
(CHead d (Bind Abbr) u)))) (\lambda (d: C).(\lambda (u: T).(arity g d u 
a2)))) (ex2_2 C T (\lambda (d: C).(\lambda (u: T).(getl i c0 (CHead d (Bind 
Abst) u)))) (\lambda (d: C).(\lambda (u: T).(arity g d u (asucc g a2)))))) 
(\lambda (H9: (ex2_2 C T (\lambda (d: C).(\lambda (u: T).(getl i c0 (CHead d 
(Bind Abbr) u)))) (\lambda (d: C).(\lambda (u: T).(arity g d u 
a1))))).(ex2_2_ind C T (\lambda (d: C).(\lambda (u: T).(getl i c0 (CHead d 
(Bind Abbr) u)))) (\lambda (d: C).(\lambda (u: T).(arity g d u a1))) (or 
(ex2_2 C T (\lambda (d: C).(\lambda (u: T).(getl i c0 (CHead d (Bind Abbr) 
u)))) (\lambda (d: C).(\lambda (u: T).(arity g d u a2)))) (ex2_2 C T (\lambda 
(d: C).(\lambda (u: T).(getl i c0 (CHead d (Bind Abst) u)))) (\lambda (d: 
C).(\lambda (u: T).(arity g d u (asucc g a2)))))) (\lambda (x0: C).(\lambda 
(x1: T).(\lambda (H10: (getl i c0 (CHead x0 (Bind Abbr) x1))).(\lambda (H11: 
(arity g x0 x1 a1)).(or_introl (ex2_2 C T (\lambda (d: C).(\lambda (u: 
T).(getl i c0 (CHead d (Bind Abbr) u)))) (\lambda (d: C).(\lambda (u: 
T).(arity g d u a2)))) (ex2_2 C T (\lambda (d: C).(\lambda (u: T).(getl i c0 
(CHead d (Bind Abst) u)))) (\lambda (d: C).(\lambda (u: T).(arity g d u 
(asucc g a2))))) (ex2_2_intro C T (\lambda (d: C).(\lambda (u: T).(getl i c0 
(CHead d (Bind Abbr) u)))) (\lambda (d: C).(\lambda (u: T).(arity g d u a2))) 
x0 x1 H10 (arity_repl g x0 x1 a1 H11 a2 H3))))))) H9)) (\lambda (H9: (ex2_2 C 
T (\lambda (d: C).(\lambda (u: T).(getl i c0 (CHead d (Bind Abst) u)))) 
(\lambda (d: C).(\lambda (u: T).(arity g d u (asucc g a1)))))).(ex2_2_ind C T 
(\lambda (d: C).(\lambda (u: T).(getl i c0 (CHead d (Bind Abst) u)))) 
(\lambda (d: C).(\lambda (u: T).(arity g d u (asucc g a1)))) (or (ex2_2 C T 
(\lambda (d: C).(\lambda (u: T).(getl i c0 (CHead d (Bind Abbr) u)))) 
(\lambda (d: C).(\lambda (u: T).(arity g d u a2)))) (ex2_2 C T (\lambda (d: 
C).(\lambda (u: T).(getl i c0 (CHead d (Bind Abst) u)))) (\lambda (d: 
C).(\lambda (u: T).(arity g d u (asucc g a2)))))) (\lambda (x0: C).(\lambda 
(x1: T).(\lambda (H10: (getl i c0 (CHead x0 (Bind Abst) x1))).(\lambda (H11: 
(arity g x0 x1 (asucc g a1))).(or_intror (ex2_2 C T (\lambda (d: C).(\lambda 
(u: T).(getl i c0 (CHead d (Bind Abbr) u)))) (\lambda (d: C).(\lambda (u: 
T).(arity g d u a2)))) (ex2_2 C T (\lambda (d: C).(\lambda (u: T).(getl i c0 
(CHead d (Bind Abst) u)))) (\lambda (d: C).(\lambda (u: T).(arity g d u 
(asucc g a2))))) (ex2_2_intro C T (\lambda (d: C).(\lambda (u: T).(getl i c0 
(CHead d (Bind Abst) u)))) (\lambda (d: C).(\lambda (u: T).(arity g d u 
(asucc g a2)))) x0 x1 H10 (arity_repl g x0 x1 (asucc g a1) H11 (asucc g a2) 
(asucc_repl g a1 a2 H3)))))))) H9)) H8))))))))))))) c y a H0))) H))))).
(* COMMENTS
Initial nodes: 3853
END *)

theorem arity_gen_bind:
 \forall (b: B).((not (eq B b Abst)) \to (\forall (g: G).(\forall (c: 
C).(\forall (u: T).(\forall (t: T).(\forall (a2: A).((arity g c (THead (Bind 
b) u t) a2) \to (ex2 A (\lambda (a1: A).(arity g c u a1)) (\lambda (_: 
A).(arity g (CHead c (Bind b) u) t a2))))))))))
\def
 \lambda (b: B).(\lambda (H: (not (eq B b Abst))).(\lambda (g: G).(\lambda 
(c: C).(\lambda (u: T).(\lambda (t: T).(\lambda (a2: A).(\lambda (H0: (arity 
g c (THead (Bind b) u t) a2)).(insert_eq T (THead (Bind b) u t) (\lambda (t0: 
T).(arity g c t0 a2)) (\lambda (_: T).(ex2 A (\lambda (a1: A).(arity g c u 
a1)) (\lambda (_: A).(arity g (CHead c (Bind b) u) t a2)))) (\lambda (y: 
T).(\lambda (H1: (arity g c y a2)).(arity_ind g (\lambda (c0: C).(\lambda 
(t0: T).(\lambda (a: A).((eq T t0 (THead (Bind b) u t)) \to (ex2 A (\lambda 
(a1: A).(arity g c0 u a1)) (\lambda (_: A).(arity g (CHead c0 (Bind b) u) t 
a))))))) (\lambda (c0: C).(\lambda (n: nat).(\lambda (H2: (eq T (TSort n) 
(THead (Bind b) u t))).(let H3 \def (eq_ind T (TSort n) (\lambda (ee: 
T).(match ee in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow 
True | (TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow False])) I 
(THead (Bind b) u t) H2) in (False_ind (ex2 A (\lambda (a1: A).(arity g c0 u 
a1)) (\lambda (_: A).(arity g (CHead c0 (Bind b) u) t (ASort O n)))) H3))))) 
(\lambda (c0: C).(\lambda (d: C).(\lambda (u0: T).(\lambda (i: nat).(\lambda 
(_: (getl i c0 (CHead d (Bind Abbr) u0))).(\lambda (a: A).(\lambda (_: (arity 
g d u0 a)).(\lambda (_: (((eq T u0 (THead (Bind b) u t)) \to (ex2 A (\lambda 
(a1: A).(arity g d u a1)) (\lambda (_: A).(arity g (CHead d (Bind b) u) t 
a)))))).(\lambda (H5: (eq T (TLRef i) (THead (Bind b) u t))).(let H6 \def 
(eq_ind T (TLRef i) (\lambda (ee: T).(match ee in T return (\lambda (_: 
T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow True | 
(THead _ _ _) \Rightarrow False])) I (THead (Bind b) u t) H5) in (False_ind 
(ex2 A (\lambda (a1: A).(arity g c0 u a1)) (\lambda (_: A).(arity g (CHead c0 
(Bind b) u) t a))) H6))))))))))) (\lambda (c0: C).(\lambda (d: C).(\lambda 
(u0: T).(\lambda (i: nat).(\lambda (_: (getl i c0 (CHead d (Bind Abst) 
u0))).(\lambda (a: A).(\lambda (_: (arity g d u0 (asucc g a))).(\lambda (_: 
(((eq T u0 (THead (Bind b) u t)) \to (ex2 A (\lambda (a1: A).(arity g d u 
a1)) (\lambda (_: A).(arity g (CHead d (Bind b) u) t (asucc g 
a))))))).(\lambda (H5: (eq T (TLRef i) (THead (Bind b) u t))).(let H6 \def 
(eq_ind T (TLRef i) (\lambda (ee: T).(match ee in T return (\lambda (_: 
T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow True | 
(THead _ _ _) \Rightarrow False])) I (THead (Bind b) u t) H5) in (False_ind 
(ex2 A (\lambda (a1: A).(arity g c0 u a1)) (\lambda (_: A).(arity g (CHead c0 
(Bind b) u) t a))) H6))))))))))) (\lambda (b0: B).(\lambda (H2: (not (eq B b0 
Abst))).(\lambda (c0: C).(\lambda (u0: T).(\lambda (a1: A).(\lambda (H3: 
(arity g c0 u0 a1)).(\lambda (H4: (((eq T u0 (THead (Bind b) u t)) \to (ex2 A 
(\lambda (a3: A).(arity g c0 u a3)) (\lambda (_: A).(arity g (CHead c0 (Bind 
b) u) t a1)))))).(\lambda (t0: T).(\lambda (a0: A).(\lambda (H5: (arity g 
(CHead c0 (Bind b0) u0) t0 a0)).(\lambda (H6: (((eq T t0 (THead (Bind b) u 
t)) \to (ex2 A (\lambda (a3: A).(arity g (CHead c0 (Bind b0) u0) u a3)) 
(\lambda (_: A).(arity g (CHead (CHead c0 (Bind b0) u0) (Bind b) u) t 
a0)))))).(\lambda (H7: (eq T (THead (Bind b0) u0 t0) (THead (Bind b) u 
t))).(let H8 \def (f_equal T B (\lambda (e: T).(match e in T return (\lambda 
(_: T).B) with [(TSort _) \Rightarrow b0 | (TLRef _) \Rightarrow b0 | (THead 
k _ _) \Rightarrow (match k in K return (\lambda (_: K).B) with [(Bind b1) 
\Rightarrow b1 | (Flat _) \Rightarrow b0])])) (THead (Bind b0) u0 t0) (THead 
(Bind b) u t) H7) in ((let H9 \def (f_equal T T (\lambda (e: T).(match e in T 
return (\lambda (_: T).T) with [(TSort _) \Rightarrow u0 | (TLRef _) 
\Rightarrow u0 | (THead _ t1 _) \Rightarrow t1])) (THead (Bind b0) u0 t0) 
(THead (Bind b) u t) H7) in ((let H10 \def (f_equal T T (\lambda (e: 
T).(match e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow t0 | 
(TLRef _) \Rightarrow t0 | (THead _ _ t1) \Rightarrow t1])) (THead (Bind b0) 
u0 t0) (THead (Bind b) u t) H7) in (\lambda (H11: (eq T u0 u)).(\lambda (H12: 
(eq B b0 b)).(let H13 \def (eq_ind T t0 (\lambda (t1: T).((eq T t1 (THead 
(Bind b) u t)) \to (ex2 A (\lambda (a3: A).(arity g (CHead c0 (Bind b0) u0) u 
a3)) (\lambda (_: A).(arity g (CHead (CHead c0 (Bind b0) u0) (Bind b) u) t 
a0))))) H6 t H10) in (let H14 \def (eq_ind T t0 (\lambda (t1: T).(arity g 
(CHead c0 (Bind b0) u0) t1 a0)) H5 t H10) in (let H15 \def (eq_ind T u0 
(\lambda (t1: T).((eq T t (THead (Bind b) u t)) \to (ex2 A (\lambda (a3: 
A).(arity g (CHead c0 (Bind b0) t1) u a3)) (\lambda (_: A).(arity g (CHead 
(CHead c0 (Bind b0) t1) (Bind b) u) t a0))))) H13 u H11) in (let H16 \def 
(eq_ind T u0 (\lambda (t1: T).(arity g (CHead c0 (Bind b0) t1) t a0)) H14 u 
H11) in (let H17 \def (eq_ind T u0 (\lambda (t1: T).((eq T t1 (THead (Bind b) 
u t)) \to (ex2 A (\lambda (a3: A).(arity g c0 u a3)) (\lambda (_: A).(arity g 
(CHead c0 (Bind b) u) t a1))))) H4 u H11) in (let H18 \def (eq_ind T u0 
(\lambda (t1: T).(arity g c0 t1 a1)) H3 u H11) in (let H19 \def (eq_ind B b0 
(\lambda (b1: B).((eq T t (THead (Bind b) u t)) \to (ex2 A (\lambda (a3: 
A).(arity g (CHead c0 (Bind b1) u) u a3)) (\lambda (_: A).(arity g (CHead 
(CHead c0 (Bind b1) u) (Bind b) u) t a0))))) H15 b H12) in (let H20 \def 
(eq_ind B b0 (\lambda (b1: B).(arity g (CHead c0 (Bind b1) u) t a0)) H16 b 
H12) in (let H21 \def (eq_ind B b0 (\lambda (b1: B).(not (eq B b1 Abst))) H2 
b H12) in (ex_intro2 A (\lambda (a3: A).(arity g c0 u a3)) (\lambda (_: 
A).(arity g (CHead c0 (Bind b) u) t a0)) a1 H18 H20))))))))))))) H9)) 
H8)))))))))))))) (\lambda (c0: C).(\lambda (u0: T).(\lambda (a1: A).(\lambda 
(H2: (arity g c0 u0 (asucc g a1))).(\lambda (H3: (((eq T u0 (THead (Bind b) u 
t)) \to (ex2 A (\lambda (a3: A).(arity g c0 u a3)) (\lambda (_: A).(arity g 
(CHead c0 (Bind b) u) t (asucc g a1))))))).(\lambda (t0: T).(\lambda (a0: 
A).(\lambda (H4: (arity g (CHead c0 (Bind Abst) u0) t0 a0)).(\lambda (H5: 
(((eq T t0 (THead (Bind b) u t)) \to (ex2 A (\lambda (a3: A).(arity g (CHead 
c0 (Bind Abst) u0) u a3)) (\lambda (_: A).(arity g (CHead (CHead c0 (Bind 
Abst) u0) (Bind b) u) t a0)))))).(\lambda (H6: (eq T (THead (Bind Abst) u0 
t0) (THead (Bind b) u t))).(let H7 \def (f_equal T B (\lambda (e: T).(match e 
in T return (\lambda (_: T).B) with [(TSort _) \Rightarrow Abst | (TLRef _) 
\Rightarrow Abst | (THead k _ _) \Rightarrow (match k in K return (\lambda 
(_: K).B) with [(Bind b0) \Rightarrow b0 | (Flat _) \Rightarrow Abst])])) 
(THead (Bind Abst) u0 t0) (THead (Bind b) u t) H6) in ((let H8 \def (f_equal 
T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) with [(TSort _) 
\Rightarrow u0 | (TLRef _) \Rightarrow u0 | (THead _ t1 _) \Rightarrow t1])) 
(THead (Bind Abst) u0 t0) (THead (Bind b) u t) H6) in ((let H9 \def (f_equal 
T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) with [(TSort _) 
\Rightarrow t0 | (TLRef _) \Rightarrow t0 | (THead _ _ t1) \Rightarrow t1])) 
(THead (Bind Abst) u0 t0) (THead (Bind b) u t) H6) in (\lambda (H10: (eq T u0 
u)).(\lambda (H11: (eq B Abst b)).(let H12 \def (eq_ind T t0 (\lambda (t1: 
T).((eq T t1 (THead (Bind b) u t)) \to (ex2 A (\lambda (a3: A).(arity g 
(CHead c0 (Bind Abst) u0) u a3)) (\lambda (_: A).(arity g (CHead (CHead c0 
(Bind Abst) u0) (Bind b) u) t a0))))) H5 t H9) in (let H13 \def (eq_ind T t0 
(\lambda (t1: T).(arity g (CHead c0 (Bind Abst) u0) t1 a0)) H4 t H9) in (let 
H14 \def (eq_ind T u0 (\lambda (t1: T).((eq T t (THead (Bind b) u t)) \to 
(ex2 A (\lambda (a3: A).(arity g (CHead c0 (Bind Abst) t1) u a3)) (\lambda 
(_: A).(arity g (CHead (CHead c0 (Bind Abst) t1) (Bind b) u) t a0))))) H12 u 
H10) in (let H15 \def (eq_ind T u0 (\lambda (t1: T).(arity g (CHead c0 (Bind 
Abst) t1) t a0)) H13 u H10) in (let H16 \def (eq_ind T u0 (\lambda (t1: 
T).((eq T t1 (THead (Bind b) u t)) \to (ex2 A (\lambda (a3: A).(arity g c0 u 
a3)) (\lambda (_: A).(arity g (CHead c0 (Bind b) u) t (asucc g a1)))))) H3 u 
H10) in (let H17 \def (eq_ind T u0 (\lambda (t1: T).(arity g c0 t1 (asucc g 
a1))) H2 u H10) in (let H18 \def (eq_ind_r B b (\lambda (b0: B).((eq T t 
(THead (Bind b0) u t)) \to (ex2 A (\lambda (a3: A).(arity g (CHead c0 (Bind 
Abst) u) u a3)) (\lambda (_: A).(arity g (CHead (CHead c0 (Bind Abst) u) 
(Bind b0) u) t a0))))) H14 Abst H11) in (let H19 \def (eq_ind_r B b (\lambda 
(b0: B).((eq T u (THead (Bind b0) u t)) \to (ex2 A (\lambda (a3: A).(arity g 
c0 u a3)) (\lambda (_: A).(arity g (CHead c0 (Bind b0) u) t (asucc g a1)))))) 
H16 Abst H11) in (let H20 \def (eq_ind_r B b (\lambda (b0: B).(not (eq B b0 
Abst))) H Abst H11) in (eq_ind B Abst (\lambda (b0: B).(ex2 A (\lambda (a3: 
A).(arity g c0 u a3)) (\lambda (_: A).(arity g (CHead c0 (Bind b0) u) t 
(AHead a1 a0))))) (let H21 \def (match (H20 (refl_equal B Abst)) in False 
return (\lambda (_: False).(ex2 A (\lambda (a3: A).(arity g c0 u a3)) 
(\lambda (_: A).(arity g (CHead c0 (Bind Abst) u) t (AHead a1 a0))))) with 
[]) in H21) b H11))))))))))))) H8)) H7)))))))))))) (\lambda (c0: C).(\lambda 
(u0: T).(\lambda (a1: A).(\lambda (_: (arity g c0 u0 a1)).(\lambda (_: (((eq 
T u0 (THead (Bind b) u t)) \to (ex2 A (\lambda (a3: A).(arity g c0 u a3)) 
(\lambda (_: A).(arity g (CHead c0 (Bind b) u) t a1)))))).(\lambda (t0: 
T).(\lambda (a0: A).(\lambda (_: (arity g c0 t0 (AHead a1 a0))).(\lambda (_: 
(((eq T t0 (THead (Bind b) u t)) \to (ex2 A (\lambda (a3: A).(arity g c0 u 
a3)) (\lambda (_: A).(arity g (CHead c0 (Bind b) u) t (AHead a1 
a0))))))).(\lambda (H6: (eq T (THead (Flat Appl) u0 t0) (THead (Bind b) u 
t))).(let H7 \def (eq_ind T (THead (Flat Appl) u0 t0) (\lambda (ee: T).(match 
ee in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | 
(TLRef _) \Rightarrow False | (THead k _ _) \Rightarrow (match k in K return 
(\lambda (_: K).Prop) with [(Bind _) \Rightarrow False | (Flat _) \Rightarrow 
True])])) I (THead (Bind b) u t) H6) in (False_ind (ex2 A (\lambda (a3: 
A).(arity g c0 u a3)) (\lambda (_: A).(arity g (CHead c0 (Bind b) u) t a0))) 
H7)))))))))))) (\lambda (c0: C).(\lambda (u0: T).(\lambda (a: A).(\lambda (_: 
(arity g c0 u0 (asucc g a))).(\lambda (_: (((eq T u0 (THead (Bind b) u t)) 
\to (ex2 A (\lambda (a1: A).(arity g c0 u a1)) (\lambda (_: A).(arity g 
(CHead c0 (Bind b) u) t (asucc g a))))))).(\lambda (t0: T).(\lambda (_: 
(arity g c0 t0 a)).(\lambda (_: (((eq T t0 (THead (Bind b) u t)) \to (ex2 A 
(\lambda (a1: A).(arity g c0 u a1)) (\lambda (_: A).(arity g (CHead c0 (Bind 
b) u) t a)))))).(\lambda (H6: (eq T (THead (Flat Cast) u0 t0) (THead (Bind b) 
u t))).(let H7 \def (eq_ind T (THead (Flat Cast) u0 t0) (\lambda (ee: 
T).(match ee in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow 
False | (TLRef _) \Rightarrow False | (THead k _ _) \Rightarrow (match k in K 
return (\lambda (_: K).Prop) with [(Bind _) \Rightarrow False | (Flat _) 
\Rightarrow True])])) I (THead (Bind b) u t) H6) in (False_ind (ex2 A 
(\lambda (a1: A).(arity g c0 u a1)) (\lambda (_: A).(arity g (CHead c0 (Bind 
b) u) t a))) H7))))))))))) (\lambda (c0: C).(\lambda (t0: T).(\lambda (a1: 
A).(\lambda (H2: (arity g c0 t0 a1)).(\lambda (H3: (((eq T t0 (THead (Bind b) 
u t)) \to (ex2 A (\lambda (a3: A).(arity g c0 u a3)) (\lambda (_: A).(arity g 
(CHead c0 (Bind b) u) t a1)))))).(\lambda (a0: A).(\lambda (H4: (leq g a1 
a0)).(\lambda (H5: (eq T t0 (THead (Bind b) u t))).(let H6 \def (f_equal T T 
(\lambda (e: T).e) t0 (THead (Bind b) u t) H5) in (let H7 \def (eq_ind T t0 
(\lambda (t1: T).((eq T t1 (THead (Bind b) u t)) \to (ex2 A (\lambda (a3: 
A).(arity g c0 u a3)) (\lambda (_: A).(arity g (CHead c0 (Bind b) u) t 
a1))))) H3 (THead (Bind b) u t) H6) in (let H8 \def (eq_ind T t0 (\lambda 
(t1: T).(arity g c0 t1 a1)) H2 (THead (Bind b) u t) H6) in (let H9 \def (H7 
(refl_equal T (THead (Bind b) u t))) in (ex2_ind A (\lambda (a3: A).(arity g 
c0 u a3)) (\lambda (_: A).(arity g (CHead c0 (Bind b) u) t a1)) (ex2 A 
(\lambda (a3: A).(arity g c0 u a3)) (\lambda (_: A).(arity g (CHead c0 (Bind 
b) u) t a0))) (\lambda (x: A).(\lambda (H10: (arity g c0 u x)).(\lambda (H11: 
(arity g (CHead c0 (Bind b) u) t a1)).(ex_intro2 A (\lambda (a3: A).(arity g 
c0 u a3)) (\lambda (_: A).(arity g (CHead c0 (Bind b) u) t a0)) x H10 
(arity_repl g (CHead c0 (Bind b) u) t a1 H11 a0 H4))))) H9))))))))))))) c y 
a2 H1))) H0)))))))).
(* COMMENTS
Initial nodes: 3365
END *)

theorem arity_gen_abst:
 \forall (g: G).(\forall (c: C).(\forall (u: T).(\forall (t: T).(\forall (a: 
A).((arity g c (THead (Bind Abst) u t) a) \to (ex3_2 A A (\lambda (a1: 
A).(\lambda (a2: A).(eq A a (AHead a1 a2)))) (\lambda (a1: A).(\lambda (_: 
A).(arity g c u (asucc g a1)))) (\lambda (_: A).(\lambda (a2: A).(arity g 
(CHead c (Bind Abst) u) t a2)))))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (u: T).(\lambda (t: T).(\lambda (a: 
A).(\lambda (H: (arity g c (THead (Bind Abst) u t) a)).(insert_eq T (THead 
(Bind Abst) u t) (\lambda (t0: T).(arity g c t0 a)) (\lambda (_: T).(ex3_2 A 
A (\lambda (a1: A).(\lambda (a2: A).(eq A a (AHead a1 a2)))) (\lambda (a1: 
A).(\lambda (_: A).(arity g c u (asucc g a1)))) (\lambda (_: A).(\lambda (a2: 
A).(arity g (CHead c (Bind Abst) u) t a2))))) (\lambda (y: T).(\lambda (H0: 
(arity g c y a)).(arity_ind g (\lambda (c0: C).(\lambda (t0: T).(\lambda (a0: 
A).((eq T t0 (THead (Bind Abst) u t)) \to (ex3_2 A A (\lambda (a1: 
A).(\lambda (a2: A).(eq A a0 (AHead a1 a2)))) (\lambda (a1: A).(\lambda (_: 
A).(arity g c0 u (asucc g a1)))) (\lambda (_: A).(\lambda (a2: A).(arity g 
(CHead c0 (Bind Abst) u) t a2)))))))) (\lambda (c0: C).(\lambda (n: 
nat).(\lambda (H1: (eq T (TSort n) (THead (Bind Abst) u t))).(let H2 \def 
(eq_ind T (TSort n) (\lambda (ee: T).(match ee in T return (\lambda (_: 
T).Prop) with [(TSort _) \Rightarrow True | (TLRef _) \Rightarrow False | 
(THead _ _ _) \Rightarrow False])) I (THead (Bind Abst) u t) H1) in 
(False_ind (ex3_2 A A (\lambda (a1: A).(\lambda (a2: A).(eq A (ASort O n) 
(AHead a1 a2)))) (\lambda (a1: A).(\lambda (_: A).(arity g c0 u (asucc g 
a1)))) (\lambda (_: A).(\lambda (a2: A).(arity g (CHead c0 (Bind Abst) u) t 
a2)))) H2))))) (\lambda (c0: C).(\lambda (d: C).(\lambda (u0: T).(\lambda (i: 
nat).(\lambda (_: (getl i c0 (CHead d (Bind Abbr) u0))).(\lambda (a0: 
A).(\lambda (_: (arity g d u0 a0)).(\lambda (_: (((eq T u0 (THead (Bind Abst) 
u t)) \to (ex3_2 A A (\lambda (a1: A).(\lambda (a2: A).(eq A a0 (AHead a1 
a2)))) (\lambda (a1: A).(\lambda (_: A).(arity g d u (asucc g a1)))) (\lambda 
(_: A).(\lambda (a2: A).(arity g (CHead d (Bind Abst) u) t a2))))))).(\lambda 
(H4: (eq T (TLRef i) (THead (Bind Abst) u t))).(let H5 \def (eq_ind T (TLRef 
i) (\lambda (ee: T).(match ee in T return (\lambda (_: T).Prop) with [(TSort 
_) \Rightarrow False | (TLRef _) \Rightarrow True | (THead _ _ _) \Rightarrow 
False])) I (THead (Bind Abst) u t) H4) in (False_ind (ex3_2 A A (\lambda (a1: 
A).(\lambda (a2: A).(eq A a0 (AHead a1 a2)))) (\lambda (a1: A).(\lambda (_: 
A).(arity g c0 u (asucc g a1)))) (\lambda (_: A).(\lambda (a2: A).(arity g 
(CHead c0 (Bind Abst) u) t a2)))) H5))))))))))) (\lambda (c0: C).(\lambda (d: 
C).(\lambda (u0: T).(\lambda (i: nat).(\lambda (_: (getl i c0 (CHead d (Bind 
Abst) u0))).(\lambda (a0: A).(\lambda (_: (arity g d u0 (asucc g 
a0))).(\lambda (_: (((eq T u0 (THead (Bind Abst) u t)) \to (ex3_2 A A 
(\lambda (a1: A).(\lambda (a2: A).(eq A (asucc g a0) (AHead a1 a2)))) 
(\lambda (a1: A).(\lambda (_: A).(arity g d u (asucc g a1)))) (\lambda (_: 
A).(\lambda (a2: A).(arity g (CHead d (Bind Abst) u) t a2))))))).(\lambda 
(H4: (eq T (TLRef i) (THead (Bind Abst) u t))).(let H5 \def (eq_ind T (TLRef 
i) (\lambda (ee: T).(match ee in T return (\lambda (_: T).Prop) with [(TSort 
_) \Rightarrow False | (TLRef _) \Rightarrow True | (THead _ _ _) \Rightarrow 
False])) I (THead (Bind Abst) u t) H4) in (False_ind (ex3_2 A A (\lambda (a1: 
A).(\lambda (a2: A).(eq A a0 (AHead a1 a2)))) (\lambda (a1: A).(\lambda (_: 
A).(arity g c0 u (asucc g a1)))) (\lambda (_: A).(\lambda (a2: A).(arity g 
(CHead c0 (Bind Abst) u) t a2)))) H5))))))))))) (\lambda (b: B).(\lambda (H1: 
(not (eq B b Abst))).(\lambda (c0: C).(\lambda (u0: T).(\lambda (a1: 
A).(\lambda (H2: (arity g c0 u0 a1)).(\lambda (H3: (((eq T u0 (THead (Bind 
Abst) u t)) \to (ex3_2 A A (\lambda (a2: A).(\lambda (a3: A).(eq A a1 (AHead 
a2 a3)))) (\lambda (a2: A).(\lambda (_: A).(arity g c0 u (asucc g a2)))) 
(\lambda (_: A).(\lambda (a3: A).(arity g (CHead c0 (Bind Abst) u) t 
a3))))))).(\lambda (t0: T).(\lambda (a2: A).(\lambda (H4: (arity g (CHead c0 
(Bind b) u0) t0 a2)).(\lambda (H5: (((eq T t0 (THead (Bind Abst) u t)) \to 
(ex3_2 A A (\lambda (a3: A).(\lambda (a4: A).(eq A a2 (AHead a3 a4)))) 
(\lambda (a3: A).(\lambda (_: A).(arity g (CHead c0 (Bind b) u0) u (asucc g 
a3)))) (\lambda (_: A).(\lambda (a4: A).(arity g (CHead (CHead c0 (Bind b) 
u0) (Bind Abst) u) t a4))))))).(\lambda (H6: (eq T (THead (Bind b) u0 t0) 
(THead (Bind Abst) u t))).(let H7 \def (f_equal T B (\lambda (e: T).(match e 
in T return (\lambda (_: T).B) with [(TSort _) \Rightarrow b | (TLRef _) 
\Rightarrow b | (THead k _ _) \Rightarrow (match k in K return (\lambda (_: 
K).B) with [(Bind b0) \Rightarrow b0 | (Flat _) \Rightarrow b])])) (THead 
(Bind b) u0 t0) (THead (Bind Abst) u t) H6) in ((let H8 \def (f_equal T T 
(\lambda (e: T).(match e in T return (\lambda (_: T).T) with [(TSort _) 
\Rightarrow u0 | (TLRef _) \Rightarrow u0 | (THead _ t1 _) \Rightarrow t1])) 
(THead (Bind b) u0 t0) (THead (Bind Abst) u t) H6) in ((let H9 \def (f_equal 
T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) with [(TSort _) 
\Rightarrow t0 | (TLRef _) \Rightarrow t0 | (THead _ _ t1) \Rightarrow t1])) 
(THead (Bind b) u0 t0) (THead (Bind Abst) u t) H6) in (\lambda (H10: (eq T u0 
u)).(\lambda (H11: (eq B b Abst)).(let H12 \def (eq_ind T t0 (\lambda (t1: 
T).((eq T t1 (THead (Bind Abst) u t)) \to (ex3_2 A A (\lambda (a3: 
A).(\lambda (a4: A).(eq A a2 (AHead a3 a4)))) (\lambda (a3: A).(\lambda (_: 
A).(arity g (CHead c0 (Bind b) u0) u (asucc g a3)))) (\lambda (_: A).(\lambda 
(a4: A).(arity g (CHead (CHead c0 (Bind b) u0) (Bind Abst) u) t a4)))))) H5 t 
H9) in (let H13 \def (eq_ind T t0 (\lambda (t1: T).(arity g (CHead c0 (Bind 
b) u0) t1 a2)) H4 t H9) in (let H14 \def (eq_ind T u0 (\lambda (t1: T).((eq T 
t (THead (Bind Abst) u t)) \to (ex3_2 A A (\lambda (a3: A).(\lambda (a4: 
A).(eq A a2 (AHead a3 a4)))) (\lambda (a3: A).(\lambda (_: A).(arity g (CHead 
c0 (Bind b) t1) u (asucc g a3)))) (\lambda (_: A).(\lambda (a4: A).(arity g 
(CHead (CHead c0 (Bind b) t1) (Bind Abst) u) t a4)))))) H12 u H10) in (let 
H15 \def (eq_ind T u0 (\lambda (t1: T).(arity g (CHead c0 (Bind b) t1) t a2)) 
H13 u H10) in (let H16 \def (eq_ind T u0 (\lambda (t1: T).((eq T t1 (THead 
(Bind Abst) u t)) \to (ex3_2 A A (\lambda (a3: A).(\lambda (a4: A).(eq A a1 
(AHead a3 a4)))) (\lambda (a3: A).(\lambda (_: A).(arity g c0 u (asucc g 
a3)))) (\lambda (_: A).(\lambda (a4: A).(arity g (CHead c0 (Bind Abst) u) t 
a4)))))) H3 u H10) in (let H17 \def (eq_ind T u0 (\lambda (t1: T).(arity g c0 
t1 a1)) H2 u H10) in (let H18 \def (eq_ind B b (\lambda (b0: B).((eq T t 
(THead (Bind Abst) u t)) \to (ex3_2 A A (\lambda (a3: A).(\lambda (a4: A).(eq 
A a2 (AHead a3 a4)))) (\lambda (a3: A).(\lambda (_: A).(arity g (CHead c0 
(Bind b0) u) u (asucc g a3)))) (\lambda (_: A).(\lambda (a4: A).(arity g 
(CHead (CHead c0 (Bind b0) u) (Bind Abst) u) t a4)))))) H14 Abst H11) in (let 
H19 \def (eq_ind B b (\lambda (b0: B).(arity g (CHead c0 (Bind b0) u) t a2)) 
H15 Abst H11) in (let H20 \def (eq_ind B b (\lambda (b0: B).(not (eq B b0 
Abst))) H1 Abst H11) in (let H21 \def (match (H20 (refl_equal B Abst)) in 
False return (\lambda (_: False).(ex3_2 A A (\lambda (a3: A).(\lambda (a4: 
A).(eq A a2 (AHead a3 a4)))) (\lambda (a3: A).(\lambda (_: A).(arity g c0 u 
(asucc g a3)))) (\lambda (_: A).(\lambda (a4: A).(arity g (CHead c0 (Bind 
Abst) u) t a4))))) with []) in H21))))))))))))) H8)) H7)))))))))))))) 
(\lambda (c0: C).(\lambda (u0: T).(\lambda (a1: A).(\lambda (H1: (arity g c0 
u0 (asucc g a1))).(\lambda (H2: (((eq T u0 (THead (Bind Abst) u t)) \to 
(ex3_2 A A (\lambda (a2: A).(\lambda (a3: A).(eq A (asucc g a1) (AHead a2 
a3)))) (\lambda (a2: A).(\lambda (_: A).(arity g c0 u (asucc g a2)))) 
(\lambda (_: A).(\lambda (a3: A).(arity g (CHead c0 (Bind Abst) u) t 
a3))))))).(\lambda (t0: T).(\lambda (a2: A).(\lambda (H3: (arity g (CHead c0 
(Bind Abst) u0) t0 a2)).(\lambda (H4: (((eq T t0 (THead (Bind Abst) u t)) \to 
(ex3_2 A A (\lambda (a3: A).(\lambda (a4: A).(eq A a2 (AHead a3 a4)))) 
(\lambda (a3: A).(\lambda (_: A).(arity g (CHead c0 (Bind Abst) u0) u (asucc 
g a3)))) (\lambda (_: A).(\lambda (a4: A).(arity g (CHead (CHead c0 (Bind 
Abst) u0) (Bind Abst) u) t a4))))))).(\lambda (H5: (eq T (THead (Bind Abst) 
u0 t0) (THead (Bind Abst) u t))).(let H6 \def (f_equal T T (\lambda (e: 
T).(match e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow u0 | 
(TLRef _) \Rightarrow u0 | (THead _ t1 _) \Rightarrow t1])) (THead (Bind 
Abst) u0 t0) (THead (Bind Abst) u t) H5) in ((let H7 \def (f_equal T T 
(\lambda (e: T).(match e in T return (\lambda (_: T).T) with [(TSort _) 
\Rightarrow t0 | (TLRef _) \Rightarrow t0 | (THead _ _ t1) \Rightarrow t1])) 
(THead (Bind Abst) u0 t0) (THead (Bind Abst) u t) H5) in (\lambda (H8: (eq T 
u0 u)).(let H9 \def (eq_ind T t0 (\lambda (t1: T).((eq T t1 (THead (Bind 
Abst) u t)) \to (ex3_2 A A (\lambda (a3: A).(\lambda (a4: A).(eq A a2 (AHead 
a3 a4)))) (\lambda (a3: A).(\lambda (_: A).(arity g (CHead c0 (Bind Abst) u0) 
u (asucc g a3)))) (\lambda (_: A).(\lambda (a4: A).(arity g (CHead (CHead c0 
(Bind Abst) u0) (Bind Abst) u) t a4)))))) H4 t H7) in (let H10 \def (eq_ind T 
t0 (\lambda (t1: T).(arity g (CHead c0 (Bind Abst) u0) t1 a2)) H3 t H7) in 
(let H11 \def (eq_ind T u0 (\lambda (t1: T).((eq T t (THead (Bind Abst) u t)) 
\to (ex3_2 A A (\lambda (a3: A).(\lambda (a4: A).(eq A a2 (AHead a3 a4)))) 
(\lambda (a3: A).(\lambda (_: A).(arity g (CHead c0 (Bind Abst) t1) u (asucc 
g a3)))) (\lambda (_: A).(\lambda (a4: A).(arity g (CHead (CHead c0 (Bind 
Abst) t1) (Bind Abst) u) t a4)))))) H9 u H8) in (let H12 \def (eq_ind T u0 
(\lambda (t1: T).(arity g (CHead c0 (Bind Abst) t1) t a2)) H10 u H8) in (let 
H13 \def (eq_ind T u0 (\lambda (t1: T).((eq T t1 (THead (Bind Abst) u t)) \to 
(ex3_2 A A (\lambda (a3: A).(\lambda (a4: A).(eq A (asucc g a1) (AHead a3 
a4)))) (\lambda (a3: A).(\lambda (_: A).(arity g c0 u (asucc g a3)))) 
(\lambda (_: A).(\lambda (a4: A).(arity g (CHead c0 (Bind Abst) u) t a4)))))) 
H2 u H8) in (let H14 \def (eq_ind T u0 (\lambda (t1: T).(arity g c0 t1 (asucc 
g a1))) H1 u H8) in (ex3_2_intro A A (\lambda (a3: A).(\lambda (a4: A).(eq A 
(AHead a1 a2) (AHead a3 a4)))) (\lambda (a3: A).(\lambda (_: A).(arity g c0 u 
(asucc g a3)))) (\lambda (_: A).(\lambda (a4: A).(arity g (CHead c0 (Bind 
Abst) u) t a4))) a1 a2 (refl_equal A (AHead a1 a2)) H14 H12))))))))) 
H6)))))))))))) (\lambda (c0: C).(\lambda (u0: T).(\lambda (a1: A).(\lambda 
(_: (arity g c0 u0 a1)).(\lambda (_: (((eq T u0 (THead (Bind Abst) u t)) \to 
(ex3_2 A A (\lambda (a2: A).(\lambda (a3: A).(eq A a1 (AHead a2 a3)))) 
(\lambda (a2: A).(\lambda (_: A).(arity g c0 u (asucc g a2)))) (\lambda (_: 
A).(\lambda (a3: A).(arity g (CHead c0 (Bind Abst) u) t a3))))))).(\lambda 
(t0: T).(\lambda (a2: A).(\lambda (_: (arity g c0 t0 (AHead a1 a2))).(\lambda 
(_: (((eq T t0 (THead (Bind Abst) u t)) \to (ex3_2 A A (\lambda (a3: 
A).(\lambda (a4: A).(eq A (AHead a1 a2) (AHead a3 a4)))) (\lambda (a3: 
A).(\lambda (_: A).(arity g c0 u (asucc g a3)))) (\lambda (_: A).(\lambda 
(a4: A).(arity g (CHead c0 (Bind Abst) u) t a4))))))).(\lambda (H5: (eq T 
(THead (Flat Appl) u0 t0) (THead (Bind Abst) u t))).(let H6 \def (eq_ind T 
(THead (Flat Appl) u0 t0) (\lambda (ee: T).(match ee in T return (\lambda (_: 
T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | 
(THead k _ _) \Rightarrow (match k in K return (\lambda (_: K).Prop) with 
[(Bind _) \Rightarrow False | (Flat _) \Rightarrow True])])) I (THead (Bind 
Abst) u t) H5) in (False_ind (ex3_2 A A (\lambda (a3: A).(\lambda (a4: A).(eq 
A a2 (AHead a3 a4)))) (\lambda (a3: A).(\lambda (_: A).(arity g c0 u (asucc g 
a3)))) (\lambda (_: A).(\lambda (a4: A).(arity g (CHead c0 (Bind Abst) u) t 
a4)))) H6)))))))))))) (\lambda (c0: C).(\lambda (u0: T).(\lambda (a0: 
A).(\lambda (_: (arity g c0 u0 (asucc g a0))).(\lambda (_: (((eq T u0 (THead 
(Bind Abst) u t)) \to (ex3_2 A A (\lambda (a1: A).(\lambda (a2: A).(eq A 
(asucc g a0) (AHead a1 a2)))) (\lambda (a1: A).(\lambda (_: A).(arity g c0 u 
(asucc g a1)))) (\lambda (_: A).(\lambda (a2: A).(arity g (CHead c0 (Bind 
Abst) u) t a2))))))).(\lambda (t0: T).(\lambda (_: (arity g c0 t0 
a0)).(\lambda (_: (((eq T t0 (THead (Bind Abst) u t)) \to (ex3_2 A A (\lambda 
(a1: A).(\lambda (a2: A).(eq A a0 (AHead a1 a2)))) (\lambda (a1: A).(\lambda 
(_: A).(arity g c0 u (asucc g a1)))) (\lambda (_: A).(\lambda (a2: A).(arity 
g (CHead c0 (Bind Abst) u) t a2))))))).(\lambda (H5: (eq T (THead (Flat Cast) 
u0 t0) (THead (Bind Abst) u t))).(let H6 \def (eq_ind T (THead (Flat Cast) u0 
t0) (\lambda (ee: T).(match ee in T return (\lambda (_: T).Prop) with [(TSort 
_) \Rightarrow False | (TLRef _) \Rightarrow False | (THead k _ _) 
\Rightarrow (match k in K return (\lambda (_: K).Prop) with [(Bind _) 
\Rightarrow False | (Flat _) \Rightarrow True])])) I (THead (Bind Abst) u t) 
H5) in (False_ind (ex3_2 A A (\lambda (a1: A).(\lambda (a2: A).(eq A a0 
(AHead a1 a2)))) (\lambda (a1: A).(\lambda (_: A).(arity g c0 u (asucc g 
a1)))) (\lambda (_: A).(\lambda (a2: A).(arity g (CHead c0 (Bind Abst) u) t 
a2)))) H6))))))))))) (\lambda (c0: C).(\lambda (t0: T).(\lambda (a1: 
A).(\lambda (H1: (arity g c0 t0 a1)).(\lambda (H2: (((eq T t0 (THead (Bind 
Abst) u t)) \to (ex3_2 A A (\lambda (a2: A).(\lambda (a3: A).(eq A a1 (AHead 
a2 a3)))) (\lambda (a2: A).(\lambda (_: A).(arity g c0 u (asucc g a2)))) 
(\lambda (_: A).(\lambda (a3: A).(arity g (CHead c0 (Bind Abst) u) t 
a3))))))).(\lambda (a2: A).(\lambda (H3: (leq g a1 a2)).(\lambda (H4: (eq T 
t0 (THead (Bind Abst) u t))).(let H5 \def (f_equal T T (\lambda (e: T).e) t0 
(THead (Bind Abst) u t) H4) in (let H6 \def (eq_ind T t0 (\lambda (t1: 
T).((eq T t1 (THead (Bind Abst) u t)) \to (ex3_2 A A (\lambda (a3: 
A).(\lambda (a4: A).(eq A a1 (AHead a3 a4)))) (\lambda (a3: A).(\lambda (_: 
A).(arity g c0 u (asucc g a3)))) (\lambda (_: A).(\lambda (a4: A).(arity g 
(CHead c0 (Bind Abst) u) t a4)))))) H2 (THead (Bind Abst) u t) H5) in (let H7 
\def (eq_ind T t0 (\lambda (t1: T).(arity g c0 t1 a1)) H1 (THead (Bind Abst) 
u t) H5) in (let H8 \def (H6 (refl_equal T (THead (Bind Abst) u t))) in 
(ex3_2_ind A A (\lambda (a3: A).(\lambda (a4: A).(eq A a1 (AHead a3 a4)))) 
(\lambda (a3: A).(\lambda (_: A).(arity g c0 u (asucc g a3)))) (\lambda (_: 
A).(\lambda (a4: A).(arity g (CHead c0 (Bind Abst) u) t a4))) (ex3_2 A A 
(\lambda (a3: A).(\lambda (a4: A).(eq A a2 (AHead a3 a4)))) (\lambda (a3: 
A).(\lambda (_: A).(arity g c0 u (asucc g a3)))) (\lambda (_: A).(\lambda 
(a4: A).(arity g (CHead c0 (Bind Abst) u) t a4)))) (\lambda (x0: A).(\lambda 
(x1: A).(\lambda (H9: (eq A a1 (AHead x0 x1))).(\lambda (H10: (arity g c0 u 
(asucc g x0))).(\lambda (H11: (arity g (CHead c0 (Bind Abst) u) t x1)).(let 
H12 \def (eq_ind A a1 (\lambda (a0: A).(leq g a0 a2)) H3 (AHead x0 x1) H9) in 
(let H13 \def (eq_ind A a1 (\lambda (a0: A).(arity g c0 (THead (Bind Abst) u 
t) a0)) H7 (AHead x0 x1) H9) in (let H_x \def (leq_gen_head1 g x0 x1 a2 H12) 
in (let H14 \def H_x in (ex3_2_ind A A (\lambda (a3: A).(\lambda (_: A).(leq 
g x0 a3))) (\lambda (_: A).(\lambda (a4: A).(leq g x1 a4))) (\lambda (a3: 
A).(\lambda (a4: A).(eq A a2 (AHead a3 a4)))) (ex3_2 A A (\lambda (a3: 
A).(\lambda (a4: A).(eq A a2 (AHead a3 a4)))) (\lambda (a3: A).(\lambda (_: 
A).(arity g c0 u (asucc g a3)))) (\lambda (_: A).(\lambda (a4: A).(arity g 
(CHead c0 (Bind Abst) u) t a4)))) (\lambda (x2: A).(\lambda (x3: A).(\lambda 
(H15: (leq g x0 x2)).(\lambda (H16: (leq g x1 x3)).(\lambda (H17: (eq A a2 
(AHead x2 x3))).(let H18 \def (f_equal A A (\lambda (e: A).e) a2 (AHead x2 
x3) H17) in (eq_ind_r A (AHead x2 x3) (\lambda (a0: A).(ex3_2 A A (\lambda 
(a3: A).(\lambda (a4: A).(eq A a0 (AHead a3 a4)))) (\lambda (a3: A).(\lambda 
(_: A).(arity g c0 u (asucc g a3)))) (\lambda (_: A).(\lambda (a4: A).(arity 
g (CHead c0 (Bind Abst) u) t a4))))) (ex3_2_intro A A (\lambda (a3: 
A).(\lambda (a4: A).(eq A (AHead x2 x3) (AHead a3 a4)))) (\lambda (a3: 
A).(\lambda (_: A).(arity g c0 u (asucc g a3)))) (\lambda (_: A).(\lambda 
(a4: A).(arity g (CHead c0 (Bind Abst) u) t a4))) x2 x3 (refl_equal A (AHead 
x2 x3)) (arity_repl g c0 u (asucc g x0) H10 (asucc g x2) (asucc_repl g x0 x2 
H15)) (arity_repl g (CHead c0 (Bind Abst) u) t x1 H11 x3 H16)) a2 H18))))))) 
H14)))))))))) H8))))))))))))) c y a H0))) H)))))).
(* COMMENTS
Initial nodes: 4265
END *)

theorem arity_gen_appl:
 \forall (g: G).(\forall (c: C).(\forall (u: T).(\forall (t: T).(\forall (a2: 
A).((arity g c (THead (Flat Appl) u t) a2) \to (ex2 A (\lambda (a1: A).(arity 
g c u a1)) (\lambda (a1: A).(arity g c t (AHead a1 a2)))))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (u: T).(\lambda (t: T).(\lambda (a2: 
A).(\lambda (H: (arity g c (THead (Flat Appl) u t) a2)).(insert_eq T (THead 
(Flat Appl) u t) (\lambda (t0: T).(arity g c t0 a2)) (\lambda (_: T).(ex2 A 
(\lambda (a1: A).(arity g c u a1)) (\lambda (a1: A).(arity g c t (AHead a1 
a2))))) (\lambda (y: T).(\lambda (H0: (arity g c y a2)).(arity_ind g (\lambda 
(c0: C).(\lambda (t0: T).(\lambda (a: A).((eq T t0 (THead (Flat Appl) u t)) 
\to (ex2 A (\lambda (a1: A).(arity g c0 u a1)) (\lambda (a1: A).(arity g c0 t 
(AHead a1 a)))))))) (\lambda (c0: C).(\lambda (n: nat).(\lambda (H1: (eq T 
(TSort n) (THead (Flat Appl) u t))).(let H2 \def (eq_ind T (TSort n) (\lambda 
(ee: T).(match ee in T return (\lambda (_: T).Prop) with [(TSort _) 
\Rightarrow True | (TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow 
False])) I (THead (Flat Appl) u t) H1) in (False_ind (ex2 A (\lambda (a1: 
A).(arity g c0 u a1)) (\lambda (a1: A).(arity g c0 t (AHead a1 (ASort O 
n))))) H2))))) (\lambda (c0: C).(\lambda (d: C).(\lambda (u0: T).(\lambda (i: 
nat).(\lambda (_: (getl i c0 (CHead d (Bind Abbr) u0))).(\lambda (a: 
A).(\lambda (_: (arity g d u0 a)).(\lambda (_: (((eq T u0 (THead (Flat Appl) 
u t)) \to (ex2 A (\lambda (a1: A).(arity g d u a1)) (\lambda (a1: A).(arity g 
d t (AHead a1 a))))))).(\lambda (H4: (eq T (TLRef i) (THead (Flat Appl) u 
t))).(let H5 \def (eq_ind T (TLRef i) (\lambda (ee: T).(match ee in T return 
(\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow True | (THead _ _ _) \Rightarrow False])) I (THead (Flat Appl) u 
t) H4) in (False_ind (ex2 A (\lambda (a1: A).(arity g c0 u a1)) (\lambda (a1: 
A).(arity g c0 t (AHead a1 a)))) H5))))))))))) (\lambda (c0: C).(\lambda (d: 
C).(\lambda (u0: T).(\lambda (i: nat).(\lambda (_: (getl i c0 (CHead d (Bind 
Abst) u0))).(\lambda (a: A).(\lambda (_: (arity g d u0 (asucc g a))).(\lambda 
(_: (((eq T u0 (THead (Flat Appl) u t)) \to (ex2 A (\lambda (a1: A).(arity g 
d u a1)) (\lambda (a1: A).(arity g d t (AHead a1 (asucc g a)))))))).(\lambda 
(H4: (eq T (TLRef i) (THead (Flat Appl) u t))).(let H5 \def (eq_ind T (TLRef 
i) (\lambda (ee: T).(match ee in T return (\lambda (_: T).Prop) with [(TSort 
_) \Rightarrow False | (TLRef _) \Rightarrow True | (THead _ _ _) \Rightarrow 
False])) I (THead (Flat Appl) u t) H4) in (False_ind (ex2 A (\lambda (a1: 
A).(arity g c0 u a1)) (\lambda (a1: A).(arity g c0 t (AHead a1 a)))) 
H5))))))))))) (\lambda (b: B).(\lambda (_: (not (eq B b Abst))).(\lambda (c0: 
C).(\lambda (u0: T).(\lambda (a1: A).(\lambda (_: (arity g c0 u0 
a1)).(\lambda (_: (((eq T u0 (THead (Flat Appl) u t)) \to (ex2 A (\lambda 
(a3: A).(arity g c0 u a3)) (\lambda (a3: A).(arity g c0 t (AHead a3 
a1))))))).(\lambda (t0: T).(\lambda (a0: A).(\lambda (_: (arity g (CHead c0 
(Bind b) u0) t0 a0)).(\lambda (_: (((eq T t0 (THead (Flat Appl) u t)) \to 
(ex2 A (\lambda (a3: A).(arity g (CHead c0 (Bind b) u0) u a3)) (\lambda (a3: 
A).(arity g (CHead c0 (Bind b) u0) t (AHead a3 a0))))))).(\lambda (H6: (eq T 
(THead (Bind b) u0 t0) (THead (Flat Appl) u t))).(let H7 \def (eq_ind T 
(THead (Bind b) u0 t0) (\lambda (ee: T).(match ee in T return (\lambda (_: 
T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | 
(THead k _ _) \Rightarrow (match k in K return (\lambda (_: K).Prop) with 
[(Bind _) \Rightarrow True | (Flat _) \Rightarrow False])])) I (THead (Flat 
Appl) u t) H6) in (False_ind (ex2 A (\lambda (a3: A).(arity g c0 u a3)) 
(\lambda (a3: A).(arity g c0 t (AHead a3 a0)))) H7)))))))))))))) (\lambda 
(c0: C).(\lambda (u0: T).(\lambda (a1: A).(\lambda (_: (arity g c0 u0 (asucc 
g a1))).(\lambda (_: (((eq T u0 (THead (Flat Appl) u t)) \to (ex2 A (\lambda 
(a3: A).(arity g c0 u a3)) (\lambda (a3: A).(arity g c0 t (AHead a3 (asucc g 
a1)))))))).(\lambda (t0: T).(\lambda (a0: A).(\lambda (_: (arity g (CHead c0 
(Bind Abst) u0) t0 a0)).(\lambda (_: (((eq T t0 (THead (Flat Appl) u t)) \to 
(ex2 A (\lambda (a3: A).(arity g (CHead c0 (Bind Abst) u0) u a3)) (\lambda 
(a3: A).(arity g (CHead c0 (Bind Abst) u0) t (AHead a3 a0))))))).(\lambda 
(H5: (eq T (THead (Bind Abst) u0 t0) (THead (Flat Appl) u t))).(let H6 \def 
(eq_ind T (THead (Bind Abst) u0 t0) (\lambda (ee: T).(match ee in T return 
(\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow False | (THead k _ _) \Rightarrow (match k in K return (\lambda 
(_: K).Prop) with [(Bind _) \Rightarrow True | (Flat _) \Rightarrow 
False])])) I (THead (Flat Appl) u t) H5) in (False_ind (ex2 A (\lambda (a3: 
A).(arity g c0 u a3)) (\lambda (a3: A).(arity g c0 t (AHead a3 (AHead a1 
a0))))) H6)))))))))))) (\lambda (c0: C).(\lambda (u0: T).(\lambda (a1: 
A).(\lambda (H1: (arity g c0 u0 a1)).(\lambda (H2: (((eq T u0 (THead (Flat 
Appl) u t)) \to (ex2 A (\lambda (a3: A).(arity g c0 u a3)) (\lambda (a3: 
A).(arity g c0 t (AHead a3 a1))))))).(\lambda (t0: T).(\lambda (a0: 
A).(\lambda (H3: (arity g c0 t0 (AHead a1 a0))).(\lambda (H4: (((eq T t0 
(THead (Flat Appl) u t)) \to (ex2 A (\lambda (a3: A).(arity g c0 u a3)) 
(\lambda (a3: A).(arity g c0 t (AHead a3 (AHead a1 a0)))))))).(\lambda (H5: 
(eq T (THead (Flat Appl) u0 t0) (THead (Flat Appl) u t))).(let H6 \def 
(f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) with 
[(TSort _) \Rightarrow u0 | (TLRef _) \Rightarrow u0 | (THead _ t1 _) 
\Rightarrow t1])) (THead (Flat Appl) u0 t0) (THead (Flat Appl) u t) H5) in 
((let H7 \def (f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: 
T).T) with [(TSort _) \Rightarrow t0 | (TLRef _) \Rightarrow t0 | (THead _ _ 
t1) \Rightarrow t1])) (THead (Flat Appl) u0 t0) (THead (Flat Appl) u t) H5) 
in (\lambda (H8: (eq T u0 u)).(let H9 \def (eq_ind T t0 (\lambda (t1: T).((eq 
T t1 (THead (Flat Appl) u t)) \to (ex2 A (\lambda (a3: A).(arity g c0 u a3)) 
(\lambda (a3: A).(arity g c0 t (AHead a3 (AHead a1 a0))))))) H4 t H7) in (let 
H10 \def (eq_ind T t0 (\lambda (t1: T).(arity g c0 t1 (AHead a1 a0))) H3 t 
H7) in (let H11 \def (eq_ind T u0 (\lambda (t1: T).((eq T t1 (THead (Flat 
Appl) u t)) \to (ex2 A (\lambda (a3: A).(arity g c0 u a3)) (\lambda (a3: 
A).(arity g c0 t (AHead a3 a1)))))) H2 u H8) in (let H12 \def (eq_ind T u0 
(\lambda (t1: T).(arity g c0 t1 a1)) H1 u H8) in (ex_intro2 A (\lambda (a3: 
A).(arity g c0 u a3)) (\lambda (a3: A).(arity g c0 t (AHead a3 a0))) a1 H12 
H10))))))) H6)))))))))))) (\lambda (c0: C).(\lambda (u0: T).(\lambda (a: 
A).(\lambda (_: (arity g c0 u0 (asucc g a))).(\lambda (_: (((eq T u0 (THead 
(Flat Appl) u t)) \to (ex2 A (\lambda (a1: A).(arity g c0 u a1)) (\lambda 
(a1: A).(arity g c0 t (AHead a1 (asucc g a)))))))).(\lambda (t0: T).(\lambda 
(_: (arity g c0 t0 a)).(\lambda (_: (((eq T t0 (THead (Flat Appl) u t)) \to 
(ex2 A (\lambda (a1: A).(arity g c0 u a1)) (\lambda (a1: A).(arity g c0 t 
(AHead a1 a))))))).(\lambda (H5: (eq T (THead (Flat Cast) u0 t0) (THead (Flat 
Appl) u t))).(let H6 \def (eq_ind T (THead (Flat Cast) u0 t0) (\lambda (ee: 
T).(match ee in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow 
False | (TLRef _) \Rightarrow False | (THead k _ _) \Rightarrow (match k in K 
return (\lambda (_: K).Prop) with [(Bind _) \Rightarrow False | (Flat f) 
\Rightarrow (match f in F return (\lambda (_: F).Prop) with [Appl \Rightarrow 
False | Cast \Rightarrow True])])])) I (THead (Flat Appl) u t) H5) in 
(False_ind (ex2 A (\lambda (a1: A).(arity g c0 u a1)) (\lambda (a1: A).(arity 
g c0 t (AHead a1 a)))) H6))))))))))) (\lambda (c0: C).(\lambda (t0: 
T).(\lambda (a1: A).(\lambda (H1: (arity g c0 t0 a1)).(\lambda (H2: (((eq T 
t0 (THead (Flat Appl) u t)) \to (ex2 A (\lambda (a3: A).(arity g c0 u a3)) 
(\lambda (a3: A).(arity g c0 t (AHead a3 a1))))))).(\lambda (a0: A).(\lambda 
(H3: (leq g a1 a0)).(\lambda (H4: (eq T t0 (THead (Flat Appl) u t))).(let H5 
\def (f_equal T T (\lambda (e: T).e) t0 (THead (Flat Appl) u t) H4) in (let 
H6 \def (eq_ind T t0 (\lambda (t1: T).((eq T t1 (THead (Flat Appl) u t)) \to 
(ex2 A (\lambda (a3: A).(arity g c0 u a3)) (\lambda (a3: A).(arity g c0 t 
(AHead a3 a1)))))) H2 (THead (Flat Appl) u t) H5) in (let H7 \def (eq_ind T 
t0 (\lambda (t1: T).(arity g c0 t1 a1)) H1 (THead (Flat Appl) u t) H5) in 
(let H8 \def (H6 (refl_equal T (THead (Flat Appl) u t))) in (ex2_ind A 
(\lambda (a3: A).(arity g c0 u a3)) (\lambda (a3: A).(arity g c0 t (AHead a3 
a1))) (ex2 A (\lambda (a3: A).(arity g c0 u a3)) (\lambda (a3: A).(arity g c0 
t (AHead a3 a0)))) (\lambda (x: A).(\lambda (H9: (arity g c0 u x)).(\lambda 
(H10: (arity g c0 t (AHead x a1))).(ex_intro2 A (\lambda (a3: A).(arity g c0 
u a3)) (\lambda (a3: A).(arity g c0 t (AHead a3 a0))) x H9 (arity_repl g c0 t 
(AHead x a1) H10 (AHead x a0) (leq_head g x x (leq_refl g x) a1 a0 H3)))))) 
H8))))))))))))) c y a2 H0))) H)))))).
(* COMMENTS
Initial nodes: 2277
END *)

theorem arity_gen_cast:
 \forall (g: G).(\forall (c: C).(\forall (u: T).(\forall (t: T).(\forall (a: 
A).((arity g c (THead (Flat Cast) u t) a) \to (land (arity g c u (asucc g a)) 
(arity g c t a)))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (u: T).(\lambda (t: T).(\lambda (a: 
A).(\lambda (H: (arity g c (THead (Flat Cast) u t) a)).(insert_eq T (THead 
(Flat Cast) u t) (\lambda (t0: T).(arity g c t0 a)) (\lambda (_: T).(land 
(arity g c u (asucc g a)) (arity g c t a))) (\lambda (y: T).(\lambda (H0: 
(arity g c y a)).(arity_ind g (\lambda (c0: C).(\lambda (t0: T).(\lambda (a0: 
A).((eq T t0 (THead (Flat Cast) u t)) \to (land (arity g c0 u (asucc g a0)) 
(arity g c0 t a0)))))) (\lambda (c0: C).(\lambda (n: nat).(\lambda (H1: (eq T 
(TSort n) (THead (Flat Cast) u t))).(let H2 \def (eq_ind T (TSort n) (\lambda 
(ee: T).(match ee in T return (\lambda (_: T).Prop) with [(TSort _) 
\Rightarrow True | (TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow 
False])) I (THead (Flat Cast) u t) H1) in (False_ind (land (arity g c0 u 
(asucc g (ASort O n))) (arity g c0 t (ASort O n))) H2))))) (\lambda (c0: 
C).(\lambda (d: C).(\lambda (u0: T).(\lambda (i: nat).(\lambda (_: (getl i c0 
(CHead d (Bind Abbr) u0))).(\lambda (a0: A).(\lambda (_: (arity g d u0 
a0)).(\lambda (_: (((eq T u0 (THead (Flat Cast) u t)) \to (land (arity g d u 
(asucc g a0)) (arity g d t a0))))).(\lambda (H4: (eq T (TLRef i) (THead (Flat 
Cast) u t))).(let H5 \def (eq_ind T (TLRef i) (\lambda (ee: T).(match ee in T 
return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow True | (THead _ _ _) \Rightarrow False])) I (THead (Flat Cast) u 
t) H4) in (False_ind (land (arity g c0 u (asucc g a0)) (arity g c0 t a0)) 
H5))))))))))) (\lambda (c0: C).(\lambda (d: C).(\lambda (u0: T).(\lambda (i: 
nat).(\lambda (_: (getl i c0 (CHead d (Bind Abst) u0))).(\lambda (a0: 
A).(\lambda (_: (arity g d u0 (asucc g a0))).(\lambda (_: (((eq T u0 (THead 
(Flat Cast) u t)) \to (land (arity g d u (asucc g (asucc g a0))) (arity g d t 
(asucc g a0)))))).(\lambda (H4: (eq T (TLRef i) (THead (Flat Cast) u 
t))).(let H5 \def (eq_ind T (TLRef i) (\lambda (ee: T).(match ee in T return 
(\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow True | (THead _ _ _) \Rightarrow False])) I (THead (Flat Cast) u 
t) H4) in (False_ind (land (arity g c0 u (asucc g a0)) (arity g c0 t a0)) 
H5))))))))))) (\lambda (b: B).(\lambda (_: (not (eq B b Abst))).(\lambda (c0: 
C).(\lambda (u0: T).(\lambda (a1: A).(\lambda (_: (arity g c0 u0 
a1)).(\lambda (_: (((eq T u0 (THead (Flat Cast) u t)) \to (land (arity g c0 u 
(asucc g a1)) (arity g c0 t a1))))).(\lambda (t0: T).(\lambda (a2: 
A).(\lambda (_: (arity g (CHead c0 (Bind b) u0) t0 a2)).(\lambda (_: (((eq T 
t0 (THead (Flat Cast) u t)) \to (land (arity g (CHead c0 (Bind b) u0) u 
(asucc g a2)) (arity g (CHead c0 (Bind b) u0) t a2))))).(\lambda (H6: (eq T 
(THead (Bind b) u0 t0) (THead (Flat Cast) u t))).(let H7 \def (eq_ind T 
(THead (Bind b) u0 t0) (\lambda (ee: T).(match ee in T return (\lambda (_: 
T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | 
(THead k _ _) \Rightarrow (match k in K return (\lambda (_: K).Prop) with 
[(Bind _) \Rightarrow True | (Flat _) \Rightarrow False])])) I (THead (Flat 
Cast) u t) H6) in (False_ind (land (arity g c0 u (asucc g a2)) (arity g c0 t 
a2)) H7)))))))))))))) (\lambda (c0: C).(\lambda (u0: T).(\lambda (a1: 
A).(\lambda (_: (arity g c0 u0 (asucc g a1))).(\lambda (_: (((eq T u0 (THead 
(Flat Cast) u t)) \to (land (arity g c0 u (asucc g (asucc g a1))) (arity g c0 
t (asucc g a1)))))).(\lambda (t0: T).(\lambda (a2: A).(\lambda (_: (arity g 
(CHead c0 (Bind Abst) u0) t0 a2)).(\lambda (_: (((eq T t0 (THead (Flat Cast) 
u t)) \to (land (arity g (CHead c0 (Bind Abst) u0) u (asucc g a2)) (arity g 
(CHead c0 (Bind Abst) u0) t a2))))).(\lambda (H5: (eq T (THead (Bind Abst) u0 
t0) (THead (Flat Cast) u t))).(let H6 \def (eq_ind T (THead (Bind Abst) u0 
t0) (\lambda (ee: T).(match ee in T return (\lambda (_: T).Prop) with [(TSort 
_) \Rightarrow False | (TLRef _) \Rightarrow False | (THead k _ _) 
\Rightarrow (match k in K return (\lambda (_: K).Prop) with [(Bind _) 
\Rightarrow True | (Flat _) \Rightarrow False])])) I (THead (Flat Cast) u t) 
H5) in (False_ind (land (arity g c0 u (asucc g (AHead a1 a2))) (arity g c0 t 
(AHead a1 a2))) H6)))))))))))) (\lambda (c0: C).(\lambda (u0: T).(\lambda 
(a1: A).(\lambda (_: (arity g c0 u0 a1)).(\lambda (_: (((eq T u0 (THead (Flat 
Cast) u t)) \to (land (arity g c0 u (asucc g a1)) (arity g c0 t 
a1))))).(\lambda (t0: T).(\lambda (a2: A).(\lambda (_: (arity g c0 t0 (AHead 
a1 a2))).(\lambda (_: (((eq T t0 (THead (Flat Cast) u t)) \to (land (arity g 
c0 u (asucc g (AHead a1 a2))) (arity g c0 t (AHead a1 a2)))))).(\lambda (H5: 
(eq T (THead (Flat Appl) u0 t0) (THead (Flat Cast) u t))).(let H6 \def 
(eq_ind T (THead (Flat Appl) u0 t0) (\lambda (ee: T).(match ee in T return 
(\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow False | (THead k _ _) \Rightarrow (match k in K return (\lambda 
(_: K).Prop) with [(Bind _) \Rightarrow False | (Flat f) \Rightarrow (match f 
in F return (\lambda (_: F).Prop) with [Appl \Rightarrow True | Cast 
\Rightarrow False])])])) I (THead (Flat Cast) u t) H5) in (False_ind (land 
(arity g c0 u (asucc g a2)) (arity g c0 t a2)) H6)))))))))))) (\lambda (c0: 
C).(\lambda (u0: T).(\lambda (a0: A).(\lambda (H1: (arity g c0 u0 (asucc g 
a0))).(\lambda (H2: (((eq T u0 (THead (Flat Cast) u t)) \to (land (arity g c0 
u (asucc g (asucc g a0))) (arity g c0 t (asucc g a0)))))).(\lambda (t0: 
T).(\lambda (H3: (arity g c0 t0 a0)).(\lambda (H4: (((eq T t0 (THead (Flat 
Cast) u t)) \to (land (arity g c0 u (asucc g a0)) (arity g c0 t 
a0))))).(\lambda (H5: (eq T (THead (Flat Cast) u0 t0) (THead (Flat Cast) u 
t))).(let H6 \def (f_equal T T (\lambda (e: T).(match e in T return (\lambda 
(_: T).T) with [(TSort _) \Rightarrow u0 | (TLRef _) \Rightarrow u0 | (THead 
_ t1 _) \Rightarrow t1])) (THead (Flat Cast) u0 t0) (THead (Flat Cast) u t) 
H5) in ((let H7 \def (f_equal T T (\lambda (e: T).(match e in T return 
(\lambda (_: T).T) with [(TSort _) \Rightarrow t0 | (TLRef _) \Rightarrow t0 
| (THead _ _ t1) \Rightarrow t1])) (THead (Flat Cast) u0 t0) (THead (Flat 
Cast) u t) H5) in (\lambda (H8: (eq T u0 u)).(let H9 \def (eq_ind T t0 
(\lambda (t1: T).((eq T t1 (THead (Flat Cast) u t)) \to (land (arity g c0 u 
(asucc g a0)) (arity g c0 t a0)))) H4 t H7) in (let H10 \def (eq_ind T t0 
(\lambda (t1: T).(arity g c0 t1 a0)) H3 t H7) in (let H11 \def (eq_ind T u0 
(\lambda (t1: T).((eq T t1 (THead (Flat Cast) u t)) \to (land (arity g c0 u 
(asucc g (asucc g a0))) (arity g c0 t (asucc g a0))))) H2 u H8) in (let H12 
\def (eq_ind T u0 (\lambda (t1: T).(arity g c0 t1 (asucc g a0))) H1 u H8) in 
(conj (arity g c0 u (asucc g a0)) (arity g c0 t a0) H12 H10))))))) 
H6))))))))))) (\lambda (c0: C).(\lambda (t0: T).(\lambda (a1: A).(\lambda 
(H1: (arity g c0 t0 a1)).(\lambda (H2: (((eq T t0 (THead (Flat Cast) u t)) 
\to (land (arity g c0 u (asucc g a1)) (arity g c0 t a1))))).(\lambda (a2: 
A).(\lambda (H3: (leq g a1 a2)).(\lambda (H4: (eq T t0 (THead (Flat Cast) u 
t))).(let H5 \def (f_equal T T (\lambda (e: T).e) t0 (THead (Flat Cast) u t) 
H4) in (let H6 \def (eq_ind T t0 (\lambda (t1: T).((eq T t1 (THead (Flat 
Cast) u t)) \to (land (arity g c0 u (asucc g a1)) (arity g c0 t a1)))) H2 
(THead (Flat Cast) u t) H5) in (let H7 \def (eq_ind T t0 (\lambda (t1: 
T).(arity g c0 t1 a1)) H1 (THead (Flat Cast) u t) H5) in (let H8 \def (H6 
(refl_equal T (THead (Flat Cast) u t))) in (land_ind (arity g c0 u (asucc g 
a1)) (arity g c0 t a1) (land (arity g c0 u (asucc g a2)) (arity g c0 t a2)) 
(\lambda (H9: (arity g c0 u (asucc g a1))).(\lambda (H10: (arity g c0 t 
a1)).(conj (arity g c0 u (asucc g a2)) (arity g c0 t a2) (arity_repl g c0 u 
(asucc g a1) H9 (asucc g a2) (asucc_repl g a1 a2 H3)) (arity_repl g c0 t a1 
H10 a2 H3)))) H8))))))))))))) c y a H0))) H)))))).
(* COMMENTS
Initial nodes: 2147
END *)

theorem arity_gen_appls:
 \forall (g: G).(\forall (c: C).(\forall (t: T).(\forall (vs: TList).(\forall 
(a2: A).((arity g c (THeads (Flat Appl) vs t) a2) \to (ex A (\lambda (a: 
A).(arity g c t a))))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (t: T).(\lambda (vs: 
TList).(TList_ind (\lambda (t0: TList).(\forall (a2: A).((arity g c (THeads 
(Flat Appl) t0 t) a2) \to (ex A (\lambda (a: A).(arity g c t a)))))) (\lambda 
(a2: A).(\lambda (H: (arity g c t a2)).(ex_intro A (\lambda (a: A).(arity g c 
t a)) a2 H))) (\lambda (t0: T).(\lambda (t1: TList).(\lambda (H: ((\forall 
(a2: A).((arity g c (THeads (Flat Appl) t1 t) a2) \to (ex A (\lambda (a: 
A).(arity g c t a))))))).(\lambda (a2: A).(\lambda (H0: (arity g c (THead 
(Flat Appl) t0 (THeads (Flat Appl) t1 t)) a2)).(let H1 \def (arity_gen_appl g 
c t0 (THeads (Flat Appl) t1 t) a2 H0) in (ex2_ind A (\lambda (a1: A).(arity g 
c t0 a1)) (\lambda (a1: A).(arity g c (THeads (Flat Appl) t1 t) (AHead a1 
a2))) (ex A (\lambda (a: A).(arity g c t a))) (\lambda (x: A).(\lambda (_: 
(arity g c t0 x)).(\lambda (H3: (arity g c (THeads (Flat Appl) t1 t) (AHead x 
a2))).(let H_x \def (H (AHead x a2) H3) in (let H4 \def H_x in (ex_ind A 
(\lambda (a: A).(arity g c t a)) (ex A (\lambda (a: A).(arity g c t a))) 
(\lambda (x0: A).(\lambda (H5: (arity g c t x0)).(ex_intro A (\lambda (a: 
A).(arity g c t a)) x0 H5))) H4)))))) H1))))))) vs)))).
(* COMMENTS
Initial nodes: 341
END *)

theorem arity_gen_lift:
 \forall (g: G).(\forall (c1: C).(\forall (t: T).(\forall (a: A).(\forall (h: 
nat).(\forall (d: nat).((arity g c1 (lift h d t) a) \to (\forall (c2: 
C).((drop h d c1 c2) \to (arity g c2 t a)))))))))
\def
 \lambda (g: G).(\lambda (c1: C).(\lambda (t: T).(\lambda (a: A).(\lambda (h: 
nat).(\lambda (d: nat).(\lambda (H: (arity g c1 (lift h d t) a)).(insert_eq T 
(lift h d t) (\lambda (t0: T).(arity g c1 t0 a)) (\lambda (_: T).(\forall 
(c2: C).((drop h d c1 c2) \to (arity g c2 t a)))) (\lambda (y: T).(\lambda 
(H0: (arity g c1 y a)).(unintro T t (\lambda (t0: T).((eq T y (lift h d t0)) 
\to (\forall (c2: C).((drop h d c1 c2) \to (arity g c2 t0 a))))) (unintro nat 
d (\lambda (n: nat).(\forall (x: T).((eq T y (lift h n x)) \to (\forall (c2: 
C).((drop h n c1 c2) \to (arity g c2 x a)))))) (arity_ind g (\lambda (c: 
C).(\lambda (t0: T).(\lambda (a0: A).(\forall (x: nat).(\forall (x0: T).((eq 
T t0 (lift h x x0)) \to (\forall (c2: C).((drop h x c c2) \to (arity g c2 x0 
a0))))))))) (\lambda (c: C).(\lambda (n: nat).(\lambda (x: nat).(\lambda (x0: 
T).(\lambda (H1: (eq T (TSort n) (lift h x x0))).(\lambda (c2: C).(\lambda 
(_: (drop h x c c2)).(eq_ind_r T (TSort n) (\lambda (t0: T).(arity g c2 t0 
(ASort O n))) (arity_sort g c2 n) x0 (lift_gen_sort h x n x0 H1))))))))) 
(\lambda (c: C).(\lambda (d0: C).(\lambda (u: T).(\lambda (i: nat).(\lambda 
(H1: (getl i c (CHead d0 (Bind Abbr) u))).(\lambda (a0: A).(\lambda (H2: 
(arity g d0 u a0)).(\lambda (H3: ((\forall (x: nat).(\forall (x0: T).((eq T u 
(lift h x x0)) \to (\forall (c2: C).((drop h x d0 c2) \to (arity g c2 x0 
a0)))))))).(\lambda (x: nat).(\lambda (x0: T).(\lambda (H4: (eq T (TLRef i) 
(lift h x x0))).(\lambda (c2: C).(\lambda (H5: (drop h x c c2)).(let H_x \def 
(lift_gen_lref x0 x h i H4) in (let H6 \def H_x in (or_ind (land (lt i x) (eq 
T x0 (TLRef i))) (land (le (plus x h) i) (eq T x0 (TLRef (minus i h)))) 
(arity g c2 x0 a0) (\lambda (H7: (land (lt i x) (eq T x0 (TLRef 
i)))).(land_ind (lt i x) (eq T x0 (TLRef i)) (arity g c2 x0 a0) (\lambda (H8: 
(lt i x)).(\lambda (H9: (eq T x0 (TLRef i))).(eq_ind_r T (TLRef i) (\lambda 
(t0: T).(arity g c2 t0 a0)) (let H10 \def (eq_ind nat x (\lambda (n: 
nat).(drop h n c c2)) H5 (S (plus i (minus x (S i)))) (lt_plus_minus i x H8)) 
in (ex3_2_ind T C (\lambda (v: T).(\lambda (_: C).(eq T u (lift h (minus x (S 
i)) v)))) (\lambda (v: T).(\lambda (e0: C).(getl i c2 (CHead e0 (Bind Abbr) 
v)))) (\lambda (_: T).(\lambda (e0: C).(drop h (minus x (S i)) d0 e0))) 
(arity g c2 (TLRef i) a0) (\lambda (x1: T).(\lambda (x2: C).(\lambda (H11: 
(eq T u (lift h (minus x (S i)) x1))).(\lambda (H12: (getl i c2 (CHead x2 
(Bind Abbr) x1))).(\lambda (H13: (drop h (minus x (S i)) d0 x2)).(let H14 
\def (eq_ind T u (\lambda (t0: T).(\forall (x3: nat).(\forall (x4: T).((eq T 
t0 (lift h x3 x4)) \to (\forall (c3: C).((drop h x3 d0 c3) \to (arity g c3 x4 
a0))))))) H3 (lift h (minus x (S i)) x1) H11) in (let H15 \def (eq_ind T u 
(\lambda (t0: T).(arity g d0 t0 a0)) H2 (lift h (minus x (S i)) x1) H11) in 
(arity_abbr g c2 x2 x1 i H12 a0 (H14 (minus x (S i)) x1 (refl_equal T (lift h 
(minus x (S i)) x1)) x2 H13))))))))) (getl_drop_conf_lt Abbr c d0 u i H1 c2 h 
(minus x (S i)) H10))) x0 H9))) H7)) (\lambda (H7: (land (le (plus x h) i) 
(eq T x0 (TLRef (minus i h))))).(land_ind (le (plus x h) i) (eq T x0 (TLRef 
(minus i h))) (arity g c2 x0 a0) (\lambda (H8: (le (plus x h) i)).(\lambda 
(H9: (eq T x0 (TLRef (minus i h)))).(eq_ind_r T (TLRef (minus i h)) (\lambda 
(t0: T).(arity g c2 t0 a0)) (arity_abbr g c2 d0 u (minus i h) 
(getl_drop_conf_ge i (CHead d0 (Bind Abbr) u) c H1 c2 h x H5 H8) a0 H2) x0 
H9))) H7)) H6)))))))))))))))) (\lambda (c: C).(\lambda (d0: C).(\lambda (u: 
T).(\lambda (i: nat).(\lambda (H1: (getl i c (CHead d0 (Bind Abst) 
u))).(\lambda (a0: A).(\lambda (H2: (arity g d0 u (asucc g a0))).(\lambda 
(H3: ((\forall (x: nat).(\forall (x0: T).((eq T u (lift h x x0)) \to (\forall 
(c2: C).((drop h x d0 c2) \to (arity g c2 x0 (asucc g a0))))))))).(\lambda 
(x: nat).(\lambda (x0: T).(\lambda (H4: (eq T (TLRef i) (lift h x 
x0))).(\lambda (c2: C).(\lambda (H5: (drop h x c c2)).(let H_x \def 
(lift_gen_lref x0 x h i H4) in (let H6 \def H_x in (or_ind (land (lt i x) (eq 
T x0 (TLRef i))) (land (le (plus x h) i) (eq T x0 (TLRef (minus i h)))) 
(arity g c2 x0 a0) (\lambda (H7: (land (lt i x) (eq T x0 (TLRef 
i)))).(land_ind (lt i x) (eq T x0 (TLRef i)) (arity g c2 x0 a0) (\lambda (H8: 
(lt i x)).(\lambda (H9: (eq T x0 (TLRef i))).(eq_ind_r T (TLRef i) (\lambda 
(t0: T).(arity g c2 t0 a0)) (let H10 \def (eq_ind nat x (\lambda (n: 
nat).(drop h n c c2)) H5 (S (plus i (minus x (S i)))) (lt_plus_minus i x H8)) 
in (ex3_2_ind T C (\lambda (v: T).(\lambda (_: C).(eq T u (lift h (minus x (S 
i)) v)))) (\lambda (v: T).(\lambda (e0: C).(getl i c2 (CHead e0 (Bind Abst) 
v)))) (\lambda (_: T).(\lambda (e0: C).(drop h (minus x (S i)) d0 e0))) 
(arity g c2 (TLRef i) a0) (\lambda (x1: T).(\lambda (x2: C).(\lambda (H11: 
(eq T u (lift h (minus x (S i)) x1))).(\lambda (H12: (getl i c2 (CHead x2 
(Bind Abst) x1))).(\lambda (H13: (drop h (minus x (S i)) d0 x2)).(let H14 
\def (eq_ind T u (\lambda (t0: T).(\forall (x3: nat).(\forall (x4: T).((eq T 
t0 (lift h x3 x4)) \to (\forall (c3: C).((drop h x3 d0 c3) \to (arity g c3 x4 
(asucc g a0)))))))) H3 (lift h (minus x (S i)) x1) H11) in (let H15 \def 
(eq_ind T u (\lambda (t0: T).(arity g d0 t0 (asucc g a0))) H2 (lift h (minus 
x (S i)) x1) H11) in (arity_abst g c2 x2 x1 i H12 a0 (H14 (minus x (S i)) x1 
(refl_equal T (lift h (minus x (S i)) x1)) x2 H13))))))))) (getl_drop_conf_lt 
Abst c d0 u i H1 c2 h (minus x (S i)) H10))) x0 H9))) H7)) (\lambda (H7: 
(land (le (plus x h) i) (eq T x0 (TLRef (minus i h))))).(land_ind (le (plus x 
h) i) (eq T x0 (TLRef (minus i h))) (arity g c2 x0 a0) (\lambda (H8: (le 
(plus x h) i)).(\lambda (H9: (eq T x0 (TLRef (minus i h)))).(eq_ind_r T 
(TLRef (minus i h)) (\lambda (t0: T).(arity g c2 t0 a0)) (arity_abst g c2 d0 
u (minus i h) (getl_drop_conf_ge i (CHead d0 (Bind Abst) u) c H1 c2 h x H5 
H8) a0 H2) x0 H9))) H7)) H6)))))))))))))))) (\lambda (b: B).(\lambda (H1: 
(not (eq B b Abst))).(\lambda (c: C).(\lambda (u: T).(\lambda (a1: 
A).(\lambda (H2: (arity g c u a1)).(\lambda (H3: ((\forall (x: nat).(\forall 
(x0: T).((eq T u (lift h x x0)) \to (\forall (c2: C).((drop h x c c2) \to 
(arity g c2 x0 a1)))))))).(\lambda (t0: T).(\lambda (a2: A).(\lambda (H4: 
(arity g (CHead c (Bind b) u) t0 a2)).(\lambda (H5: ((\forall (x: 
nat).(\forall (x0: T).((eq T t0 (lift h x x0)) \to (\forall (c2: C).((drop h 
x (CHead c (Bind b) u) c2) \to (arity g c2 x0 a2)))))))).(\lambda (x: 
nat).(\lambda (x0: T).(\lambda (H6: (eq T (THead (Bind b) u t0) (lift h x 
x0))).(\lambda (c2: C).(\lambda (H7: (drop h x c c2)).(ex3_2_ind T T (\lambda 
(y0: T).(\lambda (z: T).(eq T x0 (THead (Bind b) y0 z)))) (\lambda (y0: 
T).(\lambda (_: T).(eq T u (lift h x y0)))) (\lambda (_: T).(\lambda (z: 
T).(eq T t0 (lift h (S x) z)))) (arity g c2 x0 a2) (\lambda (x1: T).(\lambda 
(x2: T).(\lambda (H8: (eq T x0 (THead (Bind b) x1 x2))).(\lambda (H9: (eq T u 
(lift h x x1))).(\lambda (H10: (eq T t0 (lift h (S x) x2))).(eq_ind_r T 
(THead (Bind b) x1 x2) (\lambda (t1: T).(arity g c2 t1 a2)) (let H11 \def 
(eq_ind T t0 (\lambda (t1: T).(\forall (x3: nat).(\forall (x4: T).((eq T t1 
(lift h x3 x4)) \to (\forall (c3: C).((drop h x3 (CHead c (Bind b) u) c3) \to 
(arity g c3 x4 a2))))))) H5 (lift h (S x) x2) H10) in (let H12 \def (eq_ind T 
t0 (\lambda (t1: T).(arity g (CHead c (Bind b) u) t1 a2)) H4 (lift h (S x) 
x2) H10) in (let H13 \def (eq_ind T u (\lambda (t1: T).(arity g (CHead c 
(Bind b) t1) (lift h (S x) x2) a2)) H12 (lift h x x1) H9) in (let H14 \def 
(eq_ind T u (\lambda (t1: T).(\forall (x3: nat).(\forall (x4: T).((eq T (lift 
h (S x) x2) (lift h x3 x4)) \to (\forall (c3: C).((drop h x3 (CHead c (Bind 
b) t1) c3) \to (arity g c3 x4 a2))))))) H11 (lift h x x1) H9) in (let H15 
\def (eq_ind T u (\lambda (t1: T).(\forall (x3: nat).(\forall (x4: T).((eq T 
t1 (lift h x3 x4)) \to (\forall (c3: C).((drop h x3 c c3) \to (arity g c3 x4 
a1))))))) H3 (lift h x x1) H9) in (let H16 \def (eq_ind T u (\lambda (t1: 
T).(arity g c t1 a1)) H2 (lift h x x1) H9) in (arity_bind g b H1 c2 x1 a1 
(H15 x x1 (refl_equal T (lift h x x1)) c2 H7) x2 a2 (H14 (S x) x2 (refl_equal 
T (lift h (S x) x2)) (CHead c2 (Bind b) x1) (drop_skip_bind h x c c2 H7 b 
x1))))))))) x0 H8)))))) (lift_gen_bind b u t0 x0 h x H6)))))))))))))))))) 
(\lambda (c: C).(\lambda (u: T).(\lambda (a1: A).(\lambda (H1: (arity g c u 
(asucc g a1))).(\lambda (H2: ((\forall (x: nat).(\forall (x0: T).((eq T u 
(lift h x x0)) \to (\forall (c2: C).((drop h x c c2) \to (arity g c2 x0 
(asucc g a1))))))))).(\lambda (t0: T).(\lambda (a2: A).(\lambda (H3: (arity g 
(CHead c (Bind Abst) u) t0 a2)).(\lambda (H4: ((\forall (x: nat).(\forall 
(x0: T).((eq T t0 (lift h x x0)) \to (\forall (c2: C).((drop h x (CHead c 
(Bind Abst) u) c2) \to (arity g c2 x0 a2)))))))).(\lambda (x: nat).(\lambda 
(x0: T).(\lambda (H5: (eq T (THead (Bind Abst) u t0) (lift h x x0))).(\lambda 
(c2: C).(\lambda (H6: (drop h x c c2)).(ex3_2_ind T T (\lambda (y0: 
T).(\lambda (z: T).(eq T x0 (THead (Bind Abst) y0 z)))) (\lambda (y0: 
T).(\lambda (_: T).(eq T u (lift h x y0)))) (\lambda (_: T).(\lambda (z: 
T).(eq T t0 (lift h (S x) z)))) (arity g c2 x0 (AHead a1 a2)) (\lambda (x1: 
T).(\lambda (x2: T).(\lambda (H7: (eq T x0 (THead (Bind Abst) x1 
x2))).(\lambda (H8: (eq T u (lift h x x1))).(\lambda (H9: (eq T t0 (lift h (S 
x) x2))).(eq_ind_r T (THead (Bind Abst) x1 x2) (\lambda (t1: T).(arity g c2 
t1 (AHead a1 a2))) (let H10 \def (eq_ind T t0 (\lambda (t1: T).(\forall (x3: 
nat).(\forall (x4: T).((eq T t1 (lift h x3 x4)) \to (\forall (c3: C).((drop h 
x3 (CHead c (Bind Abst) u) c3) \to (arity g c3 x4 a2))))))) H4 (lift h (S x) 
x2) H9) in (let H11 \def (eq_ind T t0 (\lambda (t1: T).(arity g (CHead c 
(Bind Abst) u) t1 a2)) H3 (lift h (S x) x2) H9) in (let H12 \def (eq_ind T u 
(\lambda (t1: T).(arity g (CHead c (Bind Abst) t1) (lift h (S x) x2) a2)) H11 
(lift h x x1) H8) in (let H13 \def (eq_ind T u (\lambda (t1: T).(\forall (x3: 
nat).(\forall (x4: T).((eq T (lift h (S x) x2) (lift h x3 x4)) \to (\forall 
(c3: C).((drop h x3 (CHead c (Bind Abst) t1) c3) \to (arity g c3 x4 a2))))))) 
H10 (lift h x x1) H8) in (let H14 \def (eq_ind T u (\lambda (t1: T).(\forall 
(x3: nat).(\forall (x4: T).((eq T t1 (lift h x3 x4)) \to (\forall (c3: 
C).((drop h x3 c c3) \to (arity g c3 x4 (asucc g a1)))))))) H2 (lift h x x1) 
H8) in (let H15 \def (eq_ind T u (\lambda (t1: T).(arity g c t1 (asucc g 
a1))) H1 (lift h x x1) H8) in (arity_head g c2 x1 a1 (H14 x x1 (refl_equal T 
(lift h x x1)) c2 H6) x2 a2 (H13 (S x) x2 (refl_equal T (lift h (S x) x2)) 
(CHead c2 (Bind Abst) x1) (drop_skip_bind h x c c2 H6 Abst x1))))))))) x0 
H7)))))) (lift_gen_bind Abst u t0 x0 h x H5)))))))))))))))) (\lambda (c: 
C).(\lambda (u: T).(\lambda (a1: A).(\lambda (H1: (arity g c u a1)).(\lambda 
(H2: ((\forall (x: nat).(\forall (x0: T).((eq T u (lift h x x0)) \to (\forall 
(c2: C).((drop h x c c2) \to (arity g c2 x0 a1)))))))).(\lambda (t0: 
T).(\lambda (a2: A).(\lambda (H3: (arity g c t0 (AHead a1 a2))).(\lambda (H4: 
((\forall (x: nat).(\forall (x0: T).((eq T t0 (lift h x x0)) \to (\forall 
(c2: C).((drop h x c c2) \to (arity g c2 x0 (AHead a1 a2))))))))).(\lambda 
(x: nat).(\lambda (x0: T).(\lambda (H5: (eq T (THead (Flat Appl) u t0) (lift 
h x x0))).(\lambda (c2: C).(\lambda (H6: (drop h x c c2)).(ex3_2_ind T T 
(\lambda (y0: T).(\lambda (z: T).(eq T x0 (THead (Flat Appl) y0 z)))) 
(\lambda (y0: T).(\lambda (_: T).(eq T u (lift h x y0)))) (\lambda (_: 
T).(\lambda (z: T).(eq T t0 (lift h x z)))) (arity g c2 x0 a2) (\lambda (x1: 
T).(\lambda (x2: T).(\lambda (H7: (eq T x0 (THead (Flat Appl) x1 
x2))).(\lambda (H8: (eq T u (lift h x x1))).(\lambda (H9: (eq T t0 (lift h x 
x2))).(eq_ind_r T (THead (Flat Appl) x1 x2) (\lambda (t1: T).(arity g c2 t1 
a2)) (let H10 \def (eq_ind T t0 (\lambda (t1: T).(\forall (x3: nat).(\forall 
(x4: T).((eq T t1 (lift h x3 x4)) \to (\forall (c3: C).((drop h x3 c c3) \to 
(arity g c3 x4 (AHead a1 a2)))))))) H4 (lift h x x2) H9) in (let H11 \def 
(eq_ind T t0 (\lambda (t1: T).(arity g c t1 (AHead a1 a2))) H3 (lift h x x2) 
H9) in (let H12 \def (eq_ind T u (\lambda (t1: T).(\forall (x3: nat).(\forall 
(x4: T).((eq T t1 (lift h x3 x4)) \to (\forall (c3: C).((drop h x3 c c3) \to 
(arity g c3 x4 a1))))))) H2 (lift h x x1) H8) in (let H13 \def (eq_ind T u 
(\lambda (t1: T).(arity g c t1 a1)) H1 (lift h x x1) H8) in (arity_appl g c2 
x1 a1 (H12 x x1 (refl_equal T (lift h x x1)) c2 H6) x2 a2 (H10 x x2 
(refl_equal T (lift h x x2)) c2 H6)))))) x0 H7)))))) (lift_gen_flat Appl u t0 
x0 h x H5)))))))))))))))) (\lambda (c: C).(\lambda (u: T).(\lambda (a0: 
A).(\lambda (H1: (arity g c u (asucc g a0))).(\lambda (H2: ((\forall (x: 
nat).(\forall (x0: T).((eq T u (lift h x x0)) \to (\forall (c2: C).((drop h x 
c c2) \to (arity g c2 x0 (asucc g a0))))))))).(\lambda (t0: T).(\lambda (H3: 
(arity g c t0 a0)).(\lambda (H4: ((\forall (x: nat).(\forall (x0: T).((eq T 
t0 (lift h x x0)) \to (\forall (c2: C).((drop h x c c2) \to (arity g c2 x0 
a0)))))))).(\lambda (x: nat).(\lambda (x0: T).(\lambda (H5: (eq T (THead 
(Flat Cast) u t0) (lift h x x0))).(\lambda (c2: C).(\lambda (H6: (drop h x c 
c2)).(ex3_2_ind T T (\lambda (y0: T).(\lambda (z: T).(eq T x0 (THead (Flat 
Cast) y0 z)))) (\lambda (y0: T).(\lambda (_: T).(eq T u (lift h x y0)))) 
(\lambda (_: T).(\lambda (z: T).(eq T t0 (lift h x z)))) (arity g c2 x0 a0) 
(\lambda (x1: T).(\lambda (x2: T).(\lambda (H7: (eq T x0 (THead (Flat Cast) 
x1 x2))).(\lambda (H8: (eq T u (lift h x x1))).(\lambda (H9: (eq T t0 (lift h 
x x2))).(eq_ind_r T (THead (Flat Cast) x1 x2) (\lambda (t1: T).(arity g c2 t1 
a0)) (let H10 \def (eq_ind T t0 (\lambda (t1: T).(\forall (x3: nat).(\forall 
(x4: T).((eq T t1 (lift h x3 x4)) \to (\forall (c3: C).((drop h x3 c c3) \to 
(arity g c3 x4 a0))))))) H4 (lift h x x2) H9) in (let H11 \def (eq_ind T t0 
(\lambda (t1: T).(arity g c t1 a0)) H3 (lift h x x2) H9) in (let H12 \def 
(eq_ind T u (\lambda (t1: T).(\forall (x3: nat).(\forall (x4: T).((eq T t1 
(lift h x3 x4)) \to (\forall (c3: C).((drop h x3 c c3) \to (arity g c3 x4 
(asucc g a0)))))))) H2 (lift h x x1) H8) in (let H13 \def (eq_ind T u 
(\lambda (t1: T).(arity g c t1 (asucc g a0))) H1 (lift h x x1) H8) in 
(arity_cast g c2 x1 a0 (H12 x x1 (refl_equal T (lift h x x1)) c2 H6) x2 (H10 
x x2 (refl_equal T (lift h x x2)) c2 H6)))))) x0 H7)))))) (lift_gen_flat Cast 
u t0 x0 h x H5))))))))))))))) (\lambda (c: C).(\lambda (t0: T).(\lambda (a1: 
A).(\lambda (_: (arity g c t0 a1)).(\lambda (H2: ((\forall (x: nat).(\forall 
(x0: T).((eq T t0 (lift h x x0)) \to (\forall (c2: C).((drop h x c c2) \to 
(arity g c2 x0 a1)))))))).(\lambda (a2: A).(\lambda (H3: (leq g a1 
a2)).(\lambda (x: nat).(\lambda (x0: T).(\lambda (H4: (eq T t0 (lift h x 
x0))).(\lambda (c2: C).(\lambda (H5: (drop h x c c2)).(arity_repl g c2 x0 a1 
(H2 x x0 H4 c2 H5) a2 H3))))))))))))) c1 y a H0))))) H))))))).
(* COMMENTS
Initial nodes: 4693
END *)

