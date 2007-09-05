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

set "baseuri" "cic:/matita/LAMBDA-TYPES/LambdaDelta-1/ty3/nf2".

include "ty3/arity.ma".

include "nf2/arity.ma".

theorem ty3_nf2_inv_all:
 \forall (g: G).(\forall (c: C).(\forall (t: T).(\forall (u: T).((ty3 g c t 
u) \to ((nf2 c t) \to (or3 (ex3_2 T T (\lambda (w: T).(\lambda (u0: T).(eq T 
t (THead (Bind Abst) w u0)))) (\lambda (w: T).(\lambda (_: T).(nf2 c w))) 
(\lambda (w: T).(\lambda (u0: T).(nf2 (CHead c (Bind Abst) w) u0)))) (ex nat 
(\lambda (n: nat).(eq T t (TSort n)))) (ex3_2 TList nat (\lambda (ws: 
TList).(\lambda (i: nat).(eq T t (THeads (Flat Appl) ws (TLRef i))))) 
(\lambda (ws: TList).(\lambda (_: nat).(nfs2 c ws))) (\lambda (_: 
TList).(\lambda (i: nat).(nf2 c (TLRef i)))))))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (t: T).(\lambda (u: T).(\lambda (H: 
(ty3 g c t u)).(\lambda (H0: (nf2 c t)).(let H_x \def (ty3_arity g c t u H) 
in (let H1 \def H_x in (ex2_ind A (\lambda (a1: A).(arity g c t a1)) (\lambda 
(a1: A).(arity g c u (asucc g a1))) (or3 (ex3_2 T T (\lambda (w: T).(\lambda 
(u0: T).(eq T t (THead (Bind Abst) w u0)))) (\lambda (w: T).(\lambda (_: 
T).(nf2 c w))) (\lambda (w: T).(\lambda (u0: T).(nf2 (CHead c (Bind Abst) w) 
u0)))) (ex nat (\lambda (n: nat).(eq T t (TSort n)))) (ex3_2 TList nat 
(\lambda (ws: TList).(\lambda (i: nat).(eq T t (THeads (Flat Appl) ws (TLRef 
i))))) (\lambda (ws: TList).(\lambda (_: nat).(nfs2 c ws))) (\lambda (_: 
TList).(\lambda (i: nat).(nf2 c (TLRef i)))))) (\lambda (x: A).(\lambda (H2: 
(arity g c t x)).(\lambda (_: (arity g c u (asucc g x))).(arity_nf2_inv_all g 
c t x H2 H0)))) H1)))))))).

theorem ty3_nf2_inv_sort:
 \forall (g: G).(\forall (c: C).(\forall (t: T).(\forall (m: nat).((ty3 g c t 
(TSort m)) \to ((nf2 c t) \to (or (ex2 nat (\lambda (n: nat).(eq T t (TSort 
n))) (\lambda (n: nat).(eq nat m (next g n)))) (ex3_2 TList nat (\lambda (ws: 
TList).(\lambda (i: nat).(eq T t (THeads (Flat Appl) ws (TLRef i))))) 
(\lambda (ws: TList).(\lambda (_: nat).(nfs2 c ws))) (\lambda (_: 
TList).(\lambda (i: nat).(nf2 c (TLRef i)))))))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (t: T).(\lambda (m: nat).(\lambda 
(H: (ty3 g c t (TSort m))).(\lambda (H0: (nf2 c t)).(let H_x \def 
(ty3_nf2_inv_all g c t (TSort m) H H0) in (let H1 \def H_x in (or3_ind (ex3_2 
T T (\lambda (w: T).(\lambda (u: T).(eq T t (THead (Bind Abst) w u)))) 
(\lambda (w: T).(\lambda (_: T).(nf2 c w))) (\lambda (w: T).(\lambda (u: 
T).(nf2 (CHead c (Bind Abst) w) u)))) (ex nat (\lambda (n: nat).(eq T t 
(TSort n)))) (ex3_2 TList nat (\lambda (ws: TList).(\lambda (i: nat).(eq T t 
(THeads (Flat Appl) ws (TLRef i))))) (\lambda (ws: TList).(\lambda (_: 
nat).(nfs2 c ws))) (\lambda (_: TList).(\lambda (i: nat).(nf2 c (TLRef i))))) 
(or (ex2 nat (\lambda (n: nat).(eq T t (TSort n))) (\lambda (n: nat).(eq nat 
m (next g n)))) (ex3_2 TList nat (\lambda (ws: TList).(\lambda (i: nat).(eq T 
t (THeads (Flat Appl) ws (TLRef i))))) (\lambda (ws: TList).(\lambda (_: 
nat).(nfs2 c ws))) (\lambda (_: TList).(\lambda (i: nat).(nf2 c (TLRef 
i)))))) (\lambda (H2: (ex3_2 T T (\lambda (w: T).(\lambda (u: T).(eq T t 
(THead (Bind Abst) w u)))) (\lambda (w: T).(\lambda (_: T).(nf2 c w))) 
(\lambda (w: T).(\lambda (u: T).(nf2 (CHead c (Bind Abst) w) 
u))))).(ex3_2_ind T T (\lambda (w: T).(\lambda (u: T).(eq T t (THead (Bind 
Abst) w u)))) (\lambda (w: T).(\lambda (_: T).(nf2 c w))) (\lambda (w: 
T).(\lambda (u: T).(nf2 (CHead c (Bind Abst) w) u))) (or (ex2 nat (\lambda 
(n: nat).(eq T t (TSort n))) (\lambda (n: nat).(eq nat m (next g n)))) (ex3_2 
TList nat (\lambda (ws: TList).(\lambda (i: nat).(eq T t (THeads (Flat Appl) 
ws (TLRef i))))) (\lambda (ws: TList).(\lambda (_: nat).(nfs2 c ws))) 
(\lambda (_: TList).(\lambda (i: nat).(nf2 c (TLRef i)))))) (\lambda (x0: 
T).(\lambda (x1: T).(\lambda (H3: (eq T t (THead (Bind Abst) x0 
x1))).(\lambda (_: (nf2 c x0)).(\lambda (_: (nf2 (CHead c (Bind Abst) x0) 
x1)).(let H6 \def (eq_ind T t (\lambda (t0: T).(ty3 g c t0 (TSort m))) H 
(THead (Bind Abst) x0 x1) H3) in (eq_ind_r T (THead (Bind Abst) x0 x1) 
(\lambda (t0: T).(or (ex2 nat (\lambda (n: nat).(eq T t0 (TSort n))) (\lambda 
(n: nat).(eq nat m (next g n)))) (ex3_2 TList nat (\lambda (ws: 
TList).(\lambda (i: nat).(eq T t0 (THeads (Flat Appl) ws (TLRef i))))) 
(\lambda (ws: TList).(\lambda (_: nat).(nfs2 c ws))) (\lambda (_: 
TList).(\lambda (i: nat).(nf2 c (TLRef i))))))) (ex4_3_ind T T T (\lambda 
(t2: T).(\lambda (_: T).(\lambda (_: T).(pc3 c (THead (Bind Abst) x0 t2) 
(TSort m))))) (\lambda (_: T).(\lambda (t0: T).(\lambda (_: T).(ty3 g c x0 
t0)))) (\lambda (t2: T).(\lambda (_: T).(\lambda (_: T).(ty3 g (CHead c (Bind 
Abst) x0) x1 t2)))) (\lambda (t2: T).(\lambda (_: T).(\lambda (t1: T).(ty3 g 
(CHead c (Bind Abst) x0) t2 t1)))) (or (ex2 nat (\lambda (n: nat).(eq T 
(THead (Bind Abst) x0 x1) (TSort n))) (\lambda (n: nat).(eq nat m (next g 
n)))) (ex3_2 TList nat (\lambda (ws: TList).(\lambda (i: nat).(eq T (THead 
(Bind Abst) x0 x1) (THeads (Flat Appl) ws (TLRef i))))) (\lambda (ws: 
TList).(\lambda (_: nat).(nfs2 c ws))) (\lambda (_: TList).(\lambda (i: 
nat).(nf2 c (TLRef i)))))) (\lambda (x2: T).(\lambda (x3: T).(\lambda (x4: 
T).(\lambda (H7: (pc3 c (THead (Bind Abst) x0 x2) (TSort m))).(\lambda (_: 
(ty3 g c x0 x3)).(\lambda (_: (ty3 g (CHead c (Bind Abst) x0) x1 
x2)).(\lambda (_: (ty3 g (CHead c (Bind Abst) x0) x2 x4)).(pc3_gen_sort_abst 
c x0 x2 m (pc3_s c (TSort m) (THead (Bind Abst) x0 x2) H7) (or (ex2 nat 
(\lambda (n: nat).(eq T (THead (Bind Abst) x0 x1) (TSort n))) (\lambda (n: 
nat).(eq nat m (next g n)))) (ex3_2 TList nat (\lambda (ws: TList).(\lambda 
(i: nat).(eq T (THead (Bind Abst) x0 x1) (THeads (Flat Appl) ws (TLRef i))))) 
(\lambda (ws: TList).(\lambda (_: nat).(nfs2 c ws))) (\lambda (_: 
TList).(\lambda (i: nat).(nf2 c (TLRef i)))))))))))))) (ty3_gen_bind g Abst c 
x0 x1 (TSort m) H6)) t H3))))))) H2)) (\lambda (H2: (ex nat (\lambda (n: 
nat).(eq T t (TSort n))))).(ex_ind nat (\lambda (n: nat).(eq T t (TSort n))) 
(or (ex2 nat (\lambda (n: nat).(eq T t (TSort n))) (\lambda (n: nat).(eq nat 
m (next g n)))) (ex3_2 TList nat (\lambda (ws: TList).(\lambda (i: nat).(eq T 
t (THeads (Flat Appl) ws (TLRef i))))) (\lambda (ws: TList).(\lambda (_: 
nat).(nfs2 c ws))) (\lambda (_: TList).(\lambda (i: nat).(nf2 c (TLRef 
i)))))) (\lambda (x: nat).(\lambda (H3: (eq T t (TSort x))).(let H4 \def 
(eq_ind T t (\lambda (t0: T).(ty3 g c t0 (TSort m))) H (TSort x) H3) in 
(eq_ind_r T (TSort x) (\lambda (t0: T).(or (ex2 nat (\lambda (n: nat).(eq T 
t0 (TSort n))) (\lambda (n: nat).(eq nat m (next g n)))) (ex3_2 TList nat 
(\lambda (ws: TList).(\lambda (i: nat).(eq T t0 (THeads (Flat Appl) ws (TLRef 
i))))) (\lambda (ws: TList).(\lambda (_: nat).(nfs2 c ws))) (\lambda (_: 
TList).(\lambda (i: nat).(nf2 c (TLRef i))))))) (eq_ind nat (next g x) 
(\lambda (n: nat).(or (ex2 nat (\lambda (n0: nat).(eq T (TSort x) (TSort 
n0))) (\lambda (n0: nat).(eq nat n (next g n0)))) (ex3_2 TList nat (\lambda 
(ws: TList).(\lambda (i: nat).(eq T (TSort x) (THeads (Flat Appl) ws (TLRef 
i))))) (\lambda (ws: TList).(\lambda (_: nat).(nfs2 c ws))) (\lambda (_: 
TList).(\lambda (i: nat).(nf2 c (TLRef i))))))) (or_introl (ex2 nat (\lambda 
(n: nat).(eq T (TSort x) (TSort n))) (\lambda (n: nat).(eq nat (next g x) 
(next g n)))) (ex3_2 TList nat (\lambda (ws: TList).(\lambda (i: nat).(eq T 
(TSort x) (THeads (Flat Appl) ws (TLRef i))))) (\lambda (ws: TList).(\lambda 
(_: nat).(nfs2 c ws))) (\lambda (_: TList).(\lambda (i: nat).(nf2 c (TLRef 
i))))) (ex_intro2 nat (\lambda (n: nat).(eq T (TSort x) (TSort n))) (\lambda 
(n: nat).(eq nat (next g x) (next g n))) x (refl_equal T (TSort x)) 
(refl_equal nat (next g x)))) m (pc3_gen_sort c (next g x) m (ty3_gen_sort g 
c (TSort m) x H4))) t H3)))) H2)) (\lambda (H2: (ex3_2 TList nat (\lambda 
(ws: TList).(\lambda (i: nat).(eq T t (THeads (Flat Appl) ws (TLRef i))))) 
(\lambda (ws: TList).(\lambda (_: nat).(nfs2 c ws))) (\lambda (_: 
TList).(\lambda (i: nat).(nf2 c (TLRef i)))))).(ex3_2_ind TList nat (\lambda 
(ws: TList).(\lambda (i: nat).(eq T t (THeads (Flat Appl) ws (TLRef i))))) 
(\lambda (ws: TList).(\lambda (_: nat).(nfs2 c ws))) (\lambda (_: 
TList).(\lambda (i: nat).(nf2 c (TLRef i)))) (or (ex2 nat (\lambda (n: 
nat).(eq T t (TSort n))) (\lambda (n: nat).(eq nat m (next g n)))) (ex3_2 
TList nat (\lambda (ws: TList).(\lambda (i: nat).(eq T t (THeads (Flat Appl) 
ws (TLRef i))))) (\lambda (ws: TList).(\lambda (_: nat).(nfs2 c ws))) 
(\lambda (_: TList).(\lambda (i: nat).(nf2 c (TLRef i)))))) (\lambda (x0: 
TList).(\lambda (x1: nat).(\lambda (H3: (eq T t (THeads (Flat Appl) x0 (TLRef 
x1)))).(\lambda (H4: (nfs2 c x0)).(\lambda (H5: (nf2 c (TLRef x1))).(let H6 
\def (eq_ind T t (\lambda (t0: T).(ty3 g c t0 (TSort m))) H (THeads (Flat 
Appl) x0 (TLRef x1)) H3) in (eq_ind_r T (THeads (Flat Appl) x0 (TLRef x1)) 
(\lambda (t0: T).(or (ex2 nat (\lambda (n: nat).(eq T t0 (TSort n))) (\lambda 
(n: nat).(eq nat m (next g n)))) (ex3_2 TList nat (\lambda (ws: 
TList).(\lambda (i: nat).(eq T t0 (THeads (Flat Appl) ws (TLRef i))))) 
(\lambda (ws: TList).(\lambda (_: nat).(nfs2 c ws))) (\lambda (_: 
TList).(\lambda (i: nat).(nf2 c (TLRef i))))))) (or_intror (ex2 nat (\lambda 
(n: nat).(eq T (THeads (Flat Appl) x0 (TLRef x1)) (TSort n))) (\lambda (n: 
nat).(eq nat m (next g n)))) (ex3_2 TList nat (\lambda (ws: TList).(\lambda 
(i: nat).(eq T (THeads (Flat Appl) x0 (TLRef x1)) (THeads (Flat Appl) ws 
(TLRef i))))) (\lambda (ws: TList).(\lambda (_: nat).(nfs2 c ws))) (\lambda 
(_: TList).(\lambda (i: nat).(nf2 c (TLRef i))))) (ex3_2_intro TList nat 
(\lambda (ws: TList).(\lambda (i: nat).(eq T (THeads (Flat Appl) x0 (TLRef 
x1)) (THeads (Flat Appl) ws (TLRef i))))) (\lambda (ws: TList).(\lambda (_: 
nat).(nfs2 c ws))) (\lambda (_: TList).(\lambda (i: nat).(nf2 c (TLRef i)))) 
x0 x1 (refl_equal T (THeads (Flat Appl) x0 (TLRef x1))) H4 H5)) t H3))))))) 
H2)) H1)))))))).

