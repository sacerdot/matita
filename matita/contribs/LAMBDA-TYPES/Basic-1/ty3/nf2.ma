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

include "Basic-1/ty3/arity.ma".

include "Basic-1/pc3/nf2.ma".

include "Basic-1/nf2/arity.ma".

definition ty3_nf2_inv_abst_premise:
 C \to (T \to (T \to Prop))
\def
 \lambda (c: C).(\lambda (w: T).(\lambda (u: T).(\forall (d: C).(\forall (wi: 
T).(\forall (i: nat).((getl i c (CHead d (Bind Abst) wi)) \to (\forall (vs: 
TList).((pc3 c (THeads (Flat Appl) vs (lift (S i) O wi)) (THead (Bind Abst) w 
u)) \to False)))))))).

theorem ty3_nf2_inv_abst_premise_csort:
 \forall (w: T).(\forall (u: T).(\forall (m: nat).(ty3_nf2_inv_abst_premise 
(CSort m) w u)))
\def
 \lambda (w: T).(\lambda (u: T).(\lambda (m: nat).(\lambda (d: C).(\lambda 
(wi: T).(\lambda (i: nat).(\lambda (H: (getl i (CSort m) (CHead d (Bind Abst) 
wi))).(\lambda (vs: TList).(\lambda (_: (pc3 (CSort m) (THeads (Flat Appl) vs 
(lift (S i) O wi)) (THead (Bind Abst) w u))).(getl_gen_sort m i (CHead d 
(Bind Abst) wi) H False))))))))).
(* COMMENTS
Initial nodes: 85
END *)

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
(* COMMENTS
Initial nodes: 233
END *)

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
TList).(\lambda (i: nat).(nf2 c (TLRef i))))))) (ex3_2_ind T T (\lambda (t2: 
T).(\lambda (_: T).(pc3 c (THead (Bind Abst) x0 t2) (TSort m)))) (\lambda (_: 
T).(\lambda (t0: T).(ty3 g c x0 t0))) (\lambda (t2: T).(\lambda (_: T).(ty3 g 
(CHead c (Bind Abst) x0) x1 t2))) (or (ex2 nat (\lambda (n: nat).(eq T (THead 
(Bind Abst) x0 x1) (TSort n))) (\lambda (n: nat).(eq nat m (next g n)))) 
(ex3_2 TList nat (\lambda (ws: TList).(\lambda (i: nat).(eq T (THead (Bind 
Abst) x0 x1) (THeads (Flat Appl) ws (TLRef i))))) (\lambda (ws: 
TList).(\lambda (_: nat).(nfs2 c ws))) (\lambda (_: TList).(\lambda (i: 
nat).(nf2 c (TLRef i)))))) (\lambda (x2: T).(\lambda (x3: T).(\lambda (H7: 
(pc3 c (THead (Bind Abst) x0 x2) (TSort m))).(\lambda (_: (ty3 g c x0 
x3)).(\lambda (_: (ty3 g (CHead c (Bind Abst) x0) x1 x2)).(pc3_gen_sort_abst 
c x0 x2 m (pc3_s c (TSort m) (THead (Bind Abst) x0 x2) H7) (or (ex2 nat 
(\lambda (n: nat).(eq T (THead (Bind Abst) x0 x1) (TSort n))) (\lambda (n: 
nat).(eq nat m (next g n)))) (ex3_2 TList nat (\lambda (ws: TList).(\lambda 
(i: nat).(eq T (THead (Bind Abst) x0 x1) (THeads (Flat Appl) ws (TLRef i))))) 
(\lambda (ws: TList).(\lambda (_: nat).(nfs2 c ws))) (\lambda (_: 
TList).(\lambda (i: nat).(nf2 c (TLRef i)))))))))))) (ty3_gen_bind g Abst c 
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
(* COMMENTS
Initial nodes: 2045
END *)

theorem ty3_nf2_gen__ty3_nf2_inv_abst_aux:
 \forall (c: C).(\forall (w1: T).(\forall (u1: T).((ty3_nf2_inv_abst_premise 
c w1 u1) \to (\forall (t: T).(\forall (w2: T).(\forall (u2: T).((pc3 c (THead 
(Flat Appl) t (THead (Bind Abst) w2 u2)) (THead (Bind Abst) w1 u1)) \to 
(ty3_nf2_inv_abst_premise c w2 u2))))))))
\def
 \lambda (c: C).(\lambda (w1: T).(\lambda (u1: T).(\lambda (H: ((\forall (d: 
C).(\forall (wi: T).(\forall (i: nat).((getl i c (CHead d (Bind Abst) wi)) 
\to (\forall (vs: TList).((pc3 c (THeads (Flat Appl) vs (lift (S i) O wi)) 
(THead (Bind Abst) w1 u1)) \to False)))))))).(\lambda (t: T).(\lambda (w2: 
T).(\lambda (u2: T).(\lambda (H0: (pc3 c (THead (Flat Appl) t (THead (Bind 
Abst) w2 u2)) (THead (Bind Abst) w1 u1))).(\lambda (d: C).(\lambda (wi: 
T).(\lambda (i: nat).(\lambda (H1: (getl i c (CHead d (Bind Abst) 
wi))).(\lambda (vs: TList).(\lambda (H2: (pc3 c (THeads (Flat Appl) vs (lift 
(S i) O wi)) (THead (Bind Abst) w2 u2))).(H d wi i H1 (TCons t vs) (pc3_t 
(THead (Flat Appl) t (THead (Bind Abst) w2 u2)) c (THead (Flat Appl) t 
(THeads (Flat Appl) vs (lift (S i) O wi))) (pc3_thin_dx c (THeads (Flat Appl) 
vs (lift (S i) O wi)) (THead (Bind Abst) w2 u2) H2 t Appl) (THead (Bind Abst) 
w1 u1) H0))))))))))))))).
(* COMMENTS
Initial nodes: 271
END *)

theorem ty3_nf2_inv_abst:
 \forall (g: G).(\forall (c: C).(\forall (t: T).(\forall (w: T).(\forall (u: 
T).((ty3 g c t (THead (Bind Abst) w u)) \to ((nf2 c t) \to ((nf2 c w) \to 
((ty3_nf2_inv_abst_premise c w u) \to (ex4_2 T T (\lambda (v: T).(\lambda (_: 
T).(eq T t (THead (Bind Abst) w v)))) (\lambda (_: T).(\lambda (w0: T).(ty3 g 
c w w0))) (\lambda (v: T).(\lambda (_: T).(ty3 g (CHead c (Bind Abst) w) v 
u))) (\lambda (v: T).(\lambda (_: T).(nf2 (CHead c (Bind Abst) w) 
v))))))))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (t: T).(\lambda (w: T).(\lambda (u: 
T).(\lambda (H: (ty3 g c t (THead (Bind Abst) w u))).(\lambda (H0: (nf2 c 
t)).(\lambda (H1: (nf2 c w)).(\lambda (H2: (ty3_nf2_inv_abst_premise c w 
u)).(let H_x \def (ty3_nf2_inv_all g c t (THead (Bind Abst) w u) H H0) in 
(let H3 \def H_x in (or3_ind (ex3_2 T T (\lambda (w0: T).(\lambda (u0: T).(eq 
T t (THead (Bind Abst) w0 u0)))) (\lambda (w0: T).(\lambda (_: T).(nf2 c 
w0))) (\lambda (w0: T).(\lambda (u0: T).(nf2 (CHead c (Bind Abst) w0) u0)))) 
(ex nat (\lambda (n: nat).(eq T t (TSort n)))) (ex3_2 TList nat (\lambda (ws: 
TList).(\lambda (i: nat).(eq T t (THeads (Flat Appl) ws (TLRef i))))) 
(\lambda (ws: TList).(\lambda (_: nat).(nfs2 c ws))) (\lambda (_: 
TList).(\lambda (i: nat).(nf2 c (TLRef i))))) (ex4_2 T T (\lambda (v: 
T).(\lambda (_: T).(eq T t (THead (Bind Abst) w v)))) (\lambda (_: 
T).(\lambda (w0: T).(ty3 g c w w0))) (\lambda (v: T).(\lambda (_: T).(ty3 g 
(CHead c (Bind Abst) w) v u))) (\lambda (v: T).(\lambda (_: T).(nf2 (CHead c 
(Bind Abst) w) v)))) (\lambda (H4: (ex3_2 T T (\lambda (w0: T).(\lambda (u0: 
T).(eq T t (THead (Bind Abst) w0 u0)))) (\lambda (w0: T).(\lambda (_: T).(nf2 
c w0))) (\lambda (w0: T).(\lambda (u0: T).(nf2 (CHead c (Bind Abst) w0) 
u0))))).(ex3_2_ind T T (\lambda (w0: T).(\lambda (u0: T).(eq T t (THead (Bind 
Abst) w0 u0)))) (\lambda (w0: T).(\lambda (_: T).(nf2 c w0))) (\lambda (w0: 
T).(\lambda (u0: T).(nf2 (CHead c (Bind Abst) w0) u0))) (ex4_2 T T (\lambda 
(v: T).(\lambda (_: T).(eq T t (THead (Bind Abst) w v)))) (\lambda (_: 
T).(\lambda (w0: T).(ty3 g c w w0))) (\lambda (v: T).(\lambda (_: T).(ty3 g 
(CHead c (Bind Abst) w) v u))) (\lambda (v: T).(\lambda (_: T).(nf2 (CHead c 
(Bind Abst) w) v)))) (\lambda (x0: T).(\lambda (x1: T).(\lambda (H5: (eq T t 
(THead (Bind Abst) x0 x1))).(\lambda (H6: (nf2 c x0)).(\lambda (H7: (nf2 
(CHead c (Bind Abst) x0) x1)).(let H8 \def (eq_ind T t (\lambda (t0: T).(ty3 
g c t0 (THead (Bind Abst) w u))) H (THead (Bind Abst) x0 x1) H5) in (eq_ind_r 
T (THead (Bind Abst) x0 x1) (\lambda (t0: T).(ex4_2 T T (\lambda (v: 
T).(\lambda (_: T).(eq T t0 (THead (Bind Abst) w v)))) (\lambda (_: 
T).(\lambda (w0: T).(ty3 g c w w0))) (\lambda (v: T).(\lambda (_: T).(ty3 g 
(CHead c (Bind Abst) w) v u))) (\lambda (v: T).(\lambda (_: T).(nf2 (CHead c 
(Bind Abst) w) v))))) (ex_ind T (\lambda (t0: T).(ty3 g c (THead (Bind Abst) 
w u) t0)) (ex4_2 T T (\lambda (v: T).(\lambda (_: T).(eq T (THead (Bind Abst) 
x0 x1) (THead (Bind Abst) w v)))) (\lambda (_: T).(\lambda (w0: T).(ty3 g c w 
w0))) (\lambda (v: T).(\lambda (_: T).(ty3 g (CHead c (Bind Abst) w) v u))) 
(\lambda (v: T).(\lambda (_: T).(nf2 (CHead c (Bind Abst) w) v)))) (\lambda 
(x: T).(\lambda (H9: (ty3 g c (THead (Bind Abst) w u) x)).(ex3_2_ind T T 
(\lambda (t2: T).(\lambda (_: T).(pc3 c (THead (Bind Abst) w t2) x))) 
(\lambda (_: T).(\lambda (t0: T).(ty3 g c w t0))) (\lambda (t2: T).(\lambda 
(_: T).(ty3 g (CHead c (Bind Abst) w) u t2))) (ex4_2 T T (\lambda (v: 
T).(\lambda (_: T).(eq T (THead (Bind Abst) x0 x1) (THead (Bind Abst) w v)))) 
(\lambda (_: T).(\lambda (w0: T).(ty3 g c w w0))) (\lambda (v: T).(\lambda 
(_: T).(ty3 g (CHead c (Bind Abst) w) v u))) (\lambda (v: T).(\lambda (_: 
T).(nf2 (CHead c (Bind Abst) w) v)))) (\lambda (x2: T).(\lambda (x3: 
T).(\lambda (_: (pc3 c (THead (Bind Abst) w x2) x)).(\lambda (H11: (ty3 g c w 
x3)).(\lambda (H12: (ty3 g (CHead c (Bind Abst) w) u x2)).(ex3_2_ind T T 
(\lambda (t2: T).(\lambda (_: T).(pc3 c (THead (Bind Abst) x0 t2) (THead 
(Bind Abst) w u)))) (\lambda (_: T).(\lambda (t0: T).(ty3 g c x0 t0))) 
(\lambda (t2: T).(\lambda (_: T).(ty3 g (CHead c (Bind Abst) x0) x1 t2))) 
(ex4_2 T T (\lambda (v: T).(\lambda (_: T).(eq T (THead (Bind Abst) x0 x1) 
(THead (Bind Abst) w v)))) (\lambda (_: T).(\lambda (w0: T).(ty3 g c w w0))) 
(\lambda (v: T).(\lambda (_: T).(ty3 g (CHead c (Bind Abst) w) v u))) 
(\lambda (v: T).(\lambda (_: T).(nf2 (CHead c (Bind Abst) w) v)))) (\lambda 
(x4: T).(\lambda (x5: T).(\lambda (H13: (pc3 c (THead (Bind Abst) x0 x4) 
(THead (Bind Abst) w u))).(\lambda (_: (ty3 g c x0 x5)).(\lambda (H15: (ty3 g 
(CHead c (Bind Abst) x0) x1 x4)).(land_ind (pc3 c x0 w) (\forall (b: 
B).(\forall (u0: T).(pc3 (CHead c (Bind b) u0) x4 u))) (ex4_2 T T (\lambda 
(v: T).(\lambda (_: T).(eq T (THead (Bind Abst) x0 x1) (THead (Bind Abst) w 
v)))) (\lambda (_: T).(\lambda (w0: T).(ty3 g c w w0))) (\lambda (v: 
T).(\lambda (_: T).(ty3 g (CHead c (Bind Abst) w) v u))) (\lambda (v: 
T).(\lambda (_: T).(nf2 (CHead c (Bind Abst) w) v)))) (\lambda (H16: (pc3 c 
x0 w)).(\lambda (H17: ((\forall (b: B).(\forall (u0: T).(pc3 (CHead c (Bind 
b) u0) x4 u))))).(let H_y \def (pc3_nf2 c x0 w H16 H6 H1) in (let H18 \def 
(eq_ind T x0 (\lambda (t0: T).(ty3 g (CHead c (Bind Abst) t0) x1 x4)) H15 w 
H_y) in (let H19 \def (eq_ind T x0 (\lambda (t0: T).(nf2 (CHead c (Bind Abst) 
t0) x1)) H7 w H_y) in (eq_ind_r T w (\lambda (t0: T).(ex4_2 T T (\lambda (v: 
T).(\lambda (_: T).(eq T (THead (Bind Abst) t0 x1) (THead (Bind Abst) w v)))) 
(\lambda (_: T).(\lambda (w0: T).(ty3 g c w w0))) (\lambda (v: T).(\lambda 
(_: T).(ty3 g (CHead c (Bind Abst) w) v u))) (\lambda (v: T).(\lambda (_: 
T).(nf2 (CHead c (Bind Abst) w) v))))) (ex4_2_intro T T (\lambda (v: 
T).(\lambda (_: T).(eq T (THead (Bind Abst) w x1) (THead (Bind Abst) w v)))) 
(\lambda (_: T).(\lambda (w0: T).(ty3 g c w w0))) (\lambda (v: T).(\lambda 
(_: T).(ty3 g (CHead c (Bind Abst) w) v u))) (\lambda (v: T).(\lambda (_: 
T).(nf2 (CHead c (Bind Abst) w) v))) x1 x3 (refl_equal T (THead (Bind Abst) w 
x1)) H11 (ty3_conv g (CHead c (Bind Abst) w) u x2 H12 x1 x4 H18 (H17 Abst w)) 
H19) x0 H_y)))))) (pc3_gen_abst c x0 w x4 u H13))))))) (ty3_gen_bind g Abst c 
x0 x1 (THead (Bind Abst) w u) H8))))))) (ty3_gen_bind g Abst c w u x H9)))) 
(ty3_correct g c (THead (Bind Abst) x0 x1) (THead (Bind Abst) w u) H8)) t 
H5))))))) H4)) (\lambda (H4: (ex nat (\lambda (n: nat).(eq T t (TSort 
n))))).(ex_ind nat (\lambda (n: nat).(eq T t (TSort n))) (ex4_2 T T (\lambda 
(v: T).(\lambda (_: T).(eq T t (THead (Bind Abst) w v)))) (\lambda (_: 
T).(\lambda (w0: T).(ty3 g c w w0))) (\lambda (v: T).(\lambda (_: T).(ty3 g 
(CHead c (Bind Abst) w) v u))) (\lambda (v: T).(\lambda (_: T).(nf2 (CHead c 
(Bind Abst) w) v)))) (\lambda (x: nat).(\lambda (H5: (eq T t (TSort x))).(let 
H6 \def (eq_ind T t (\lambda (t0: T).(ty3 g c t0 (THead (Bind Abst) w u))) H 
(TSort x) H5) in (eq_ind_r T (TSort x) (\lambda (t0: T).(ex4_2 T T (\lambda 
(v: T).(\lambda (_: T).(eq T t0 (THead (Bind Abst) w v)))) (\lambda (_: 
T).(\lambda (w0: T).(ty3 g c w w0))) (\lambda (v: T).(\lambda (_: T).(ty3 g 
(CHead c (Bind Abst) w) v u))) (\lambda (v: T).(\lambda (_: T).(nf2 (CHead c 
(Bind Abst) w) v))))) (pc3_gen_sort_abst c w u (next g x) (ty3_gen_sort g c 
(THead (Bind Abst) w u) x H6) (ex4_2 T T (\lambda (v: T).(\lambda (_: T).(eq 
T (TSort x) (THead (Bind Abst) w v)))) (\lambda (_: T).(\lambda (w0: T).(ty3 
g c w w0))) (\lambda (v: T).(\lambda (_: T).(ty3 g (CHead c (Bind Abst) w) v 
u))) (\lambda (v: T).(\lambda (_: T).(nf2 (CHead c (Bind Abst) w) v))))) t 
H5)))) H4)) (\lambda (H4: (ex3_2 TList nat (\lambda (ws: TList).(\lambda (i: 
nat).(eq T t (THeads (Flat Appl) ws (TLRef i))))) (\lambda (ws: 
TList).(\lambda (_: nat).(nfs2 c ws))) (\lambda (_: TList).(\lambda (i: 
nat).(nf2 c (TLRef i)))))).(ex3_2_ind TList nat (\lambda (ws: TList).(\lambda 
(i: nat).(eq T t (THeads (Flat Appl) ws (TLRef i))))) (\lambda (ws: 
TList).(\lambda (_: nat).(nfs2 c ws))) (\lambda (_: TList).(\lambda (i: 
nat).(nf2 c (TLRef i)))) (ex4_2 T T (\lambda (v: T).(\lambda (_: T).(eq T t 
(THead (Bind Abst) w v)))) (\lambda (_: T).(\lambda (w0: T).(ty3 g c w w0))) 
(\lambda (v: T).(\lambda (_: T).(ty3 g (CHead c (Bind Abst) w) v u))) 
(\lambda (v: T).(\lambda (_: T).(nf2 (CHead c (Bind Abst) w) v)))) (\lambda 
(x0: TList).(\lambda (x1: nat).(\lambda (H5: (eq T t (THeads (Flat Appl) x0 
(TLRef x1)))).(\lambda (_: (nfs2 c x0)).(\lambda (H7: (nf2 c (TLRef 
x1))).(let H8 \def (eq_ind T t (\lambda (t0: T).(ty3 g c t0 (THead (Bind 
Abst) w u))) H (THeads (Flat Appl) x0 (TLRef x1)) H5) in (eq_ind_r T (THeads 
(Flat Appl) x0 (TLRef x1)) (\lambda (t0: T).(ex4_2 T T (\lambda (v: 
T).(\lambda (_: T).(eq T t0 (THead (Bind Abst) w v)))) (\lambda (_: 
T).(\lambda (w0: T).(ty3 g c w w0))) (\lambda (v: T).(\lambda (_: T).(ty3 g 
(CHead c (Bind Abst) w) v u))) (\lambda (v: T).(\lambda (_: T).(nf2 (CHead c 
(Bind Abst) w) v))))) (let H9 \def H2 in ((let H10 \def H8 in (unintro T u 
(\lambda (t0: T).((ty3 g c (THeads (Flat Appl) x0 (TLRef x1)) (THead (Bind 
Abst) w t0)) \to ((ty3_nf2_inv_abst_premise c w t0) \to (ex4_2 T T (\lambda 
(v: T).(\lambda (_: T).(eq T (THeads (Flat Appl) x0 (TLRef x1)) (THead (Bind 
Abst) w v)))) (\lambda (_: T).(\lambda (w0: T).(ty3 g c w w0))) (\lambda (v: 
T).(\lambda (_: T).(ty3 g (CHead c (Bind Abst) w) v t0))) (\lambda (v: 
T).(\lambda (_: T).(nf2 (CHead c (Bind Abst) w) v))))))) (unintro T w 
(\lambda (t0: T).(\forall (x: T).((ty3 g c (THeads (Flat Appl) x0 (TLRef x1)) 
(THead (Bind Abst) t0 x)) \to ((ty3_nf2_inv_abst_premise c t0 x) \to (ex4_2 T 
T (\lambda (v: T).(\lambda (_: T).(eq T (THeads (Flat Appl) x0 (TLRef x1)) 
(THead (Bind Abst) t0 v)))) (\lambda (_: T).(\lambda (w0: T).(ty3 g c t0 
w0))) (\lambda (v: T).(\lambda (_: T).(ty3 g (CHead c (Bind Abst) t0) v x))) 
(\lambda (v: T).(\lambda (_: T).(nf2 (CHead c (Bind Abst) t0) v)))))))) 
(TList_ind (\lambda (t0: TList).(\forall (x: T).(\forall (x2: T).((ty3 g c 
(THeads (Flat Appl) t0 (TLRef x1)) (THead (Bind Abst) x x2)) \to 
((ty3_nf2_inv_abst_premise c x x2) \to (ex4_2 T T (\lambda (v: T).(\lambda 
(_: T).(eq T (THeads (Flat Appl) t0 (TLRef x1)) (THead (Bind Abst) x v)))) 
(\lambda (_: T).(\lambda (w0: T).(ty3 g c x w0))) (\lambda (v: T).(\lambda 
(_: T).(ty3 g (CHead c (Bind Abst) x) v x2))) (\lambda (v: T).(\lambda (_: 
T).(nf2 (CHead c (Bind Abst) x) v))))))))) (\lambda (x: T).(\lambda (x2: 
T).(\lambda (H11: (ty3 g c (TLRef x1) (THead (Bind Abst) x x2))).(\lambda 
(H12: (ty3_nf2_inv_abst_premise c x x2)).(or_ind (ex3_3 C T T (\lambda (_: 
C).(\lambda (_: T).(\lambda (t0: T).(pc3 c (lift (S x1) O t0) (THead (Bind 
Abst) x x2))))) (\lambda (e: C).(\lambda (u0: T).(\lambda (_: T).(getl x1 c 
(CHead e (Bind Abbr) u0))))) (\lambda (e: C).(\lambda (u0: T).(\lambda (t0: 
T).(ty3 g e u0 t0))))) (ex3_3 C T T (\lambda (_: C).(\lambda (u0: T).(\lambda 
(_: T).(pc3 c (lift (S x1) O u0) (THead (Bind Abst) x x2))))) (\lambda (e: 
C).(\lambda (u0: T).(\lambda (_: T).(getl x1 c (CHead e (Bind Abst) u0))))) 
(\lambda (e: C).(\lambda (u0: T).(\lambda (t0: T).(ty3 g e u0 t0))))) (ex4_2 
T T (\lambda (v: T).(\lambda (_: T).(eq T (TLRef x1) (THead (Bind Abst) x 
v)))) (\lambda (_: T).(\lambda (w0: T).(ty3 g c x w0))) (\lambda (v: 
T).(\lambda (_: T).(ty3 g (CHead c (Bind Abst) x) v x2))) (\lambda (v: 
T).(\lambda (_: T).(nf2 (CHead c (Bind Abst) x) v)))) (\lambda (H13: (ex3_3 C 
T T (\lambda (_: C).(\lambda (_: T).(\lambda (t0: T).(pc3 c (lift (S x1) O 
t0) (THead (Bind Abst) x x2))))) (\lambda (e: C).(\lambda (u0: T).(\lambda 
(_: T).(getl x1 c (CHead e (Bind Abbr) u0))))) (\lambda (e: C).(\lambda (u0: 
T).(\lambda (t0: T).(ty3 g e u0 t0)))))).(ex3_3_ind C T T (\lambda (_: 
C).(\lambda (_: T).(\lambda (t0: T).(pc3 c (lift (S x1) O t0) (THead (Bind 
Abst) x x2))))) (\lambda (e: C).(\lambda (u0: T).(\lambda (_: T).(getl x1 c 
(CHead e (Bind Abbr) u0))))) (\lambda (e: C).(\lambda (u0: T).(\lambda (t0: 
T).(ty3 g e u0 t0)))) (ex4_2 T T (\lambda (v: T).(\lambda (_: T).(eq T (TLRef 
x1) (THead (Bind Abst) x v)))) (\lambda (_: T).(\lambda (w0: T).(ty3 g c x 
w0))) (\lambda (v: T).(\lambda (_: T).(ty3 g (CHead c (Bind Abst) x) v x2))) 
(\lambda (v: T).(\lambda (_: T).(nf2 (CHead c (Bind Abst) x) v)))) (\lambda 
(x3: C).(\lambda (x4: T).(\lambda (x5: T).(\lambda (_: (pc3 c (lift (S x1) O 
x5) (THead (Bind Abst) x x2))).(\lambda (H15: (getl x1 c (CHead x3 (Bind 
Abbr) x4))).(\lambda (_: (ty3 g x3 x4 x5)).(nf2_gen_lref c x3 x4 x1 H15 H7 
(ex4_2 T T (\lambda (v: T).(\lambda (_: T).(eq T (TLRef x1) (THead (Bind 
Abst) x v)))) (\lambda (_: T).(\lambda (w0: T).(ty3 g c x w0))) (\lambda (v: 
T).(\lambda (_: T).(ty3 g (CHead c (Bind Abst) x) v x2))) (\lambda (v: 
T).(\lambda (_: T).(nf2 (CHead c (Bind Abst) x) v))))))))))) H13)) (\lambda 
(H13: (ex3_3 C T T (\lambda (_: C).(\lambda (u0: T).(\lambda (_: T).(pc3 c 
(lift (S x1) O u0) (THead (Bind Abst) x x2))))) (\lambda (e: C).(\lambda (u0: 
T).(\lambda (_: T).(getl x1 c (CHead e (Bind Abst) u0))))) (\lambda (e: 
C).(\lambda (u0: T).(\lambda (t0: T).(ty3 g e u0 t0)))))).(ex3_3_ind C T T 
(\lambda (_: C).(\lambda (u0: T).(\lambda (_: T).(pc3 c (lift (S x1) O u0) 
(THead (Bind Abst) x x2))))) (\lambda (e: C).(\lambda (u0: T).(\lambda (_: 
T).(getl x1 c (CHead e (Bind Abst) u0))))) (\lambda (e: C).(\lambda (u0: 
T).(\lambda (t0: T).(ty3 g e u0 t0)))) (ex4_2 T T (\lambda (v: T).(\lambda 
(_: T).(eq T (TLRef x1) (THead (Bind Abst) x v)))) (\lambda (_: T).(\lambda 
(w0: T).(ty3 g c x w0))) (\lambda (v: T).(\lambda (_: T).(ty3 g (CHead c 
(Bind Abst) x) v x2))) (\lambda (v: T).(\lambda (_: T).(nf2 (CHead c (Bind 
Abst) x) v)))) (\lambda (x3: C).(\lambda (x4: T).(\lambda (x5: T).(\lambda 
(H14: (pc3 c (lift (S x1) O x4) (THead (Bind Abst) x x2))).(\lambda (H15: 
(getl x1 c (CHead x3 (Bind Abst) x4))).(\lambda (_: (ty3 g x3 x4 x5)).(let 
H_x0 \def (H12 x3 x4 x1 H15 TNil H14) in (let H17 \def H_x0 in (False_ind 
(ex4_2 T T (\lambda (v: T).(\lambda (_: T).(eq T (TLRef x1) (THead (Bind 
Abst) x v)))) (\lambda (_: T).(\lambda (w0: T).(ty3 g c x w0))) (\lambda (v: 
T).(\lambda (_: T).(ty3 g (CHead c (Bind Abst) x) v x2))) (\lambda (v: 
T).(\lambda (_: T).(nf2 (CHead c (Bind Abst) x) v)))) H17))))))))) H13)) 
(ty3_gen_lref g c (THead (Bind Abst) x x2) x1 H11)))))) (\lambda (t0: 
T).(\lambda (t1: TList).(\lambda (H11: ((\forall (x: T).(\forall (x2: 
T).((ty3 g c (THeads (Flat Appl) t1 (TLRef x1)) (THead (Bind Abst) x x2)) \to 
((ty3_nf2_inv_abst_premise c x x2) \to (ex4_2 T T (\lambda (v: T).(\lambda 
(_: T).(eq T (THeads (Flat Appl) t1 (TLRef x1)) (THead (Bind Abst) x v)))) 
(\lambda (_: T).(\lambda (w0: T).(ty3 g c x w0))) (\lambda (v: T).(\lambda 
(_: T).(ty3 g (CHead c (Bind Abst) x) v x2))) (\lambda (v: T).(\lambda (_: 
T).(nf2 (CHead c (Bind Abst) x) v)))))))))).(\lambda (x: T).(\lambda (x2: 
T).(\lambda (H12: (ty3 g c (THead (Flat Appl) t0 (THeads (Flat Appl) t1 
(TLRef x1))) (THead (Bind Abst) x x2))).(\lambda (H13: 
(ty3_nf2_inv_abst_premise c x x2)).(ex3_2_ind T T (\lambda (u0: T).(\lambda 
(t2: T).(pc3 c (THead (Flat Appl) t0 (THead (Bind Abst) u0 t2)) (THead (Bind 
Abst) x x2)))) (\lambda (u0: T).(\lambda (t2: T).(ty3 g c (THeads (Flat Appl) 
t1 (TLRef x1)) (THead (Bind Abst) u0 t2)))) (\lambda (u0: T).(\lambda (_: 
T).(ty3 g c t0 u0))) (ex4_2 T T (\lambda (v: T).(\lambda (_: T).(eq T (THead 
(Flat Appl) t0 (THeads (Flat Appl) t1 (TLRef x1))) (THead (Bind Abst) x v)))) 
(\lambda (_: T).(\lambda (w0: T).(ty3 g c x w0))) (\lambda (v: T).(\lambda 
(_: T).(ty3 g (CHead c (Bind Abst) x) v x2))) (\lambda (v: T).(\lambda (_: 
T).(nf2 (CHead c (Bind Abst) x) v)))) (\lambda (x3: T).(\lambda (x4: 
T).(\lambda (H14: (pc3 c (THead (Flat Appl) t0 (THead (Bind Abst) x3 x4)) 
(THead (Bind Abst) x x2))).(\lambda (H15: (ty3 g c (THeads (Flat Appl) t1 
(TLRef x1)) (THead (Bind Abst) x3 x4))).(\lambda (_: (ty3 g c t0 x3)).(let 
H_y \def (ty3_nf2_gen__ty3_nf2_inv_abst_aux c x x2 H13 t0 x3 x4 H14) in (let 
H_x0 \def (H11 x3 x4 H15 H_y) in (let H17 \def H_x0 in (ex4_2_ind T T 
(\lambda (v: T).(\lambda (_: T).(eq T (THeads (Flat Appl) t1 (TLRef x1)) 
(THead (Bind Abst) x3 v)))) (\lambda (_: T).(\lambda (w0: T).(ty3 g c x3 
w0))) (\lambda (v: T).(\lambda (_: T).(ty3 g (CHead c (Bind Abst) x3) v x4))) 
(\lambda (v: T).(\lambda (_: T).(nf2 (CHead c (Bind Abst) x3) v))) (ex4_2 T T 
(\lambda (v: T).(\lambda (_: T).(eq T (THead (Flat Appl) t0 (THeads (Flat 
Appl) t1 (TLRef x1))) (THead (Bind Abst) x v)))) (\lambda (_: T).(\lambda 
(w0: T).(ty3 g c x w0))) (\lambda (v: T).(\lambda (_: T).(ty3 g (CHead c 
(Bind Abst) x) v x2))) (\lambda (v: T).(\lambda (_: T).(nf2 (CHead c (Bind 
Abst) x) v)))) (\lambda (x5: T).(\lambda (x6: T).(\lambda (H18: (eq T (THeads 
(Flat Appl) t1 (TLRef x1)) (THead (Bind Abst) x3 x5))).(\lambda (_: (ty3 g c 
x3 x6)).(\lambda (_: (ty3 g (CHead c (Bind Abst) x3) x5 x4)).(\lambda (_: 
(nf2 (CHead c (Bind Abst) x3) x5)).(TList_ind (\lambda (t2: TList).((eq T 
(THeads (Flat Appl) t2 (TLRef x1)) (THead (Bind Abst) x3 x5)) \to (ex4_2 T T 
(\lambda (v: T).(\lambda (_: T).(eq T (THead (Flat Appl) t0 (THeads (Flat 
Appl) t2 (TLRef x1))) (THead (Bind Abst) x v)))) (\lambda (_: T).(\lambda 
(w0: T).(ty3 g c x w0))) (\lambda (v: T).(\lambda (_: T).(ty3 g (CHead c 
(Bind Abst) x) v x2))) (\lambda (v: T).(\lambda (_: T).(nf2 (CHead c (Bind 
Abst) x) v)))))) (\lambda (H22: (eq T (THeads (Flat Appl) TNil (TLRef x1)) 
(THead (Bind Abst) x3 x5))).(let H23 \def (eq_ind T (TLRef x1) (\lambda (ee: 
T).(match ee in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow 
False | (TLRef _) \Rightarrow True | (THead _ _ _) \Rightarrow False])) I 
(THead (Bind Abst) x3 x5) H22) in (False_ind (ex4_2 T T (\lambda (v: 
T).(\lambda (_: T).(eq T (THead (Flat Appl) t0 (THeads (Flat Appl) TNil 
(TLRef x1))) (THead (Bind Abst) x v)))) (\lambda (_: T).(\lambda (w0: T).(ty3 
g c x w0))) (\lambda (v: T).(\lambda (_: T).(ty3 g (CHead c (Bind Abst) x) v 
x2))) (\lambda (v: T).(\lambda (_: T).(nf2 (CHead c (Bind Abst) x) v)))) 
H23))) (\lambda (t2: T).(\lambda (t3: TList).(\lambda (_: (((eq T (THeads 
(Flat Appl) t3 (TLRef x1)) (THead (Bind Abst) x3 x5)) \to (ex4_2 T T (\lambda 
(v: T).(\lambda (_: T).(eq T (THead (Flat Appl) t0 (THeads (Flat Appl) t3 
(TLRef x1))) (THead (Bind Abst) x v)))) (\lambda (_: T).(\lambda (w0: T).(ty3 
g c x w0))) (\lambda (v: T).(\lambda (_: T).(ty3 g (CHead c (Bind Abst) x) v 
x2))) (\lambda (v: T).(\lambda (_: T).(nf2 (CHead c (Bind Abst) x) 
v))))))).(\lambda (H22: (eq T (THeads (Flat Appl) (TCons t2 t3) (TLRef x1)) 
(THead (Bind Abst) x3 x5))).(let H23 \def (eq_ind T (THead (Flat Appl) t2 
(THeads (Flat Appl) t3 (TLRef x1))) (\lambda (ee: T).(match ee in T return 
(\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow False | (THead k _ _) \Rightarrow (match k in K return (\lambda 
(_: K).Prop) with [(Bind _) \Rightarrow False | (Flat _) \Rightarrow 
True])])) I (THead (Bind Abst) x3 x5) H22) in (False_ind (ex4_2 T T (\lambda 
(v: T).(\lambda (_: T).(eq T (THead (Flat Appl) t0 (THeads (Flat Appl) (TCons 
t2 t3) (TLRef x1))) (THead (Bind Abst) x v)))) (\lambda (_: T).(\lambda (w0: 
T).(ty3 g c x w0))) (\lambda (v: T).(\lambda (_: T).(ty3 g (CHead c (Bind 
Abst) x) v x2))) (\lambda (v: T).(\lambda (_: T).(nf2 (CHead c (Bind Abst) x) 
v)))) H23)))))) t1 H18))))))) H17))))))))) (ty3_gen_appl g c t0 (THeads (Flat 
Appl) t1 (TLRef x1)) (THead (Bind Abst) x x2) H12))))))))) x0)) H10)) H9)) t 
H5))))))) H4)) H3))))))))))).
(* COMMENTS
Initial nodes: 5333
END *)

