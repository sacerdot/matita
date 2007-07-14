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

set "baseuri" "cic:/matita/LAMBDA-TYPES/LambdaDelta-1/spare".

include "theory.ma".

definition nfs2:
 C \to (TList \to Prop)
\def
 let rec nfs2 (c: C) (ts: TList) on ts: Prop \def (match ts with [TNil 
\Rightarrow True | (TCons t ts0) \Rightarrow (land (nf2 c t) (nfs2 c ts0))]) 
in nfs2.

theorem nf2_gen_beta:
 \forall (c: C).(\forall (u: T).(\forall (v: T).(\forall (t: T).((nf2 c 
(THead (Flat Appl) u (THead (Bind Abst) v t))) \to (\forall (P: Prop).P)))))
\def
 \lambda (c: C).(\lambda (u: T).(\lambda (v: T).(\lambda (t: T).(\lambda (H: 
((\forall (t2: T).((pr2 c (THead (Flat Appl) u (THead (Bind Abst) v t)) t2) 
\to (eq T (THead (Flat Appl) u (THead (Bind Abst) v t)) t2))))).(\lambda (P: 
Prop).(let H0 \def (eq_ind T (THead (Flat Appl) u (THead (Bind Abst) v t)) 
(\lambda (ee: T).(match ee in T return (\lambda (_: T).Prop) with [(TSort _) 
\Rightarrow False | (TLRef _) \Rightarrow False | (THead k _ _) \Rightarrow 
(match k in K return (\lambda (_: K).Prop) with [(Bind _) \Rightarrow False | 
(Flat _) \Rightarrow True])])) I (THead (Bind Abbr) u t) (H (THead (Bind 
Abbr) u t) (pr2_free c (THead (Flat Appl) u (THead (Bind Abst) v t)) (THead 
(Bind Abbr) u t) (pr0_beta v u u (pr0_refl u) t t (pr0_refl t))))) in 
(False_ind P H0))))))).

theorem nf2_gen__aux:
 \forall (b: B).(\forall (x: T).(\forall (u: T).(\forall (d: nat).((eq T 
(THead (Bind b) u (lift (S O) d x)) x) \to (\forall (P: Prop).P)))))
\def
 \lambda (b: B).(\lambda (x: T).(T_ind (\lambda (t: T).(\forall (u: 
T).(\forall (d: nat).((eq T (THead (Bind b) u (lift (S O) d t)) t) \to 
(\forall (P: Prop).P))))) (\lambda (n: nat).(\lambda (u: T).(\lambda (d: 
nat).(\lambda (H: (eq T (THead (Bind b) u (lift (S O) d (TSort n))) (TSort 
n))).(\lambda (P: Prop).(let H0 \def (eq_ind T (THead (Bind b) u (lift (S O) 
d (TSort n))) (\lambda (ee: T).(match ee in T return (\lambda (_: T).Prop) 
with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | (THead _ _ 
_) \Rightarrow True])) I (TSort n) H) in (False_ind P H0))))))) (\lambda (n: 
nat).(\lambda (u: T).(\lambda (d: nat).(\lambda (H: (eq T (THead (Bind b) u 
(lift (S O) d (TLRef n))) (TLRef n))).(\lambda (P: Prop).(let H0 \def (eq_ind 
T (THead (Bind b) u (lift (S O) d (TLRef n))) (\lambda (ee: T).(match ee in T 
return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow False | (THead _ _ _) \Rightarrow True])) I (TLRef n) H) in 
(False_ind P H0))))))) (\lambda (k: K).(\lambda (t: T).(\lambda (_: ((\forall 
(u: T).(\forall (d: nat).((eq T (THead (Bind b) u (lift (S O) d t)) t) \to 
(\forall (P: Prop).P)))))).(\lambda (t0: T).(\lambda (H0: ((\forall (u: 
T).(\forall (d: nat).((eq T (THead (Bind b) u (lift (S O) d t0)) t0) \to 
(\forall (P: Prop).P)))))).(\lambda (u: T).(\lambda (d: nat).(\lambda (H1: 
(eq T (THead (Bind b) u (lift (S O) d (THead k t t0))) (THead k t 
t0))).(\lambda (P: Prop).(let H2 \def (f_equal T K (\lambda (e: T).(match e 
in T return (\lambda (_: T).K) with [(TSort _) \Rightarrow (Bind b) | (TLRef 
_) \Rightarrow (Bind b) | (THead k0 _ _) \Rightarrow k0])) (THead (Bind b) u 
(lift (S O) d (THead k t t0))) (THead k t t0) H1) in ((let H3 \def (f_equal T 
T (\lambda (e: T).(match e in T return (\lambda (_: T).T) with [(TSort _) 
\Rightarrow u | (TLRef _) \Rightarrow u | (THead _ t1 _) \Rightarrow t1])) 
(THead (Bind b) u (lift (S O) d (THead k t t0))) (THead k t t0) H1) in ((let 
H4 \def (f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) 
with [(TSort _) \Rightarrow (THead k ((let rec lref_map (f: ((nat \to nat))) 
(d0: nat) (t1: T) on t1: T \def (match t1 with [(TSort n) \Rightarrow (TSort 
n) | (TLRef i) \Rightarrow (TLRef (match (blt i d0) with [true \Rightarrow i 
| false \Rightarrow (f i)])) | (THead k0 u0 t2) \Rightarrow (THead k0 
(lref_map f d0 u0) (lref_map f (s k0 d0) t2))]) in lref_map) (\lambda (x0: 
nat).(plus x0 (S O))) d t) ((let rec lref_map (f: ((nat \to nat))) (d0: nat) 
(t1: T) on t1: T \def (match t1 with [(TSort n) \Rightarrow (TSort n) | 
(TLRef i) \Rightarrow (TLRef (match (blt i d0) with [true \Rightarrow i | 
false \Rightarrow (f i)])) | (THead k0 u0 t2) \Rightarrow (THead k0 (lref_map 
f d0 u0) (lref_map f (s k0 d0) t2))]) in lref_map) (\lambda (x0: nat).(plus 
x0 (S O))) (s k d) t0)) | (TLRef _) \Rightarrow (THead k ((let rec lref_map 
(f: ((nat \to nat))) (d0: nat) (t1: T) on t1: T \def (match t1 with [(TSort 
n) \Rightarrow (TSort n) | (TLRef i) \Rightarrow (TLRef (match (blt i d0) 
with [true \Rightarrow i | false \Rightarrow (f i)])) | (THead k0 u0 t2) 
\Rightarrow (THead k0 (lref_map f d0 u0) (lref_map f (s k0 d0) t2))]) in 
lref_map) (\lambda (x0: nat).(plus x0 (S O))) d t) ((let rec lref_map (f: 
((nat \to nat))) (d0: nat) (t1: T) on t1: T \def (match t1 with [(TSort n) 
\Rightarrow (TSort n) | (TLRef i) \Rightarrow (TLRef (match (blt i d0) with 
[true \Rightarrow i | false \Rightarrow (f i)])) | (THead k0 u0 t2) 
\Rightarrow (THead k0 (lref_map f d0 u0) (lref_map f (s k0 d0) t2))]) in 
lref_map) (\lambda (x0: nat).(plus x0 (S O))) (s k d) t0)) | (THead _ _ t1) 
\Rightarrow t1])) (THead (Bind b) u (lift (S O) d (THead k t t0))) (THead k t 
t0) H1) in (\lambda (_: (eq T u t)).(\lambda (H6: (eq K (Bind b) k)).(let H7 
\def (eq_ind_r K k (\lambda (k0: K).(eq T (lift (S O) d (THead k0 t t0)) t0)) 
H4 (Bind b) H6) in (let H8 \def (eq_ind T (lift (S O) d (THead (Bind b) t 
t0)) (\lambda (t1: T).(eq T t1 t0)) H7 (THead (Bind b) (lift (S O) d t) (lift 
(S O) (S d) t0)) (lift_bind b t t0 (S O) d)) in (H0 (lift (S O) d t) (S d) H8 
P)))))) H3)) H2))))))))))) x)).

theorem nf2_gen_abbr:
 \forall (c: C).(\forall (u: T).(\forall (t: T).((nf2 c (THead (Bind Abbr) u 
t)) \to (\forall (P: Prop).P))))
\def
 \lambda (c: C).(\lambda (u: T).(\lambda (t: T).(\lambda (H: ((\forall (t2: 
T).((pr2 c (THead (Bind Abbr) u t) t2) \to (eq T (THead (Bind Abbr) u t) 
t2))))).(\lambda (P: Prop).(let H_x \def (dnf_dec u t O) in (let H0 \def H_x 
in (ex_ind T (\lambda (v: T).(or (subst0 O u t (lift (S O) O v)) (eq T t 
(lift (S O) O v)))) P (\lambda (x: T).(\lambda (H1: (or (subst0 O u t (lift 
(S O) O x)) (eq T t (lift (S O) O x)))).(or_ind (subst0 O u t (lift (S O) O 
x)) (eq T t (lift (S O) O x)) P (\lambda (H2: (subst0 O u t (lift (S O) O 
x))).(let H3 \def (f_equal T T (\lambda (e: T).(match e in T return (\lambda 
(_: T).T) with [(TSort _) \Rightarrow t | (TLRef _) \Rightarrow t | (THead _ 
_ t0) \Rightarrow t0])) (THead (Bind Abbr) u t) (THead (Bind Abbr) u (lift (S 
O) O x)) (H (THead (Bind Abbr) u (lift (S O) O x)) (pr2_free c (THead (Bind 
Abbr) u t) (THead (Bind Abbr) u (lift (S O) O x)) (pr0_delta u u (pr0_refl u) 
t t (pr0_refl t) (lift (S O) O x) H2)))) in (let H4 \def (eq_ind T t (\lambda 
(t0: T).(subst0 O u t0 (lift (S O) O x))) H2 (lift (S O) O x) H3) in 
(subst0_refl u (lift (S O) O x) O H4 P)))) (\lambda (H2: (eq T t (lift (S O) 
O x))).(let H3 \def (eq_ind T t (\lambda (t0: T).(\forall (t2: T).((pr2 c 
(THead (Bind Abbr) u t0) t2) \to (eq T (THead (Bind Abbr) u t0) t2)))) H 
(lift (S O) O x) H2) in (nf2_gen__aux Abbr x u O (H3 x (pr2_free c (THead 
(Bind Abbr) u (lift (S O) O x)) x (pr0_zeta Abbr not_abbr_abst x x (pr0_refl 
x) u))) P))) H1))) H0))))))).

theorem nf2_gen_void:
 \forall (c: C).(\forall (u: T).(\forall (t: T).((nf2 c (THead (Bind Void) u 
(lift (S O) O t))) \to (\forall (P: Prop).P))))
\def
 \lambda (c: C).(\lambda (u: T).(\lambda (t: T).(\lambda (H: ((\forall (t2: 
T).((pr2 c (THead (Bind Void) u (lift (S O) O t)) t2) \to (eq T (THead (Bind 
Void) u (lift (S O) O t)) t2))))).(\lambda (P: Prop).(nf2_gen__aux Void t u O 
(H t (pr2_free c (THead (Bind Void) u (lift (S O) O t)) t (pr0_zeta Void 
not_void_abst t t (pr0_refl t) u))) P))))).

theorem arity_nf2_inv_all:
 \forall (g: G).(\forall (c: C).(\forall (t: T).(\forall (a: A).((arity g c t 
a) \to ((nf2 c t) \to (or3 (ex3_2 T T (\lambda (w: T).(\lambda (u: T).(eq T t 
(THead (Bind Abst) w u)))) (\lambda (w: T).(\lambda (_: T).(nf2 c w))) 
(\lambda (w: T).(\lambda (u: T).(nf2 (CHead c (Bind Abst) w) u)))) (ex nat 
(\lambda (n: nat).(eq T t (TSort n)))) (ex3_4 TList nat C T (\lambda (ws: 
TList).(\lambda (i: nat).(\lambda (_: C).(\lambda (_: T).(eq T t (THeads 
(Flat Appl) ws (TLRef i))))))) (\lambda (_: TList).(\lambda (i: nat).(\lambda 
(d: C).(\lambda (v: T).(getl i c (CHead d (Bind Abst) v)))))) (\lambda (ws: 
TList).(\lambda (_: nat).(\lambda (_: C).(\lambda (_: T).(nfs2 c 
ws))))))))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (t: T).(\lambda (a: A).(\lambda (H: 
(arity g c t a)).(arity_ind g (\lambda (c0: C).(\lambda (t0: T).(\lambda (_: 
A).((nf2 c0 t0) \to (or3 (ex3_2 T T (\lambda (w: T).(\lambda (u: T).(eq T t0 
(THead (Bind Abst) w u)))) (\lambda (w: T).(\lambda (_: T).(nf2 c0 w))) 
(\lambda (w: T).(\lambda (u: T).(nf2 (CHead c0 (Bind Abst) w) u)))) (ex nat 
(\lambda (n: nat).(eq T t0 (TSort n)))) (ex3_4 TList nat C T (\lambda (ws: 
TList).(\lambda (i: nat).(\lambda (_: C).(\lambda (_: T).(eq T t0 (THeads 
(Flat Appl) ws (TLRef i))))))) (\lambda (_: TList).(\lambda (i: nat).(\lambda 
(d: C).(\lambda (v: T).(getl i c0 (CHead d (Bind Abst) v)))))) (\lambda (ws: 
TList).(\lambda (_: nat).(\lambda (_: C).(\lambda (_: T).(nfs2 c0 
ws))))))))))) (\lambda (c0: C).(\lambda (n: nat).(\lambda (_: (nf2 c0 (TSort 
n))).(or3_intro1 (ex3_2 T T (\lambda (w: T).(\lambda (u: T).(eq T (TSort n) 
(THead (Bind Abst) w u)))) (\lambda (w: T).(\lambda (_: T).(nf2 c0 w))) 
(\lambda (w: T).(\lambda (u: T).(nf2 (CHead c0 (Bind Abst) w) u)))) (ex nat 
(\lambda (n0: nat).(eq T (TSort n) (TSort n0)))) (ex3_4 TList nat C T 
(\lambda (ws: TList).(\lambda (i: nat).(\lambda (_: C).(\lambda (_: T).(eq T 
(TSort n) (THeads (Flat Appl) ws (TLRef i))))))) (\lambda (_: TList).(\lambda 
(i: nat).(\lambda (d: C).(\lambda (v: T).(getl i c0 (CHead d (Bind Abst) 
v)))))) (\lambda (ws: TList).(\lambda (_: nat).(\lambda (_: C).(\lambda (_: 
T).(nfs2 c0 ws)))))) (ex_intro nat (\lambda (n0: nat).(eq T (TSort n) (TSort 
n0))) n (refl_equal T (TSort n))))))) (\lambda (c0: C).(\lambda (d: 
C).(\lambda (u: T).(\lambda (i: nat).(\lambda (H0: (getl i c0 (CHead d (Bind 
Abbr) u))).(\lambda (a0: A).(\lambda (_: (arity g d u a0)).(\lambda (_: 
(((nf2 d u) \to (or3 (ex3_2 T T (\lambda (w: T).(\lambda (u0: T).(eq T u 
(THead (Bind Abst) w u0)))) (\lambda (w: T).(\lambda (_: T).(nf2 d w))) 
(\lambda (w: T).(\lambda (u0: T).(nf2 (CHead d (Bind Abst) w) u0)))) (ex nat 
(\lambda (n: nat).(eq T u (TSort n)))) (ex3_4 TList nat C T (\lambda (ws: 
TList).(\lambda (i0: nat).(\lambda (_: C).(\lambda (_: T).(eq T u (THeads 
(Flat Appl) ws (TLRef i0))))))) (\lambda (_: TList).(\lambda (i0: 
nat).(\lambda (d0: C).(\lambda (v: T).(getl i0 d (CHead d0 (Bind Abst) 
v)))))) (\lambda (ws: TList).(\lambda (_: nat).(\lambda (_: C).(\lambda (_: 
T).(nfs2 d ws)))))))))).(\lambda (H3: (nf2 c0 (TLRef i))).(nf2_gen_lref c0 d 
u i H0 H3 (or3 (ex3_2 T T (\lambda (w: T).(\lambda (u0: T).(eq T (TLRef i) 
(THead (Bind Abst) w u0)))) (\lambda (w: T).(\lambda (_: T).(nf2 c0 w))) 
(\lambda (w: T).(\lambda (u0: T).(nf2 (CHead c0 (Bind Abst) w) u0)))) (ex nat 
(\lambda (n: nat).(eq T (TLRef i) (TSort n)))) (ex3_4 TList nat C T (\lambda 
(ws: TList).(\lambda (i0: nat).(\lambda (_: C).(\lambda (_: T).(eq T (TLRef 
i) (THeads (Flat Appl) ws (TLRef i0))))))) (\lambda (_: TList).(\lambda (i0: 
nat).(\lambda (d0: C).(\lambda (v: T).(getl i0 c0 (CHead d0 (Bind Abst) 
v)))))) (\lambda (ws: TList).(\lambda (_: nat).(\lambda (_: C).(\lambda (_: 
T).(nfs2 c0 ws))))))))))))))))) (\lambda (c0: C).(\lambda (d: C).(\lambda (u: 
T).(\lambda (i: nat).(\lambda (H0: (getl i c0 (CHead d (Bind Abst) 
u))).(\lambda (a0: A).(\lambda (_: (arity g d u (asucc g a0))).(\lambda (_: 
(((nf2 d u) \to (or3 (ex3_2 T T (\lambda (w: T).(\lambda (u0: T).(eq T u 
(THead (Bind Abst) w u0)))) (\lambda (w: T).(\lambda (_: T).(nf2 d w))) 
(\lambda (w: T).(\lambda (u0: T).(nf2 (CHead d (Bind Abst) w) u0)))) (ex nat 
(\lambda (n: nat).(eq T u (TSort n)))) (ex3_4 TList nat C T (\lambda (ws: 
TList).(\lambda (i0: nat).(\lambda (_: C).(\lambda (_: T).(eq T u (THeads 
(Flat Appl) ws (TLRef i0))))))) (\lambda (_: TList).(\lambda (i0: 
nat).(\lambda (d0: C).(\lambda (v: T).(getl i0 d (CHead d0 (Bind Abst) 
v)))))) (\lambda (ws: TList).(\lambda (_: nat).(\lambda (_: C).(\lambda (_: 
T).(nfs2 d ws)))))))))).(\lambda (_: (nf2 c0 (TLRef i))).(or3_intro2 (ex3_2 T 
T (\lambda (w: T).(\lambda (u0: T).(eq T (TLRef i) (THead (Bind Abst) w 
u0)))) (\lambda (w: T).(\lambda (_: T).(nf2 c0 w))) (\lambda (w: T).(\lambda 
(u0: T).(nf2 (CHead c0 (Bind Abst) w) u0)))) (ex nat (\lambda (n: nat).(eq T 
(TLRef i) (TSort n)))) (ex3_4 TList nat C T (\lambda (ws: TList).(\lambda 
(i0: nat).(\lambda (_: C).(\lambda (_: T).(eq T (TLRef i) (THeads (Flat Appl) 
ws (TLRef i0))))))) (\lambda (_: TList).(\lambda (i0: nat).(\lambda (d0: 
C).(\lambda (v: T).(getl i0 c0 (CHead d0 (Bind Abst) v)))))) (\lambda (ws: 
TList).(\lambda (_: nat).(\lambda (_: C).(\lambda (_: T).(nfs2 c0 ws)))))) 
(ex3_4_intro TList nat C T (\lambda (ws: TList).(\lambda (i0: nat).(\lambda 
(_: C).(\lambda (_: T).(eq T (TLRef i) (THeads (Flat Appl) ws (TLRef 
i0))))))) (\lambda (_: TList).(\lambda (i0: nat).(\lambda (d0: C).(\lambda 
(v: T).(getl i0 c0 (CHead d0 (Bind Abst) v)))))) (\lambda (ws: 
TList).(\lambda (_: nat).(\lambda (_: C).(\lambda (_: T).(nfs2 c0 ws))))) 
TNil i d u (refl_equal T (TLRef i)) H0 I))))))))))) (\lambda (b: B).(\lambda 
(H0: (not (eq B b Abst))).(\lambda (c0: C).(\lambda (u: T).(\lambda (a1: 
A).(\lambda (_: (arity g c0 u a1)).(\lambda (_: (((nf2 c0 u) \to (or3 (ex3_2 
T T (\lambda (w: T).(\lambda (u0: T).(eq T u (THead (Bind Abst) w u0)))) 
(\lambda (w: T).(\lambda (_: T).(nf2 c0 w))) (\lambda (w: T).(\lambda (u0: 
T).(nf2 (CHead c0 (Bind Abst) w) u0)))) (ex nat (\lambda (n: nat).(eq T u 
(TSort n)))) (ex3_4 TList nat C T (\lambda (ws: TList).(\lambda (i: 
nat).(\lambda (_: C).(\lambda (_: T).(eq T u (THeads (Flat Appl) ws (TLRef 
i))))))) (\lambda (_: TList).(\lambda (i: nat).(\lambda (d: C).(\lambda (v: 
T).(getl i c0 (CHead d (Bind Abst) v)))))) (\lambda (ws: TList).(\lambda (_: 
nat).(\lambda (_: C).(\lambda (_: T).(nfs2 c0 ws)))))))))).(\lambda (t0: 
T).(\lambda (a2: A).(\lambda (H3: (arity g (CHead c0 (Bind b) u) t0 
a2)).(\lambda (_: (((nf2 (CHead c0 (Bind b) u) t0) \to (or3 (ex3_2 T T 
(\lambda (w: T).(\lambda (u0: T).(eq T t0 (THead (Bind Abst) w u0)))) 
(\lambda (w: T).(\lambda (_: T).(nf2 (CHead c0 (Bind b) u) w))) (\lambda (w: 
T).(\lambda (u0: T).(nf2 (CHead (CHead c0 (Bind b) u) (Bind Abst) w) u0)))) 
(ex nat (\lambda (n: nat).(eq T t0 (TSort n)))) (ex3_4 TList nat C T (\lambda 
(ws: TList).(\lambda (i: nat).(\lambda (_: C).(\lambda (_: T).(eq T t0 
(THeads (Flat Appl) ws (TLRef i))))))) (\lambda (_: TList).(\lambda (i: 
nat).(\lambda (d: C).(\lambda (v: T).(getl i (CHead c0 (Bind b) u) (CHead d 
(Bind Abst) v)))))) (\lambda (ws: TList).(\lambda (_: nat).(\lambda (_: 
C).(\lambda (_: T).(nfs2 (CHead c0 (Bind b) u) ws)))))))))).(\lambda (H5: 
(nf2 c0 (THead (Bind b) u t0))).(B_ind (\lambda (b0: B).((not (eq B b0 Abst)) 
\to ((arity g (CHead c0 (Bind b0) u) t0 a2) \to ((nf2 c0 (THead (Bind b0) u 
t0)) \to (or3 (ex3_2 T T (\lambda (w: T).(\lambda (u0: T).(eq T (THead (Bind 
b0) u t0) (THead (Bind Abst) w u0)))) (\lambda (w: T).(\lambda (_: T).(nf2 c0 
w))) (\lambda (w: T).(\lambda (u0: T).(nf2 (CHead c0 (Bind Abst) w) u0)))) 
(ex nat (\lambda (n: nat).(eq T (THead (Bind b0) u t0) (TSort n)))) (ex3_4 
TList nat C T (\lambda (ws: TList).(\lambda (i: nat).(\lambda (_: C).(\lambda 
(_: T).(eq T (THead (Bind b0) u t0) (THeads (Flat Appl) ws (TLRef i))))))) 
(\lambda (_: TList).(\lambda (i: nat).(\lambda (d: C).(\lambda (v: T).(getl i 
c0 (CHead d (Bind Abst) v)))))) (\lambda (ws: TList).(\lambda (_: 
nat).(\lambda (_: C).(\lambda (_: T).(nfs2 c0 ws))))))))))) (\lambda (_: (not 
(eq B Abbr Abst))).(\lambda (_: (arity g (CHead c0 (Bind Abbr) u) t0 
a2)).(\lambda (H8: (nf2 c0 (THead (Bind Abbr) u t0))).(nf2_gen_abbr c0 u t0 
H8 (or3 (ex3_2 T T (\lambda (w: T).(\lambda (u0: T).(eq T (THead (Bind Abbr) 
u t0) (THead (Bind Abst) w u0)))) (\lambda (w: T).(\lambda (_: T).(nf2 c0 
w))) (\lambda (w: T).(\lambda (u0: T).(nf2 (CHead c0 (Bind Abst) w) u0)))) 
(ex nat (\lambda (n: nat).(eq T (THead (Bind Abbr) u t0) (TSort n)))) (ex3_4 
TList nat C T (\lambda (ws: TList).(\lambda (i: nat).(\lambda (_: C).(\lambda 
(_: T).(eq T (THead (Bind Abbr) u t0) (THeads (Flat Appl) ws (TLRef i))))))) 
(\lambda (_: TList).(\lambda (i: nat).(\lambda (d: C).(\lambda (v: T).(getl i 
c0 (CHead d (Bind Abst) v)))))) (\lambda (ws: TList).(\lambda (_: 
nat).(\lambda (_: C).(\lambda (_: T).(nfs2 c0 ws))))))))))) (\lambda (H6: 
(not (eq B Abst Abst))).(\lambda (_: (arity g (CHead c0 (Bind Abst) u) t0 
a2)).(\lambda (_: (nf2 c0 (THead (Bind Abst) u t0))).(let H9 \def (match (H6 
(refl_equal B Abst)) in False return (\lambda (_: False).(or3 (ex3_2 T T 
(\lambda (w: T).(\lambda (u0: T).(eq T (THead (Bind Abst) u t0) (THead (Bind 
Abst) w u0)))) (\lambda (w: T).(\lambda (_: T).(nf2 c0 w))) (\lambda (w: 
T).(\lambda (u0: T).(nf2 (CHead c0 (Bind Abst) w) u0)))) (ex nat (\lambda (n: 
nat).(eq T (THead (Bind Abst) u t0) (TSort n)))) (ex3_4 TList nat C T 
(\lambda (ws: TList).(\lambda (i: nat).(\lambda (_: C).(\lambda (_: T).(eq T 
(THead (Bind Abst) u t0) (THeads (Flat Appl) ws (TLRef i))))))) (\lambda (_: 
TList).(\lambda (i: nat).(\lambda (d: C).(\lambda (v: T).(getl i c0 (CHead d 
(Bind Abst) v)))))) (\lambda (ws: TList).(\lambda (_: nat).(\lambda (_: 
C).(\lambda (_: T).(nfs2 c0 ws)))))))) with []) in H9)))) (\lambda (_: (not 
(eq B Void Abst))).(\lambda (H7: (arity g (CHead c0 (Bind Void) u) t0 
a2)).(\lambda (H8: (nf2 c0 (THead (Bind Void) u t0))).(let H9 \def 
(arity_gen_cvoid g (CHead c0 (Bind Void) u) t0 a2 H7 c0 u O (getl_refl Void 
c0 u)) in (ex_ind T (\lambda (v: T).(eq T t0 (lift (S O) O v))) (or3 (ex3_2 T 
T (\lambda (w: T).(\lambda (u0: T).(eq T (THead (Bind Void) u t0) (THead 
(Bind Abst) w u0)))) (\lambda (w: T).(\lambda (_: T).(nf2 c0 w))) (\lambda 
(w: T).(\lambda (u0: T).(nf2 (CHead c0 (Bind Abst) w) u0)))) (ex nat (\lambda 
(n: nat).(eq T (THead (Bind Void) u t0) (TSort n)))) (ex3_4 TList nat C T 
(\lambda (ws: TList).(\lambda (i: nat).(\lambda (_: C).(\lambda (_: T).(eq T 
(THead (Bind Void) u t0) (THeads (Flat Appl) ws (TLRef i))))))) (\lambda (_: 
TList).(\lambda (i: nat).(\lambda (d: C).(\lambda (v: T).(getl i c0 (CHead d 
(Bind Abst) v)))))) (\lambda (ws: TList).(\lambda (_: nat).(\lambda (_: 
C).(\lambda (_: T).(nfs2 c0 ws))))))) (\lambda (x: T).(\lambda (H10: (eq T t0 
(lift (S O) O x))).(let H11 \def (eq_ind T t0 (\lambda (t1: T).(nf2 c0 (THead 
(Bind Void) u t1))) H8 (lift (S O) O x) H10) in (eq_ind_r T (lift (S O) O x) 
(\lambda (t1: T).(or3 (ex3_2 T T (\lambda (w: T).(\lambda (u0: T).(eq T 
(THead (Bind Void) u t1) (THead (Bind Abst) w u0)))) (\lambda (w: T).(\lambda 
(_: T).(nf2 c0 w))) (\lambda (w: T).(\lambda (u0: T).(nf2 (CHead c0 (Bind 
Abst) w) u0)))) (ex nat (\lambda (n: nat).(eq T (THead (Bind Void) u t1) 
(TSort n)))) (ex3_4 TList nat C T (\lambda (ws: TList).(\lambda (i: 
nat).(\lambda (_: C).(\lambda (_: T).(eq T (THead (Bind Void) u t1) (THeads 
(Flat Appl) ws (TLRef i))))))) (\lambda (_: TList).(\lambda (i: nat).(\lambda 
(d: C).(\lambda (v: T).(getl i c0 (CHead d (Bind Abst) v)))))) (\lambda (ws: 
TList).(\lambda (_: nat).(\lambda (_: C).(\lambda (_: T).(nfs2 c0 ws)))))))) 
(nf2_gen_void c0 u x H11 (or3 (ex3_2 T T (\lambda (w: T).(\lambda (u0: T).(eq 
T (THead (Bind Void) u (lift (S O) O x)) (THead (Bind Abst) w u0)))) (\lambda 
(w: T).(\lambda (_: T).(nf2 c0 w))) (\lambda (w: T).(\lambda (u0: T).(nf2 
(CHead c0 (Bind Abst) w) u0)))) (ex nat (\lambda (n: nat).(eq T (THead (Bind 
Void) u (lift (S O) O x)) (TSort n)))) (ex3_4 TList nat C T (\lambda (ws: 
TList).(\lambda (i: nat).(\lambda (_: C).(\lambda (_: T).(eq T (THead (Bind 
Void) u (lift (S O) O x)) (THeads (Flat Appl) ws (TLRef i))))))) (\lambda (_: 
TList).(\lambda (i: nat).(\lambda (d: C).(\lambda (v: T).(getl i c0 (CHead d 
(Bind Abst) v)))))) (\lambda (ws: TList).(\lambda (_: nat).(\lambda (_: 
C).(\lambda (_: T).(nfs2 c0 ws)))))))) t0 H10)))) H9))))) b H0 H3 
H5))))))))))))) (\lambda (c0: C).(\lambda (u: T).(\lambda (a1: A).(\lambda 
(_: (arity g c0 u (asucc g a1))).(\lambda (_: (((nf2 c0 u) \to (or3 (ex3_2 T 
T (\lambda (w: T).(\lambda (u0: T).(eq T u (THead (Bind Abst) w u0)))) 
(\lambda (w: T).(\lambda (_: T).(nf2 c0 w))) (\lambda (w: T).(\lambda (u0: 
T).(nf2 (CHead c0 (Bind Abst) w) u0)))) (ex nat (\lambda (n: nat).(eq T u 
(TSort n)))) (ex3_4 TList nat C T (\lambda (ws: TList).(\lambda (i: 
nat).(\lambda (_: C).(\lambda (_: T).(eq T u (THeads (Flat Appl) ws (TLRef 
i))))))) (\lambda (_: TList).(\lambda (i: nat).(\lambda (d: C).(\lambda (v: 
T).(getl i c0 (CHead d (Bind Abst) v)))))) (\lambda (ws: TList).(\lambda (_: 
nat).(\lambda (_: C).(\lambda (_: T).(nfs2 c0 ws)))))))))).(\lambda (t0: 
T).(\lambda (a2: A).(\lambda (_: (arity g (CHead c0 (Bind Abst) u) t0 
a2)).(\lambda (_: (((nf2 (CHead c0 (Bind Abst) u) t0) \to (or3 (ex3_2 T T 
(\lambda (w: T).(\lambda (u0: T).(eq T t0 (THead (Bind Abst) w u0)))) 
(\lambda (w: T).(\lambda (_: T).(nf2 (CHead c0 (Bind Abst) u) w))) (\lambda 
(w: T).(\lambda (u0: T).(nf2 (CHead (CHead c0 (Bind Abst) u) (Bind Abst) w) 
u0)))) (ex nat (\lambda (n: nat).(eq T t0 (TSort n)))) (ex3_4 TList nat C T 
(\lambda (ws: TList).(\lambda (i: nat).(\lambda (_: C).(\lambda (_: T).(eq T 
t0 (THeads (Flat Appl) ws (TLRef i))))))) (\lambda (_: TList).(\lambda (i: 
nat).(\lambda (d: C).(\lambda (v: T).(getl i (CHead c0 (Bind Abst) u) (CHead 
d (Bind Abst) v)))))) (\lambda (ws: TList).(\lambda (_: nat).(\lambda (_: 
C).(\lambda (_: T).(nfs2 (CHead c0 (Bind Abst) u) ws)))))))))).(\lambda (H4: 
(nf2 c0 (THead (Bind Abst) u t0))).(let H5 \def (nf2_gen_abst c0 u t0 H4) in 
(and_ind (nf2 c0 u) (nf2 (CHead c0 (Bind Abst) u) t0) (or3 (ex3_2 T T 
(\lambda (w: T).(\lambda (u0: T).(eq T (THead (Bind Abst) u t0) (THead (Bind 
Abst) w u0)))) (\lambda (w: T).(\lambda (_: T).(nf2 c0 w))) (\lambda (w: 
T).(\lambda (u0: T).(nf2 (CHead c0 (Bind Abst) w) u0)))) (ex nat (\lambda (n: 
nat).(eq T (THead (Bind Abst) u t0) (TSort n)))) (ex3_4 TList nat C T 
(\lambda (ws: TList).(\lambda (i: nat).(\lambda (_: C).(\lambda (_: T).(eq T 
(THead (Bind Abst) u t0) (THeads (Flat Appl) ws (TLRef i))))))) (\lambda (_: 
TList).(\lambda (i: nat).(\lambda (d: C).(\lambda (v: T).(getl i c0 (CHead d 
(Bind Abst) v)))))) (\lambda (ws: TList).(\lambda (_: nat).(\lambda (_: 
C).(\lambda (_: T).(nfs2 c0 ws))))))) (\lambda (H6: (nf2 c0 u)).(\lambda (H7: 
(nf2 (CHead c0 (Bind Abst) u) t0)).(or3_intro0 (ex3_2 T T (\lambda (w: 
T).(\lambda (u0: T).(eq T (THead (Bind Abst) u t0) (THead (Bind Abst) w 
u0)))) (\lambda (w: T).(\lambda (_: T).(nf2 c0 w))) (\lambda (w: T).(\lambda 
(u0: T).(nf2 (CHead c0 (Bind Abst) w) u0)))) (ex nat (\lambda (n: nat).(eq T 
(THead (Bind Abst) u t0) (TSort n)))) (ex3_4 TList nat C T (\lambda (ws: 
TList).(\lambda (i: nat).(\lambda (_: C).(\lambda (_: T).(eq T (THead (Bind 
Abst) u t0) (THeads (Flat Appl) ws (TLRef i))))))) (\lambda (_: 
TList).(\lambda (i: nat).(\lambda (d: C).(\lambda (v: T).(getl i c0 (CHead d 
(Bind Abst) v)))))) (\lambda (ws: TList).(\lambda (_: nat).(\lambda (_: 
C).(\lambda (_: T).(nfs2 c0 ws)))))) (ex3_2_intro T T (\lambda (w: 
T).(\lambda (u0: T).(eq T (THead (Bind Abst) u t0) (THead (Bind Abst) w 
u0)))) (\lambda (w: T).(\lambda (_: T).(nf2 c0 w))) (\lambda (w: T).(\lambda 
(u0: T).(nf2 (CHead c0 (Bind Abst) w) u0))) u t0 (refl_equal T (THead (Bind 
Abst) u t0)) H6 H7)))) H5)))))))))))) (\lambda (c0: C).(\lambda (u: 
T).(\lambda (a1: A).(\lambda (_: (arity g c0 u a1)).(\lambda (_: (((nf2 c0 u) 
\to (or3 (ex3_2 T T (\lambda (w: T).(\lambda (u0: T).(eq T u (THead (Bind 
Abst) w u0)))) (\lambda (w: T).(\lambda (_: T).(nf2 c0 w))) (\lambda (w: 
T).(\lambda (u0: T).(nf2 (CHead c0 (Bind Abst) w) u0)))) (ex nat (\lambda (n: 
nat).(eq T u (TSort n)))) (ex3_4 TList nat C T (\lambda (ws: TList).(\lambda 
(i: nat).(\lambda (_: C).(\lambda (_: T).(eq T u (THeads (Flat Appl) ws 
(TLRef i))))))) (\lambda (_: TList).(\lambda (i: nat).(\lambda (d: 
C).(\lambda (v: T).(getl i c0 (CHead d (Bind Abst) v)))))) (\lambda (ws: 
TList).(\lambda (_: nat).(\lambda (_: C).(\lambda (_: T).(nfs2 c0 
ws)))))))))).(\lambda (t0: T).(\lambda (a2: A).(\lambda (H2: (arity g c0 t0 
(AHead a1 a2))).(\lambda (H3: (((nf2 c0 t0) \to (or3 (ex3_2 T T (\lambda (w: 
T).(\lambda (u0: T).(eq T t0 (THead (Bind Abst) w u0)))) (\lambda (w: 
T).(\lambda (_: T).(nf2 c0 w))) (\lambda (w: T).(\lambda (u0: T).(nf2 (CHead 
c0 (Bind Abst) w) u0)))) (ex nat (\lambda (n: nat).(eq T t0 (TSort n)))) 
(ex3_4 TList nat C T (\lambda (ws: TList).(\lambda (i: nat).(\lambda (_: 
C).(\lambda (_: T).(eq T t0 (THeads (Flat Appl) ws (TLRef i))))))) (\lambda 
(_: TList).(\lambda (i: nat).(\lambda (d: C).(\lambda (v: T).(getl i c0 
(CHead d (Bind Abst) v)))))) (\lambda (ws: TList).(\lambda (_: nat).(\lambda 
(_: C).(\lambda (_: T).(nfs2 c0 ws)))))))))).(\lambda (H4: (nf2 c0 (THead 
(Flat Appl) u t0))).(let H5 \def (nf2_gen_flat Appl c0 u t0 H4) in (and_ind 
(nf2 c0 u) (nf2 c0 t0) (or3 (ex3_2 T T (\lambda (w: T).(\lambda (u0: T).(eq T 
(THead (Flat Appl) u t0) (THead (Bind Abst) w u0)))) (\lambda (w: T).(\lambda 
(_: T).(nf2 c0 w))) (\lambda (w: T).(\lambda (u0: T).(nf2 (CHead c0 (Bind 
Abst) w) u0)))) (ex nat (\lambda (n: nat).(eq T (THead (Flat Appl) u t0) 
(TSort n)))) (ex3_4 TList nat C T (\lambda (ws: TList).(\lambda (i: 
nat).(\lambda (_: C).(\lambda (_: T).(eq T (THead (Flat Appl) u t0) (THeads 
(Flat Appl) ws (TLRef i))))))) (\lambda (_: TList).(\lambda (i: nat).(\lambda 
(d: C).(\lambda (v: T).(getl i c0 (CHead d (Bind Abst) v)))))) (\lambda (ws: 
TList).(\lambda (_: nat).(\lambda (_: C).(\lambda (_: T).(nfs2 c0 ws))))))) 
(\lambda (H6: (nf2 c0 u)).(\lambda (H7: (nf2 c0 t0)).(let H_x \def (H3 H7) in 
(let H8 \def H_x in (or3_ind (ex3_2 T T (\lambda (w: T).(\lambda (u0: T).(eq 
T t0 (THead (Bind Abst) w u0)))) (\lambda (w: T).(\lambda (_: T).(nf2 c0 w))) 
(\lambda (w: T).(\lambda (u0: T).(nf2 (CHead c0 (Bind Abst) w) u0)))) (ex nat 
(\lambda (n: nat).(eq T t0 (TSort n)))) (ex3_4 TList nat C T (\lambda (ws: 
TList).(\lambda (i: nat).(\lambda (_: C).(\lambda (_: T).(eq T t0 (THeads 
(Flat Appl) ws (TLRef i))))))) (\lambda (_: TList).(\lambda (i: nat).(\lambda 
(d: C).(\lambda (v: T).(getl i c0 (CHead d (Bind Abst) v)))))) (\lambda (ws: 
TList).(\lambda (_: nat).(\lambda (_: C).(\lambda (_: T).(nfs2 c0 ws)))))) 
(or3 (ex3_2 T T (\lambda (w: T).(\lambda (u0: T).(eq T (THead (Flat Appl) u 
t0) (THead (Bind Abst) w u0)))) (\lambda (w: T).(\lambda (_: T).(nf2 c0 w))) 
(\lambda (w: T).(\lambda (u0: T).(nf2 (CHead c0 (Bind Abst) w) u0)))) (ex nat 
(\lambda (n: nat).(eq T (THead (Flat Appl) u t0) (TSort n)))) (ex3_4 TList 
nat C T (\lambda (ws: TList).(\lambda (i: nat).(\lambda (_: C).(\lambda (_: 
T).(eq T (THead (Flat Appl) u t0) (THeads (Flat Appl) ws (TLRef i))))))) 
(\lambda (_: TList).(\lambda (i: nat).(\lambda (d: C).(\lambda (v: T).(getl i 
c0 (CHead d (Bind Abst) v)))))) (\lambda (ws: TList).(\lambda (_: 
nat).(\lambda (_: C).(\lambda (_: T).(nfs2 c0 ws))))))) (\lambda (H9: (ex3_2 
T T (\lambda (w: T).(\lambda (u0: T).(eq T t0 (THead (Bind Abst) w u0)))) 
(\lambda (w: T).(\lambda (_: T).(nf2 c0 w))) (\lambda (w: T).(\lambda (u0: 
T).(nf2 (CHead c0 (Bind Abst) w) u0))))).(ex3_2_ind T T (\lambda (w: 
T).(\lambda (u0: T).(eq T t0 (THead (Bind Abst) w u0)))) (\lambda (w: 
T).(\lambda (_: T).(nf2 c0 w))) (\lambda (w: T).(\lambda (u0: T).(nf2 (CHead 
c0 (Bind Abst) w) u0))) (or3 (ex3_2 T T (\lambda (w: T).(\lambda (u0: T).(eq 
T (THead (Flat Appl) u t0) (THead (Bind Abst) w u0)))) (\lambda (w: 
T).(\lambda (_: T).(nf2 c0 w))) (\lambda (w: T).(\lambda (u0: T).(nf2 (CHead 
c0 (Bind Abst) w) u0)))) (ex nat (\lambda (n: nat).(eq T (THead (Flat Appl) u 
t0) (TSort n)))) (ex3_4 TList nat C T (\lambda (ws: TList).(\lambda (i: 
nat).(\lambda (_: C).(\lambda (_: T).(eq T (THead (Flat Appl) u t0) (THeads 
(Flat Appl) ws (TLRef i))))))) (\lambda (_: TList).(\lambda (i: nat).(\lambda 
(d: C).(\lambda (v: T).(getl i c0 (CHead d (Bind Abst) v)))))) (\lambda (ws: 
TList).(\lambda (_: nat).(\lambda (_: C).(\lambda (_: T).(nfs2 c0 ws))))))) 
(\lambda (x0: T).(\lambda (x1: T).(\lambda (H10: (eq T t0 (THead (Bind Abst) 
x0 x1))).(\lambda (_: (nf2 c0 x0)).(\lambda (_: (nf2 (CHead c0 (Bind Abst) 
x0) x1)).(let H13 \def (eq_ind T t0 (\lambda (t1: T).(nf2 c0 (THead (Flat 
Appl) u t1))) H4 (THead (Bind Abst) x0 x1) H10) in (let H14 \def (eq_ind T t0 
(\lambda (t1: T).(arity g c0 t1 (AHead a1 a2))) H2 (THead (Bind Abst) x0 x1) 
H10) in (eq_ind_r T (THead (Bind Abst) x0 x1) (\lambda (t1: T).(or3 (ex3_2 T 
T (\lambda (w: T).(\lambda (u0: T).(eq T (THead (Flat Appl) u t1) (THead 
(Bind Abst) w u0)))) (\lambda (w: T).(\lambda (_: T).(nf2 c0 w))) (\lambda 
(w: T).(\lambda (u0: T).(nf2 (CHead c0 (Bind Abst) w) u0)))) (ex nat (\lambda 
(n: nat).(eq T (THead (Flat Appl) u t1) (TSort n)))) (ex3_4 TList nat C T 
(\lambda (ws: TList).(\lambda (i: nat).(\lambda (_: C).(\lambda (_: T).(eq T 
(THead (Flat Appl) u t1) (THeads (Flat Appl) ws (TLRef i))))))) (\lambda (_: 
TList).(\lambda (i: nat).(\lambda (d: C).(\lambda (v: T).(getl i c0 (CHead d 
(Bind Abst) v)))))) (\lambda (ws: TList).(\lambda (_: nat).(\lambda (_: 
C).(\lambda (_: T).(nfs2 c0 ws)))))))) (nf2_gen_beta c0 u x0 x1 H13 (or3 
(ex3_2 T T (\lambda (w: T).(\lambda (u0: T).(eq T (THead (Flat Appl) u (THead 
(Bind Abst) x0 x1)) (THead (Bind Abst) w u0)))) (\lambda (w: T).(\lambda (_: 
T).(nf2 c0 w))) (\lambda (w: T).(\lambda (u0: T).(nf2 (CHead c0 (Bind Abst) 
w) u0)))) (ex nat (\lambda (n: nat).(eq T (THead (Flat Appl) u (THead (Bind 
Abst) x0 x1)) (TSort n)))) (ex3_4 TList nat C T (\lambda (ws: TList).(\lambda 
(i: nat).(\lambda (_: C).(\lambda (_: T).(eq T (THead (Flat Appl) u (THead 
(Bind Abst) x0 x1)) (THeads (Flat Appl) ws (TLRef i))))))) (\lambda (_: 
TList).(\lambda (i: nat).(\lambda (d: C).(\lambda (v: T).(getl i c0 (CHead d 
(Bind Abst) v)))))) (\lambda (ws: TList).(\lambda (_: nat).(\lambda (_: 
C).(\lambda (_: T).(nfs2 c0 ws)))))))) t0 H10)))))))) H9)) (\lambda (H9: (ex 
nat (\lambda (n: nat).(eq T t0 (TSort n))))).(ex_ind nat (\lambda (n: 
nat).(eq T t0 (TSort n))) (or3 (ex3_2 T T (\lambda (w: T).(\lambda (u0: 
T).(eq T (THead (Flat Appl) u t0) (THead (Bind Abst) w u0)))) (\lambda (w: 
T).(\lambda (_: T).(nf2 c0 w))) (\lambda (w: T).(\lambda (u0: T).(nf2 (CHead 
c0 (Bind Abst) w) u0)))) (ex nat (\lambda (n: nat).(eq T (THead (Flat Appl) u 
t0) (TSort n)))) (ex3_4 TList nat C T (\lambda (ws: TList).(\lambda (i: 
nat).(\lambda (_: C).(\lambda (_: T).(eq T (THead (Flat Appl) u t0) (THeads 
(Flat Appl) ws (TLRef i))))))) (\lambda (_: TList).(\lambda (i: nat).(\lambda 
(d: C).(\lambda (v: T).(getl i c0 (CHead d (Bind Abst) v)))))) (\lambda (ws: 
TList).(\lambda (_: nat).(\lambda (_: C).(\lambda (_: T).(nfs2 c0 ws))))))) 
(\lambda (x: nat).(\lambda (H10: (eq T t0 (TSort x))).(let H11 \def (eq_ind T 
t0 (\lambda (t1: T).(nf2 c0 (THead (Flat Appl) u t1))) H4 (TSort x) H10) in 
(let H12 \def (eq_ind T t0 (\lambda (t1: T).(arity g c0 t1 (AHead a1 a2))) H2 
(TSort x) H10) in (eq_ind_r T (TSort x) (\lambda (t1: T).(or3 (ex3_2 T T 
(\lambda (w: T).(\lambda (u0: T).(eq T (THead (Flat Appl) u t1) (THead (Bind 
Abst) w u0)))) (\lambda (w: T).(\lambda (_: T).(nf2 c0 w))) (\lambda (w: 
T).(\lambda (u0: T).(nf2 (CHead c0 (Bind Abst) w) u0)))) (ex nat (\lambda (n: 
nat).(eq T (THead (Flat Appl) u t1) (TSort n)))) (ex3_4 TList nat C T 
(\lambda (ws: TList).(\lambda (i: nat).(\lambda (_: C).(\lambda (_: T).(eq T 
(THead (Flat Appl) u t1) (THeads (Flat Appl) ws (TLRef i))))))) (\lambda (_: 
TList).(\lambda (i: nat).(\lambda (d: C).(\lambda (v: T).(getl i c0 (CHead d 
(Bind Abst) v)))))) (\lambda (ws: TList).(\lambda (_: nat).(\lambda (_: 
C).(\lambda (_: T).(nfs2 c0 ws)))))))) (let H13 \def (match (arity_gen_sort g 
c0 x (AHead a1 a2) H12) in leq return (\lambda (a0: A).(\lambda (a3: 
A).(\lambda (_: (leq ? a0 a3)).((eq A a0 (AHead a1 a2)) \to ((eq A a3 (ASort 
O x)) \to (or3 (ex3_2 T T (\lambda (w: T).(\lambda (u0: T).(eq T (THead (Flat 
Appl) u (TSort x)) (THead (Bind Abst) w u0)))) (\lambda (w: T).(\lambda (_: 
T).(nf2 c0 w))) (\lambda (w: T).(\lambda (u0: T).(nf2 (CHead c0 (Bind Abst) 
w) u0)))) (ex nat (\lambda (n: nat).(eq T (THead (Flat Appl) u (TSort x)) 
(TSort n)))) (ex3_4 TList nat C T (\lambda (ws: TList).(\lambda (i: 
nat).(\lambda (_: C).(\lambda (_: T).(eq T (THead (Flat Appl) u (TSort x)) 
(THeads (Flat Appl) ws (TLRef i))))))) (\lambda (_: TList).(\lambda (i: 
nat).(\lambda (d: C).(\lambda (v: T).(getl i c0 (CHead d (Bind Abst) v)))))) 
(\lambda (ws: TList).(\lambda (_: nat).(\lambda (_: C).(\lambda (_: T).(nfs2 
c0 ws)))))))))))) with [(leq_sort h1 h2 n1 n2 k H13) \Rightarrow (\lambda 
(H14: (eq A (ASort h1 n1) (AHead a1 a2))).(\lambda (H15: (eq A (ASort h2 n2) 
(ASort O x))).((let H16 \def (eq_ind A (ASort h1 n1) (\lambda (e: A).(match e 
in A return (\lambda (_: A).Prop) with [(ASort _ _) \Rightarrow True | (AHead 
_ _) \Rightarrow False])) I (AHead a1 a2) H14) in (False_ind ((eq A (ASort h2 
n2) (ASort O x)) \to ((eq A (aplus g (ASort h1 n1) k) (aplus g (ASort h2 n2) 
k)) \to (or3 (ex3_2 T T (\lambda (w: T).(\lambda (u0: T).(eq T (THead (Flat 
Appl) u (TSort x)) (THead (Bind Abst) w u0)))) (\lambda (w: T).(\lambda (_: 
T).(nf2 c0 w))) (\lambda (w: T).(\lambda (u0: T).(nf2 (CHead c0 (Bind Abst) 
w) u0)))) (ex nat (\lambda (n: nat).(eq T (THead (Flat Appl) u (TSort x)) 
(TSort n)))) (ex3_4 TList nat C T (\lambda (ws: TList).(\lambda (i: 
nat).(\lambda (_: C).(\lambda (_: T).(eq T (THead (Flat Appl) u (TSort x)) 
(THeads (Flat Appl) ws (TLRef i))))))) (\lambda (_: TList).(\lambda (i: 
nat).(\lambda (d: C).(\lambda (v: T).(getl i c0 (CHead d (Bind Abst) v)))))) 
(\lambda (ws: TList).(\lambda (_: nat).(\lambda (_: C).(\lambda (_: T).(nfs2 
c0 ws))))))))) H16)) H15 H13))) | (leq_head a0 a3 H13 a4 a5 H14) \Rightarrow 
(\lambda (H15: (eq A (AHead a0 a4) (AHead a1 a2))).(\lambda (H16: (eq A 
(AHead a3 a5) (ASort O x))).((let H17 \def (f_equal A A (\lambda (e: 
A).(match e in A return (\lambda (_: A).A) with [(ASort _ _) \Rightarrow a4 | 
(AHead _ a6) \Rightarrow a6])) (AHead a0 a4) (AHead a1 a2) H15) in ((let H18 
\def (f_equal A A (\lambda (e: A).(match e in A return (\lambda (_: A).A) 
with [(ASort _ _) \Rightarrow a0 | (AHead a6 _) \Rightarrow a6])) (AHead a0 
a4) (AHead a1 a2) H15) in (eq_ind A a1 (\lambda (a6: A).((eq A a4 a2) \to 
((eq A (AHead a3 a5) (ASort O x)) \to ((leq g a6 a3) \to ((leq g a4 a5) \to 
(or3 (ex3_2 T T (\lambda (w: T).(\lambda (u0: T).(eq T (THead (Flat Appl) u 
(TSort x)) (THead (Bind Abst) w u0)))) (\lambda (w: T).(\lambda (_: T).(nf2 
c0 w))) (\lambda (w: T).(\lambda (u0: T).(nf2 (CHead c0 (Bind Abst) w) u0)))) 
(ex nat (\lambda (n: nat).(eq T (THead (Flat Appl) u (TSort x)) (TSort n)))) 
(ex3_4 TList nat C T (\lambda (ws: TList).(\lambda (i: nat).(\lambda (_: 
C).(\lambda (_: T).(eq T (THead (Flat Appl) u (TSort x)) (THeads (Flat Appl) 
ws (TLRef i))))))) (\lambda (_: TList).(\lambda (i: nat).(\lambda (d: 
C).(\lambda (v: T).(getl i c0 (CHead d (Bind Abst) v)))))) (\lambda (ws: 
TList).(\lambda (_: nat).(\lambda (_: C).(\lambda (_: T).(nfs2 c0 
ws)))))))))))) (\lambda (H19: (eq A a4 a2)).(eq_ind A a2 (\lambda (a6: 
A).((eq A (AHead a3 a5) (ASort O x)) \to ((leq g a1 a3) \to ((leq g a6 a5) 
\to (or3 (ex3_2 T T (\lambda (w: T).(\lambda (u0: T).(eq T (THead (Flat Appl) 
u (TSort x)) (THead (Bind Abst) w u0)))) (\lambda (w: T).(\lambda (_: T).(nf2 
c0 w))) (\lambda (w: T).(\lambda (u0: T).(nf2 (CHead c0 (Bind Abst) w) u0)))) 
(ex nat (\lambda (n: nat).(eq T (THead (Flat Appl) u (TSort x)) (TSort n)))) 
(ex3_4 TList nat C T (\lambda (ws: TList).(\lambda (i: nat).(\lambda (_: 
C).(\lambda (_: T).(eq T (THead (Flat Appl) u (TSort x)) (THeads (Flat Appl) 
ws (TLRef i))))))) (\lambda (_: TList).(\lambda (i: nat).(\lambda (d: 
C).(\lambda (v: T).(getl i c0 (CHead d (Bind Abst) v)))))) (\lambda (ws: 
TList).(\lambda (_: nat).(\lambda (_: C).(\lambda (_: T).(nfs2 c0 
ws))))))))))) (\lambda (H20: (eq A (AHead a3 a5) (ASort O x))).(let H21 \def 
(eq_ind A (AHead a3 a5) (\lambda (e: A).(match e in A return (\lambda (_: 
A).Prop) with [(ASort _ _) \Rightarrow False | (AHead _ _) \Rightarrow 
True])) I (ASort O x) H20) in (False_ind ((leq g a1 a3) \to ((leq g a2 a5) 
\to (or3 (ex3_2 T T (\lambda (w: T).(\lambda (u0: T).(eq T (THead (Flat Appl) 
u (TSort x)) (THead (Bind Abst) w u0)))) (\lambda (w: T).(\lambda (_: T).(nf2 
c0 w))) (\lambda (w: T).(\lambda (u0: T).(nf2 (CHead c0 (Bind Abst) w) u0)))) 
(ex nat (\lambda (n: nat).(eq T (THead (Flat Appl) u (TSort x)) (TSort n)))) 
(ex3_4 TList nat C T (\lambda (ws: TList).(\lambda (i: nat).(\lambda (_: 
C).(\lambda (_: T).(eq T (THead (Flat Appl) u (TSort x)) (THeads (Flat Appl) 
ws (TLRef i))))))) (\lambda (_: TList).(\lambda (i: nat).(\lambda (d: 
C).(\lambda (v: T).(getl i c0 (CHead d (Bind Abst) v)))))) (\lambda (ws: 
TList).(\lambda (_: nat).(\lambda (_: C).(\lambda (_: T).(nfs2 c0 ws))))))))) 
H21))) a4 (sym_eq A a4 a2 H19))) a0 (sym_eq A a0 a1 H18))) H17)) H16 H13 
H14)))]) in (H13 (refl_equal A (AHead a1 a2)) (refl_equal A (ASort O x)))) t0 
H10))))) H9)) (\lambda (H9: (ex3_4 TList nat C T (\lambda (ws: 
TList).(\lambda (i: nat).(\lambda (_: C).(\lambda (_: T).(eq T t0 (THeads 
(Flat Appl) ws (TLRef i))))))) (\lambda (_: TList).(\lambda (i: nat).(\lambda 
(d: C).(\lambda (v: T).(getl i c0 (CHead d (Bind Abst) v)))))) (\lambda (ws: 
TList).(\lambda (_: nat).(\lambda (_: C).(\lambda (_: T).(nfs2 c0 
ws))))))).(ex3_4_ind TList nat C T (\lambda (ws: TList).(\lambda (i: 
nat).(\lambda (_: C).(\lambda (_: T).(eq T t0 (THeads (Flat Appl) ws (TLRef 
i))))))) (\lambda (_: TList).(\lambda (i: nat).(\lambda (d: C).(\lambda (v: 
T).(getl i c0 (CHead d (Bind Abst) v)))))) (\lambda (ws: TList).(\lambda (_: 
nat).(\lambda (_: C).(\lambda (_: T).(nfs2 c0 ws))))) (or3 (ex3_2 T T 
(\lambda (w: T).(\lambda (u0: T).(eq T (THead (Flat Appl) u t0) (THead (Bind 
Abst) w u0)))) (\lambda (w: T).(\lambda (_: T).(nf2 c0 w))) (\lambda (w: 
T).(\lambda (u0: T).(nf2 (CHead c0 (Bind Abst) w) u0)))) (ex nat (\lambda (n: 
nat).(eq T (THead (Flat Appl) u t0) (TSort n)))) (ex3_4 TList nat C T 
(\lambda (ws: TList).(\lambda (i: nat).(\lambda (_: C).(\lambda (_: T).(eq T 
(THead (Flat Appl) u t0) (THeads (Flat Appl) ws (TLRef i))))))) (\lambda (_: 
TList).(\lambda (i: nat).(\lambda (d: C).(\lambda (v: T).(getl i c0 (CHead d 
(Bind Abst) v)))))) (\lambda (ws: TList).(\lambda (_: nat).(\lambda (_: 
C).(\lambda (_: T).(nfs2 c0 ws))))))) (\lambda (x0: TList).(\lambda (x1: 
nat).(\lambda (x2: C).(\lambda (x3: T).(\lambda (H10: (eq T t0 (THeads (Flat 
Appl) x0 (TLRef x1)))).(\lambda (H11: (getl x1 c0 (CHead x2 (Bind Abst) 
x3))).(\lambda (H12: (nfs2 c0 x0)).(let H13 \def (eq_ind T t0 (\lambda (t1: 
T).(nf2 c0 (THead (Flat Appl) u t1))) H4 (THeads (Flat Appl) x0 (TLRef x1)) 
H10) in (let H14 \def (eq_ind T t0 (\lambda (t1: T).(arity g c0 t1 (AHead a1 
a2))) H2 (THeads (Flat Appl) x0 (TLRef x1)) H10) in (eq_ind_r T (THeads (Flat 
Appl) x0 (TLRef x1)) (\lambda (t1: T).(or3 (ex3_2 T T (\lambda (w: 
T).(\lambda (u0: T).(eq T (THead (Flat Appl) u t1) (THead (Bind Abst) w 
u0)))) (\lambda (w: T).(\lambda (_: T).(nf2 c0 w))) (\lambda (w: T).(\lambda 
(u0: T).(nf2 (CHead c0 (Bind Abst) w) u0)))) (ex nat (\lambda (n: nat).(eq T 
(THead (Flat Appl) u t1) (TSort n)))) (ex3_4 TList nat C T (\lambda (ws: 
TList).(\lambda (i: nat).(\lambda (_: C).(\lambda (_: T).(eq T (THead (Flat 
Appl) u t1) (THeads (Flat Appl) ws (TLRef i))))))) (\lambda (_: 
TList).(\lambda (i: nat).(\lambda (d: C).(\lambda (v: T).(getl i c0 (CHead d 
(Bind Abst) v)))))) (\lambda (ws: TList).(\lambda (_: nat).(\lambda (_: 
C).(\lambda (_: T).(nfs2 c0 ws)))))))) (or3_intro2 (ex3_2 T T (\lambda (w: 
T).(\lambda (u0: T).(eq T (THead (Flat Appl) u (THeads (Flat Appl) x0 (TLRef 
x1))) (THead (Bind Abst) w u0)))) (\lambda (w: T).(\lambda (_: T).(nf2 c0 
w))) (\lambda (w: T).(\lambda (u0: T).(nf2 (CHead c0 (Bind Abst) w) u0)))) 
(ex nat (\lambda (n: nat).(eq T (THead (Flat Appl) u (THeads (Flat Appl) x0 
(TLRef x1))) (TSort n)))) (ex3_4 TList nat C T (\lambda (ws: TList).(\lambda 
(i: nat).(\lambda (_: C).(\lambda (_: T).(eq T (THead (Flat Appl) u (THeads 
(Flat Appl) x0 (TLRef x1))) (THeads (Flat Appl) ws (TLRef i))))))) (\lambda 
(_: TList).(\lambda (i: nat).(\lambda (d: C).(\lambda (v: T).(getl i c0 
(CHead d (Bind Abst) v)))))) (\lambda (ws: TList).(\lambda (_: nat).(\lambda 
(_: C).(\lambda (_: T).(nfs2 c0 ws)))))) (ex3_4_intro TList nat C T (\lambda 
(ws: TList).(\lambda (i: nat).(\lambda (_: C).(\lambda (_: T).(eq T (THead 
(Flat Appl) u (THeads (Flat Appl) x0 (TLRef x1))) (THeads (Flat Appl) ws 
(TLRef i))))))) (\lambda (_: TList).(\lambda (i: nat).(\lambda (d: 
C).(\lambda (v: T).(getl i c0 (CHead d (Bind Abst) v)))))) (\lambda (ws: 
TList).(\lambda (_: nat).(\lambda (_: C).(\lambda (_: T).(nfs2 c0 ws))))) 
(TCons u x0) x1 x2 x3 (refl_equal T (THead (Flat Appl) u (THeads (Flat Appl) 
x0 (TLRef x1)))) H11 (conj (nf2 c0 u) (nfs2 c0 x0) H6 H12))) t0 H10)))))))))) 
H9)) H8))))) H5)))))))))))) (\lambda (c0: C).(\lambda (u: T).(\lambda (a0: 
A).(\lambda (_: (arity g c0 u (asucc g a0))).(\lambda (_: (((nf2 c0 u) \to 
(or3 (ex3_2 T T (\lambda (w: T).(\lambda (u0: T).(eq T u (THead (Bind Abst) w 
u0)))) (\lambda (w: T).(\lambda (_: T).(nf2 c0 w))) (\lambda (w: T).(\lambda 
(u0: T).(nf2 (CHead c0 (Bind Abst) w) u0)))) (ex nat (\lambda (n: nat).(eq T 
u (TSort n)))) (ex3_4 TList nat C T (\lambda (ws: TList).(\lambda (i: 
nat).(\lambda (_: C).(\lambda (_: T).(eq T u (THeads (Flat Appl) ws (TLRef 
i))))))) (\lambda (_: TList).(\lambda (i: nat).(\lambda (d: C).(\lambda (v: 
T).(getl i c0 (CHead d (Bind Abst) v)))))) (\lambda (ws: TList).(\lambda (_: 
nat).(\lambda (_: C).(\lambda (_: T).(nfs2 c0 ws)))))))))).(\lambda (t0: 
T).(\lambda (_: (arity g c0 t0 a0)).(\lambda (_: (((nf2 c0 t0) \to (or3 
(ex3_2 T T (\lambda (w: T).(\lambda (u0: T).(eq T t0 (THead (Bind Abst) w 
u0)))) (\lambda (w: T).(\lambda (_: T).(nf2 c0 w))) (\lambda (w: T).(\lambda 
(u0: T).(nf2 (CHead c0 (Bind Abst) w) u0)))) (ex nat (\lambda (n: nat).(eq T 
t0 (TSort n)))) (ex3_4 TList nat C T (\lambda (ws: TList).(\lambda (i: 
nat).(\lambda (_: C).(\lambda (_: T).(eq T t0 (THeads (Flat Appl) ws (TLRef 
i))))))) (\lambda (_: TList).(\lambda (i: nat).(\lambda (d: C).(\lambda (v: 
T).(getl i c0 (CHead d (Bind Abst) v)))))) (\lambda (ws: TList).(\lambda (_: 
nat).(\lambda (_: C).(\lambda (_: T).(nfs2 c0 ws)))))))))).(\lambda (H4: (nf2 
c0 (THead (Flat Cast) u t0))).(nf2_gen_cast c0 u t0 H4 (or3 (ex3_2 T T 
(\lambda (w: T).(\lambda (u0: T).(eq T (THead (Flat Cast) u t0) (THead (Bind 
Abst) w u0)))) (\lambda (w: T).(\lambda (_: T).(nf2 c0 w))) (\lambda (w: 
T).(\lambda (u0: T).(nf2 (CHead c0 (Bind Abst) w) u0)))) (ex nat (\lambda (n: 
nat).(eq T (THead (Flat Cast) u t0) (TSort n)))) (ex3_4 TList nat C T 
(\lambda (ws: TList).(\lambda (i: nat).(\lambda (_: C).(\lambda (_: T).(eq T 
(THead (Flat Cast) u t0) (THeads (Flat Appl) ws (TLRef i))))))) (\lambda (_: 
TList).(\lambda (i: nat).(\lambda (d: C).(\lambda (v: T).(getl i c0 (CHead d 
(Bind Abst) v)))))) (\lambda (ws: TList).(\lambda (_: nat).(\lambda (_: 
C).(\lambda (_: T).(nfs2 c0 ws))))))))))))))))) (\lambda (c0: C).(\lambda 
(t0: T).(\lambda (a1: A).(\lambda (_: (arity g c0 t0 a1)).(\lambda (H1: 
(((nf2 c0 t0) \to (or3 (ex3_2 T T (\lambda (w: T).(\lambda (u: T).(eq T t0 
(THead (Bind Abst) w u)))) (\lambda (w: T).(\lambda (_: T).(nf2 c0 w))) 
(\lambda (w: T).(\lambda (u: T).(nf2 (CHead c0 (Bind Abst) w) u)))) (ex nat 
(\lambda (n: nat).(eq T t0 (TSort n)))) (ex3_4 TList nat C T (\lambda (ws: 
TList).(\lambda (i: nat).(\lambda (_: C).(\lambda (_: T).(eq T t0 (THeads 
(Flat Appl) ws (TLRef i))))))) (\lambda (_: TList).(\lambda (i: nat).(\lambda 
(d: C).(\lambda (v: T).(getl i c0 (CHead d (Bind Abst) v)))))) (\lambda (ws: 
TList).(\lambda (_: nat).(\lambda (_: C).(\lambda (_: T).(nfs2 c0 
ws)))))))))).(\lambda (a2: A).(\lambda (_: (leq g a1 a2)).(\lambda (H3: (nf2 
c0 t0)).(let H_x \def (H1 H3) in (let H4 \def H_x in (or3_ind (ex3_2 T T 
(\lambda (w: T).(\lambda (u: T).(eq T t0 (THead (Bind Abst) w u)))) (\lambda 
(w: T).(\lambda (_: T).(nf2 c0 w))) (\lambda (w: T).(\lambda (u: T).(nf2 
(CHead c0 (Bind Abst) w) u)))) (ex nat (\lambda (n: nat).(eq T t0 (TSort 
n)))) (ex3_4 TList nat C T (\lambda (ws: TList).(\lambda (i: nat).(\lambda 
(_: C).(\lambda (_: T).(eq T t0 (THeads (Flat Appl) ws (TLRef i))))))) 
(\lambda (_: TList).(\lambda (i: nat).(\lambda (d: C).(\lambda (v: T).(getl i 
c0 (CHead d (Bind Abst) v)))))) (\lambda (ws: TList).(\lambda (_: 
nat).(\lambda (_: C).(\lambda (_: T).(nfs2 c0 ws)))))) (or3 (ex3_2 T T 
(\lambda (w: T).(\lambda (u: T).(eq T t0 (THead (Bind Abst) w u)))) (\lambda 
(w: T).(\lambda (_: T).(nf2 c0 w))) (\lambda (w: T).(\lambda (u: T).(nf2 
(CHead c0 (Bind Abst) w) u)))) (ex nat (\lambda (n: nat).(eq T t0 (TSort 
n)))) (ex3_4 TList nat C T (\lambda (ws: TList).(\lambda (i: nat).(\lambda 
(_: C).(\lambda (_: T).(eq T t0 (THeads (Flat Appl) ws (TLRef i))))))) 
(\lambda (_: TList).(\lambda (i: nat).(\lambda (d: C).(\lambda (v: T).(getl i 
c0 (CHead d (Bind Abst) v)))))) (\lambda (ws: TList).(\lambda (_: 
nat).(\lambda (_: C).(\lambda (_: T).(nfs2 c0 ws))))))) (\lambda (H5: (ex3_2 
T T (\lambda (w: T).(\lambda (u: T).(eq T t0 (THead (Bind Abst) w u)))) 
(\lambda (w: T).(\lambda (_: T).(nf2 c0 w))) (\lambda (w: T).(\lambda (u: 
T).(nf2 (CHead c0 (Bind Abst) w) u))))).(ex3_2_ind T T (\lambda (w: 
T).(\lambda (u: T).(eq T t0 (THead (Bind Abst) w u)))) (\lambda (w: 
T).(\lambda (_: T).(nf2 c0 w))) (\lambda (w: T).(\lambda (u: T).(nf2 (CHead 
c0 (Bind Abst) w) u))) (or3 (ex3_2 T T (\lambda (w: T).(\lambda (u: T).(eq T 
t0 (THead (Bind Abst) w u)))) (\lambda (w: T).(\lambda (_: T).(nf2 c0 w))) 
(\lambda (w: T).(\lambda (u: T).(nf2 (CHead c0 (Bind Abst) w) u)))) (ex nat 
(\lambda (n: nat).(eq T t0 (TSort n)))) (ex3_4 TList nat C T (\lambda (ws: 
TList).(\lambda (i: nat).(\lambda (_: C).(\lambda (_: T).(eq T t0 (THeads 
(Flat Appl) ws (TLRef i))))))) (\lambda (_: TList).(\lambda (i: nat).(\lambda 
(d: C).(\lambda (v: T).(getl i c0 (CHead d (Bind Abst) v)))))) (\lambda (ws: 
TList).(\lambda (_: nat).(\lambda (_: C).(\lambda (_: T).(nfs2 c0 ws))))))) 
(\lambda (x0: T).(\lambda (x1: T).(\lambda (H6: (eq T t0 (THead (Bind Abst) 
x0 x1))).(\lambda (H7: (nf2 c0 x0)).(\lambda (H8: (nf2 (CHead c0 (Bind Abst) 
x0) x1)).(eq_ind_r T (THead (Bind Abst) x0 x1) (\lambda (t1: T).(or3 (ex3_2 T 
T (\lambda (w: T).(\lambda (u: T).(eq T t1 (THead (Bind Abst) w u)))) 
(\lambda (w: T).(\lambda (_: T).(nf2 c0 w))) (\lambda (w: T).(\lambda (u: 
T).(nf2 (CHead c0 (Bind Abst) w) u)))) (ex nat (\lambda (n: nat).(eq T t1 
(TSort n)))) (ex3_4 TList nat C T (\lambda (ws: TList).(\lambda (i: 
nat).(\lambda (_: C).(\lambda (_: T).(eq T t1 (THeads (Flat Appl) ws (TLRef 
i))))))) (\lambda (_: TList).(\lambda (i: nat).(\lambda (d: C).(\lambda (v: 
T).(getl i c0 (CHead d (Bind Abst) v)))))) (\lambda (ws: TList).(\lambda (_: 
nat).(\lambda (_: C).(\lambda (_: T).(nfs2 c0 ws)))))))) (or3_intro0 (ex3_2 T 
T (\lambda (w: T).(\lambda (u: T).(eq T (THead (Bind Abst) x0 x1) (THead 
(Bind Abst) w u)))) (\lambda (w: T).(\lambda (_: T).(nf2 c0 w))) (\lambda (w: 
T).(\lambda (u: T).(nf2 (CHead c0 (Bind Abst) w) u)))) (ex nat (\lambda (n: 
nat).(eq T (THead (Bind Abst) x0 x1) (TSort n)))) (ex3_4 TList nat C T 
(\lambda (ws: TList).(\lambda (i: nat).(\lambda (_: C).(\lambda (_: T).(eq T 
(THead (Bind Abst) x0 x1) (THeads (Flat Appl) ws (TLRef i))))))) (\lambda (_: 
TList).(\lambda (i: nat).(\lambda (d: C).(\lambda (v: T).(getl i c0 (CHead d 
(Bind Abst) v)))))) (\lambda (ws: TList).(\lambda (_: nat).(\lambda (_: 
C).(\lambda (_: T).(nfs2 c0 ws)))))) (ex3_2_intro T T (\lambda (w: 
T).(\lambda (u: T).(eq T (THead (Bind Abst) x0 x1) (THead (Bind Abst) w u)))) 
(\lambda (w: T).(\lambda (_: T).(nf2 c0 w))) (\lambda (w: T).(\lambda (u: 
T).(nf2 (CHead c0 (Bind Abst) w) u))) x0 x1 (refl_equal T (THead (Bind Abst) 
x0 x1)) H7 H8)) t0 H6)))))) H5)) (\lambda (H5: (ex nat (\lambda (n: nat).(eq 
T t0 (TSort n))))).(ex_ind nat (\lambda (n: nat).(eq T t0 (TSort n))) (or3 
(ex3_2 T T (\lambda (w: T).(\lambda (u: T).(eq T t0 (THead (Bind Abst) w 
u)))) (\lambda (w: T).(\lambda (_: T).(nf2 c0 w))) (\lambda (w: T).(\lambda 
(u: T).(nf2 (CHead c0 (Bind Abst) w) u)))) (ex nat (\lambda (n: nat).(eq T t0 
(TSort n)))) (ex3_4 TList nat C T (\lambda (ws: TList).(\lambda (i: 
nat).(\lambda (_: C).(\lambda (_: T).(eq T t0 (THeads (Flat Appl) ws (TLRef 
i))))))) (\lambda (_: TList).(\lambda (i: nat).(\lambda (d: C).(\lambda (v: 
T).(getl i c0 (CHead d (Bind Abst) v)))))) (\lambda (ws: TList).(\lambda (_: 
nat).(\lambda (_: C).(\lambda (_: T).(nfs2 c0 ws))))))) (\lambda (x: 
nat).(\lambda (H6: (eq T t0 (TSort x))).(eq_ind_r T (TSort x) (\lambda (t1: 
T).(or3 (ex3_2 T T (\lambda (w: T).(\lambda (u: T).(eq T t1 (THead (Bind 
Abst) w u)))) (\lambda (w: T).(\lambda (_: T).(nf2 c0 w))) (\lambda (w: 
T).(\lambda (u: T).(nf2 (CHead c0 (Bind Abst) w) u)))) (ex nat (\lambda (n: 
nat).(eq T t1 (TSort n)))) (ex3_4 TList nat C T (\lambda (ws: TList).(\lambda 
(i: nat).(\lambda (_: C).(\lambda (_: T).(eq T t1 (THeads (Flat Appl) ws 
(TLRef i))))))) (\lambda (_: TList).(\lambda (i: nat).(\lambda (d: 
C).(\lambda (v: T).(getl i c0 (CHead d (Bind Abst) v)))))) (\lambda (ws: 
TList).(\lambda (_: nat).(\lambda (_: C).(\lambda (_: T).(nfs2 c0 ws)))))))) 
(or3_intro1 (ex3_2 T T (\lambda (w: T).(\lambda (u: T).(eq T (TSort x) (THead 
(Bind Abst) w u)))) (\lambda (w: T).(\lambda (_: T).(nf2 c0 w))) (\lambda (w: 
T).(\lambda (u: T).(nf2 (CHead c0 (Bind Abst) w) u)))) (ex nat (\lambda (n: 
nat).(eq T (TSort x) (TSort n)))) (ex3_4 TList nat C T (\lambda (ws: 
TList).(\lambda (i: nat).(\lambda (_: C).(\lambda (_: T).(eq T (TSort x) 
(THeads (Flat Appl) ws (TLRef i))))))) (\lambda (_: TList).(\lambda (i: 
nat).(\lambda (d: C).(\lambda (v: T).(getl i c0 (CHead d (Bind Abst) v)))))) 
(\lambda (ws: TList).(\lambda (_: nat).(\lambda (_: C).(\lambda (_: T).(nfs2 
c0 ws)))))) (ex_intro nat (\lambda (n: nat).(eq T (TSort x) (TSort n))) x 
(refl_equal T (TSort x)))) t0 H6))) H5)) (\lambda (H5: (ex3_4 TList nat C T 
(\lambda (ws: TList).(\lambda (i: nat).(\lambda (_: C).(\lambda (_: T).(eq T 
t0 (THeads (Flat Appl) ws (TLRef i))))))) (\lambda (_: TList).(\lambda (i: 
nat).(\lambda (d: C).(\lambda (v: T).(getl i c0 (CHead d (Bind Abst) v)))))) 
(\lambda (ws: TList).(\lambda (_: nat).(\lambda (_: C).(\lambda (_: T).(nfs2 
c0 ws))))))).(ex3_4_ind TList nat C T (\lambda (ws: TList).(\lambda (i: 
nat).(\lambda (_: C).(\lambda (_: T).(eq T t0 (THeads (Flat Appl) ws (TLRef 
i))))))) (\lambda (_: TList).(\lambda (i: nat).(\lambda (d: C).(\lambda (v: 
T).(getl i c0 (CHead d (Bind Abst) v)))))) (\lambda (ws: TList).(\lambda (_: 
nat).(\lambda (_: C).(\lambda (_: T).(nfs2 c0 ws))))) (or3 (ex3_2 T T 
(\lambda (w: T).(\lambda (u: T).(eq T t0 (THead (Bind Abst) w u)))) (\lambda 
(w: T).(\lambda (_: T).(nf2 c0 w))) (\lambda (w: T).(\lambda (u: T).(nf2 
(CHead c0 (Bind Abst) w) u)))) (ex nat (\lambda (n: nat).(eq T t0 (TSort 
n)))) (ex3_4 TList nat C T (\lambda (ws: TList).(\lambda (i: nat).(\lambda 
(_: C).(\lambda (_: T).(eq T t0 (THeads (Flat Appl) ws (TLRef i))))))) 
(\lambda (_: TList).(\lambda (i: nat).(\lambda (d: C).(\lambda (v: T).(getl i 
c0 (CHead d (Bind Abst) v)))))) (\lambda (ws: TList).(\lambda (_: 
nat).(\lambda (_: C).(\lambda (_: T).(nfs2 c0 ws))))))) (\lambda (x0: 
TList).(\lambda (x1: nat).(\lambda (x2: C).(\lambda (x3: T).(\lambda (H6: (eq 
T t0 (THeads (Flat Appl) x0 (TLRef x1)))).(\lambda (H7: (getl x1 c0 (CHead x2 
(Bind Abst) x3))).(\lambda (H8: (nfs2 c0 x0)).(eq_ind_r T (THeads (Flat Appl) 
x0 (TLRef x1)) (\lambda (t1: T).(or3 (ex3_2 T T (\lambda (w: T).(\lambda (u: 
T).(eq T t1 (THead (Bind Abst) w u)))) (\lambda (w: T).(\lambda (_: T).(nf2 
c0 w))) (\lambda (w: T).(\lambda (u: T).(nf2 (CHead c0 (Bind Abst) w) u)))) 
(ex nat (\lambda (n: nat).(eq T t1 (TSort n)))) (ex3_4 TList nat C T (\lambda 
(ws: TList).(\lambda (i: nat).(\lambda (_: C).(\lambda (_: T).(eq T t1 
(THeads (Flat Appl) ws (TLRef i))))))) (\lambda (_: TList).(\lambda (i: 
nat).(\lambda (d: C).(\lambda (v: T).(getl i c0 (CHead d (Bind Abst) v)))))) 
(\lambda (ws: TList).(\lambda (_: nat).(\lambda (_: C).(\lambda (_: T).(nfs2 
c0 ws)))))))) (or3_intro2 (ex3_2 T T (\lambda (w: T).(\lambda (u: T).(eq T 
(THeads (Flat Appl) x0 (TLRef x1)) (THead (Bind Abst) w u)))) (\lambda (w: 
T).(\lambda (_: T).(nf2 c0 w))) (\lambda (w: T).(\lambda (u: T).(nf2 (CHead 
c0 (Bind Abst) w) u)))) (ex nat (\lambda (n: nat).(eq T (THeads (Flat Appl) 
x0 (TLRef x1)) (TSort n)))) (ex3_4 TList nat C T (\lambda (ws: 
TList).(\lambda (i: nat).(\lambda (_: C).(\lambda (_: T).(eq T (THeads (Flat 
Appl) x0 (TLRef x1)) (THeads (Flat Appl) ws (TLRef i))))))) (\lambda (_: 
TList).(\lambda (i: nat).(\lambda (d: C).(\lambda (v: T).(getl i c0 (CHead d 
(Bind Abst) v)))))) (\lambda (ws: TList).(\lambda (_: nat).(\lambda (_: 
C).(\lambda (_: T).(nfs2 c0 ws)))))) (ex3_4_intro TList nat C T (\lambda (ws: 
TList).(\lambda (i: nat).(\lambda (_: C).(\lambda (_: T).(eq T (THeads (Flat 
Appl) x0 (TLRef x1)) (THeads (Flat Appl) ws (TLRef i))))))) (\lambda (_: 
TList).(\lambda (i: nat).(\lambda (d: C).(\lambda (v: T).(getl i c0 (CHead d 
(Bind Abst) v)))))) (\lambda (ws: TList).(\lambda (_: nat).(\lambda (_: 
C).(\lambda (_: T).(nfs2 c0 ws))))) x0 x1 x2 x3 (refl_equal T (THeads (Flat 
Appl) x0 (TLRef x1))) H7 H8)) t0 H6)))))))) H5)) H4))))))))))) c t a H))))).

theorem pc3_gen_sort_abst:
 \forall (c: C).(\forall (u: T).(\forall (t: T).(\forall (n: nat).((pc3 c 
(TSort n) (THead (Bind Abst) u t)) \to (\forall (P: Prop).P)))))
\def
 \lambda (c: C).(\lambda (u: T).(\lambda (t: T).(\lambda (n: nat).(\lambda 
(H: (pc3 c (TSort n) (THead (Bind Abst) u t))).(\lambda (P: Prop).(let H0 
\def H in (ex2_ind T (\lambda (t0: T).(pr3 c (TSort n) t0)) (\lambda (t0: 
T).(pr3 c (THead (Bind Abst) u t) t0)) P (\lambda (x: T).(\lambda (H1: (pr3 c 
(TSort n) x)).(\lambda (H2: (pr3 c (THead (Bind Abst) u t) x)).(let H3 \def 
(pr3_gen_abst c u t x H2) in (ex3_2_ind T T (\lambda (u2: T).(\lambda (t2: 
T).(eq T x (THead (Bind Abst) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr3 
c u u2))) (\lambda (_: T).(\lambda (t2: T).(\forall (b: B).(\forall (u0: 
T).(pr3 (CHead c (Bind b) u0) t t2))))) P (\lambda (x0: T).(\lambda (x1: 
T).(\lambda (H4: (eq T x (THead (Bind Abst) x0 x1))).(\lambda (_: (pr3 c u 
x0)).(\lambda (_: ((\forall (b: B).(\forall (u0: T).(pr3 (CHead c (Bind b) 
u0) t x1))))).(let H7 \def (eq_ind T x (\lambda (t0: T).(eq T t0 (TSort n))) 
(pr3_gen_sort c x n H1) (THead (Bind Abst) x0 x1) H4) in (let H8 \def (eq_ind 
T (THead (Bind Abst) x0 x1) (\lambda (ee: T).(match ee in T return (\lambda 
(_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False 
| (THead _ _ _) \Rightarrow True])) I (TSort n) H7) in (False_ind P 
H8)))))))) H3))))) H0))))))).

theorem ty3_gen_abst_abst:
 \forall (g: G).(\forall (c: C).(\forall (u: T).(\forall (t1: T).(\forall 
(t2: T).((ty3 g c (THead (Bind Abst) u t1) (THead (Bind Abst) u t2)) \to (ex2 
T (\lambda (w: T).(ty3 g c u w)) (\lambda (_: T).(ty3 g (CHead c (Bind Abst) 
u) t1 t2))))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (u: T).(\lambda (t1: T).(\lambda 
(t2: T).(\lambda (H: (ty3 g c (THead (Bind Abst) u t1) (THead (Bind Abst) u 
t2))).(ex_ind T (\lambda (t: T).(ty3 g c (THead (Bind Abst) u t2) t)) (ex2 T 
(\lambda (w: T).(ty3 g c u w)) (\lambda (_: T).(ty3 g (CHead c (Bind Abst) u) 
t1 t2))) (\lambda (x: T).(\lambda (H0: (ty3 g c (THead (Bind Abst) u t2) 
x)).(ex4_3_ind T T T (\lambda (t3: T).(\lambda (_: T).(\lambda (_: T).(pc3 c 
(THead (Bind Abst) u t3) x)))) (\lambda (_: T).(\lambda (t: T).(\lambda (_: 
T).(ty3 g c u t)))) (\lambda (t3: T).(\lambda (_: T).(\lambda (_: T).(ty3 g 
(CHead c (Bind Abst) u) t2 t3)))) (\lambda (t3: T).(\lambda (_: T).(\lambda 
(t0: T).(ty3 g (CHead c (Bind Abst) u) t3 t0)))) (ex2 T (\lambda (w: T).(ty3 
g c u w)) (\lambda (_: T).(ty3 g (CHead c (Bind Abst) u) t1 t2))) (\lambda 
(x0: T).(\lambda (x1: T).(\lambda (x2: T).(\lambda (_: (pc3 c (THead (Bind 
Abst) u x0) x)).(\lambda (_: (ty3 g c u x1)).(\lambda (H3: (ty3 g (CHead c 
(Bind Abst) u) t2 x0)).(\lambda (_: (ty3 g (CHead c (Bind Abst) u) x0 
x2)).(ex4_3_ind T T T (\lambda (t3: T).(\lambda (_: T).(\lambda (_: T).(pc3 c 
(THead (Bind Abst) u t3) (THead (Bind Abst) u t2))))) (\lambda (_: 
T).(\lambda (t: T).(\lambda (_: T).(ty3 g c u t)))) (\lambda (t3: T).(\lambda 
(_: T).(\lambda (_: T).(ty3 g (CHead c (Bind Abst) u) t1 t3)))) (\lambda (t3: 
T).(\lambda (_: T).(\lambda (t0: T).(ty3 g (CHead c (Bind Abst) u) t3 t0)))) 
(ex2 T (\lambda (w: T).(ty3 g c u w)) (\lambda (_: T).(ty3 g (CHead c (Bind 
Abst) u) t1 t2))) (\lambda (x3: T).(\lambda (x4: T).(\lambda (x5: T).(\lambda 
(H5: (pc3 c (THead (Bind Abst) u x3) (THead (Bind Abst) u t2))).(\lambda (H6: 
(ty3 g c u x4)).(\lambda (H7: (ty3 g (CHead c (Bind Abst) u) t1 x3)).(\lambda 
(_: (ty3 g (CHead c (Bind Abst) u) x3 x5)).(and_ind (pc3 c u u) (\forall (b: 
B).(\forall (u0: T).(pc3 (CHead c (Bind b) u0) x3 t2))) (ex2 T (\lambda (w: 
T).(ty3 g c u w)) (\lambda (_: T).(ty3 g (CHead c (Bind Abst) u) t1 t2))) 
(\lambda (_: (pc3 c u u)).(\lambda (H10: ((\forall (b: B).(\forall (u0: 
T).(pc3 (CHead c (Bind b) u0) x3 t2))))).(ex_intro2 T (\lambda (w: T).(ty3 g 
c u w)) (\lambda (_: T).(ty3 g (CHead c (Bind Abst) u) t1 t2)) x4 H6 
(ty3_conv g (CHead c (Bind Abst) u) t2 x0 H3 t1 x3 H7 (H10 Abst u))))) 
(pc3_gen_abst c u u x3 t2 H5))))))))) (ty3_gen_bind g Abst c u t1 (THead 
(Bind Abst) u t2) H))))))))) (ty3_gen_bind g Abst c u t2 x H0)))) 
(ty3_correct g c (THead (Bind Abst) u t1) (THead (Bind Abst) u t2) H))))))).

theorem ty3_typecheck:
 \forall (g: G).(\forall (c: C).(\forall (t: T).(\forall (v: T).((ty3 g c t 
v) \to (ex T (\lambda (u: T).(ty3 g c (THead (Flat Cast) v t) u)))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (t: T).(\lambda (v: T).(\lambda (H: 
(ty3 g c t v)).(ex_ind T (\lambda (t0: T).(ty3 g c v t0)) (ex T (\lambda (u: 
T).(ty3 g c (THead (Flat Cast) v t) u))) (\lambda (x: T).(\lambda (H0: (ty3 g 
c v x)).(ex_intro T (\lambda (u: T).(ty3 g c (THead (Flat Cast) v t) u)) v 
(ty3_cast g c t v H x H0)))) (ty3_correct g c t v H)))))).

inductive sort: T \to Prop \def
| sort_sort: \forall (n: nat).(sort (TSort n))
| sort_abst: \forall (u: T).((sort u) \to (\forall (t: T).((sort t) \to (sort 
(THead (Bind Abst) u t))))).

theorem sort_nf2:
 \forall (t: T).((sort t) \to (\forall (c: C).(nf2 c t)))
\def
 \lambda (t: T).(\lambda (H: (sort t)).(sort_ind (\lambda (t0: T).(\forall 
(c: C).(nf2 c t0))) (\lambda (n: nat).(\lambda (c: C).(nf2_sort c n))) 
(\lambda (u: T).(\lambda (_: (sort u)).(\lambda (H1: ((\forall (c: C).(nf2 c 
u)))).(\lambda (t0: T).(\lambda (_: (sort t0)).(\lambda (H3: ((\forall (c: 
C).(nf2 c t0)))).(\lambda (c: C).(let H_y \def (H3 (CHead c (Bind Abst) u)) 
in (nf2_abst c u (H1 c) Abst u t0 H_y))))))))) t H)).

theorem sort_pc3:
 \forall (t1: T).((sort t1) \to (\forall (t2: T).((sort t2) \to (\forall (c: 
C).((pc3 c t1 t2) \to (eq T t1 t2))))))
\def
 \lambda (t1: T).(\lambda (H: (sort t1)).(sort_ind (\lambda (t: T).(\forall 
(t2: T).((sort t2) \to (\forall (c: C).((pc3 c t t2) \to (eq T t t2)))))) 
(\lambda (n: nat).(\lambda (t2: T).(\lambda (H0: (sort t2)).(sort_ind 
(\lambda (t: T).(\forall (c: C).((pc3 c (TSort n) t) \to (eq T (TSort n) 
t)))) (\lambda (n0: nat).(\lambda (c: C).(\lambda (H1: (pc3 c (TSort n) 
(TSort n0))).(eq_ind nat n (\lambda (n1: nat).(eq T (TSort n) (TSort n1))) 
(refl_equal T (TSort n)) n0 (pc3_gen_sort c n n0 H1))))) (\lambda (u: 
T).(\lambda (_: (sort u)).(\lambda (_: ((\forall (c: C).((pc3 c (TSort n) u) 
\to (eq T (TSort n) u))))).(\lambda (t: T).(\lambda (_: (sort t)).(\lambda 
(_: ((\forall (c: C).((pc3 c (TSort n) t) \to (eq T (TSort n) t))))).(\lambda 
(c: C).(\lambda (H5: (pc3 c (TSort n) (THead (Bind Abst) u 
t))).(pc3_gen_sort_abst c u t n H5 (eq T (TSort n) (THead (Bind Abst) u 
t))))))))))) t2 H0)))) (\lambda (u: T).(\lambda (_: (sort u)).(\lambda (H1: 
((\forall (t2: T).((sort t2) \to (\forall (c: C).((pc3 c u t2) \to (eq T u 
t2))))))).(\lambda (t: T).(\lambda (_: (sort t)).(\lambda (H3: ((\forall (t2: 
T).((sort t2) \to (\forall (c: C).((pc3 c t t2) \to (eq T t 
t2))))))).(\lambda (t2: T).(\lambda (H4: (sort t2)).(sort_ind (\lambda (t0: 
T).(\forall (c: C).((pc3 c (THead (Bind Abst) u t) t0) \to (eq T (THead (Bind 
Abst) u t) t0)))) (\lambda (n: nat).(\lambda (c: C).(\lambda (H5: (pc3 c 
(THead (Bind Abst) u t) (TSort n))).(pc3_gen_sort_abst c u t n (pc3_s c 
(TSort n) (THead (Bind Abst) u t) H5) (eq T (THead (Bind Abst) u t) (TSort 
n)))))) (\lambda (u0: T).(\lambda (H5: (sort u0)).(\lambda (_: ((\forall (c: 
C).((pc3 c (THead (Bind Abst) u t) u0) \to (eq T (THead (Bind Abst) u t) 
u0))))).(\lambda (t0: T).(\lambda (H7: (sort t0)).(\lambda (_: ((\forall (c: 
C).((pc3 c (THead (Bind Abst) u t) t0) \to (eq T (THead (Bind Abst) u t) 
t0))))).(\lambda (c: C).(\lambda (H9: (pc3 c (THead (Bind Abst) u t) (THead 
(Bind Abst) u0 t0))).(and_ind (pc3 c u u0) (\forall (b: B).(\forall (u1: 
T).(pc3 (CHead c (Bind b) u1) t t0))) (eq T (THead (Bind Abst) u t) (THead 
(Bind Abst) u0 t0)) (\lambda (H10: (pc3 c u u0)).(\lambda (H11: ((\forall (b: 
B).(\forall (u1: T).(pc3 (CHead c (Bind b) u1) t t0))))).(let H_y \def (H11 
Abbr u) in (let H_y0 \def (H1 u0 H5 c H10) in (let H_y1 \def (H3 t0 H7 (CHead 
c (Bind Abbr) u) H_y) in (let H12 \def (eq_ind_r T t0 (\lambda (t3: T).(pc3 
(CHead c (Bind Abbr) u) t t3)) H_y t H_y1) in (let H13 \def (eq_ind_r T t0 
(\lambda (t3: T).(sort t3)) H7 t H_y1) in (eq_ind T t (\lambda (t3: T).(eq T 
(THead (Bind Abst) u t) (THead (Bind Abst) u0 t3))) (let H14 \def (eq_ind_r T 
u0 (\lambda (t3: T).(pc3 c u t3)) H10 u H_y0) in (let H15 \def (eq_ind_r T u0 
(\lambda (t3: T).(sort t3)) H5 u H_y0) in (eq_ind T u (\lambda (t3: T).(eq T 
(THead (Bind Abst) u t) (THead (Bind Abst) t3 t))) (refl_equal T (THead (Bind 
Abst) u t)) u0 H_y0))) t0 H_y1)))))))) (pc3_gen_abst c u u0 t t0 H9)))))))))) 
t2 H4))))))))) t1 H)).

theorem sort_correct:
 \forall (g: G).(\forall (t1: T).((sort t1) \to (\forall (c: C).(ex3 T 
(\lambda (t2: T).(tau0 g c t1 t2)) (\lambda (t2: T).(ty3 g c t1 t2)) (\lambda 
(t2: T).(sort t2))))))
\def
 \lambda (g: G).(\lambda (t1: T).(\lambda (H: (sort t1)).(sort_ind (\lambda 
(t: T).(\forall (c: C).(ex3 T (\lambda (t2: T).(tau0 g c t t2)) (\lambda (t2: 
T).(ty3 g c t t2)) (\lambda (t2: T).(sort t2))))) (\lambda (n: nat).(\lambda 
(c: C).(ex3_intro T (\lambda (t2: T).(tau0 g c (TSort n) t2)) (\lambda (t2: 
T).(ty3 g c (TSort n) t2)) (\lambda (t2: T).(sort t2)) (TSort (next g n)) 
(tau0_sort g c n) (ty3_sort g c n) (sort_sort (next g n))))) (\lambda (u: 
T).(\lambda (H0: (sort u)).(\lambda (H1: ((\forall (c: C).(ex3 T (\lambda 
(t2: T).(tau0 g c u t2)) (\lambda (t2: T).(ty3 g c u t2)) (\lambda (t2: 
T).(sort t2)))))).(\lambda (t: T).(\lambda (_: (sort t)).(\lambda (H3: 
((\forall (c: C).(ex3 T (\lambda (t2: T).(tau0 g c t t2)) (\lambda (t2: 
T).(ty3 g c t t2)) (\lambda (t2: T).(sort t2)))))).(\lambda (c: C).(let H_x 
\def (H1 c) in (let H4 \def H_x in (ex3_ind T (\lambda (t2: T).(tau0 g c u 
t2)) (\lambda (t2: T).(ty3 g c u t2)) (\lambda (t2: T).(sort t2)) (ex3 T 
(\lambda (t2: T).(tau0 g c (THead (Bind Abst) u t) t2)) (\lambda (t2: T).(ty3 
g c (THead (Bind Abst) u t) t2)) (\lambda (t2: T).(sort t2))) (\lambda (x0: 
T).(\lambda (_: (tau0 g c u x0)).(\lambda (H6: (ty3 g c u x0)).(\lambda (_: 
(sort x0)).(let H_x0 \def (H3 (CHead c (Bind Abst) u)) in (let H8 \def H_x0 
in (ex3_ind T (\lambda (t2: T).(tau0 g (CHead c (Bind Abst) u) t t2)) 
(\lambda (t2: T).(ty3 g (CHead c (Bind Abst) u) t t2)) (\lambda (t2: T).(sort 
t2)) (ex3 T (\lambda (t2: T).(tau0 g c (THead (Bind Abst) u t) t2)) (\lambda 
(t2: T).(ty3 g c (THead (Bind Abst) u t) t2)) (\lambda (t2: T).(sort t2))) 
(\lambda (x1: T).(\lambda (H9: (tau0 g (CHead c (Bind Abst) u) t 
x1)).(\lambda (H10: (ty3 g (CHead c (Bind Abst) u) t x1)).(\lambda (H11: 
(sort x1)).(ex_ind T (\lambda (t0: T).(ty3 g (CHead c (Bind Abst) u) x1 t0)) 
(ex3 T (\lambda (t2: T).(tau0 g c (THead (Bind Abst) u t) t2)) (\lambda (t2: 
T).(ty3 g c (THead (Bind Abst) u t) t2)) (\lambda (t2: T).(sort t2))) 
(\lambda (x: T).(\lambda (H12: (ty3 g (CHead c (Bind Abst) u) x1 
x)).(ex3_intro T (\lambda (t2: T).(tau0 g c (THead (Bind Abst) u t) t2)) 
(\lambda (t2: T).(ty3 g c (THead (Bind Abst) u t) t2)) (\lambda (t2: T).(sort 
t2)) (THead (Bind Abst) u x1) (tau0_bind g Abst c u t x1 H9) (ty3_bind g c u 
x0 H6 Abst t x1 H10 x H12) (sort_abst u H0 x1 H11)))) (ty3_correct g (CHead c 
(Bind Abst) u) t x1 H10)))))) H8))))))) H4)))))))))) t1 H))).

definition pchurch_context:
 T \to (T \to T)
\def
 \lambda (t: T).(\lambda (u: T).(THead (Bind Abst) t (THead (Bind Abst) 
(THead (Bind Abst) (lift (S O) O t) (lift (S (S O)) O t)) u))).

definition pnat:
 T \to T
\def
 \lambda (t: T).(pchurch_context t (lift (S (S O)) O t)).

definition church_body:
 nat \to T
\def
 let rec church_body (n: nat) on n: T \def (match n with [O \Rightarrow 
(TLRef (S O)) | (S n0) \Rightarrow (THead (Flat Appl) (church_body n0) (TLRef 
O))]) in church_body.

definition pchurch:
 T \to (nat \to T)
\def
 \lambda (t: T).(\lambda (n: nat).(pchurch_context t (church_body n))).

theorem pnat_props__lift_SSO_O:
 \forall (t: T).(eq T (lift (S (S O)) O t) (lift (S O) O (lift (S O) O t)))
\def
 \lambda (t: T).(eq_ind_r T (lift (plus (S O) (S O)) O t) (\lambda (t0: 
T).(eq T (lift (S (S O)) O t) t0)) (refl_equal T (lift (plus (S O) (S O)) O 
t)) (lift (S O) O (lift (S O) O t)) (lift_free t (S O) (S O) O O (le_O_n 
(plus O (S O))) (le_n O))).

theorem pnat_props__lift_SO_SO:
 \forall (t: T).(eq T (lift (S O) (S O) (lift (S O) O t)) (lift (S O) O (lift 
(S O) O t)))
\def
 \lambda (t: T).(eq_ind nat (plus (S O) O) (\lambda (n: nat).(eq T (lift (S 
O) n (lift (S O) O t)) (lift (S O) O (lift (S O) O t)))) (eq_ind_r T (lift (S 
O) O (lift (S O) O t)) (\lambda (t0: T).(eq T t0 (lift (S O) O (lift (S O) O 
t)))) (refl_equal T (lift (S O) O (lift (S O) O t))) (lift (S O) (plus (S O) 
O) (lift (S O) O t)) (lift_d t (S O) (S O) O O (le_n O))) (S O) (refl_equal 
nat (S O))).

theorem pnat_ty3:
 \forall (g: G).(\forall (c: C).(\forall (t: T).(\forall (u: T).((ty3 g c t 
u) \to (\forall (n: nat).(ty3 g c (pchurch t n) (pnat t)))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (t: T).(\lambda (u: T).(\lambda (H: 
(ty3 g c t u)).(ex_ind T (\lambda (t0: T).(ty3 g c u t0)) (\forall (n: 
nat).(ty3 g c (THead (Bind Abst) t (THead (Bind Abst) (THead (Bind Abst) 
(lift (S O) O t) (lift (S (S O)) O t)) (church_body n))) (THead (Bind Abst) t 
(THead (Bind Abst) (THead (Bind Abst) (lift (S O) O t) (lift (S (S O)) O t)) 
(lift (S (S O)) O t))))) (\lambda (x: T).(\lambda (H0: (ty3 g c u 
x)).(\lambda (n: nat).(nat_ind (\lambda (n0: nat).(ty3 g c (THead (Bind Abst) 
t (THead (Bind Abst) (THead (Bind Abst) (lift (S O) O t) (lift (S (S O)) O 
t)) (church_body n0))) (THead (Bind Abst) t (THead (Bind Abst) (THead (Bind 
Abst) (lift (S O) O t) (lift (S (S O)) O t)) (lift (S (S O)) O t))))) 
(ty3_bind g c t u H Abst (THead (Bind Abst) (THead (Bind Abst) (lift (S O) O 
t) (lift (S (S O)) O t)) (TLRef (S O))) (THead (Bind Abst) (THead (Bind Abst) 
(lift (S O) O t) (lift (S (S O)) O t)) (lift (S (S O)) O t)) (ty3_bind g 
(CHead c (Bind Abst) t) (THead (Bind Abst) (lift (S O) O t) (lift (S (S O)) O 
t)) (THead (Bind Abst) (lift (S O) O t) (lift (S (S O)) O u)) (ty3_bind g 
(CHead c (Bind Abst) t) (lift (S O) O t) (lift (S O) O u) (ty3_lift g c t u H 
(CHead c (Bind Abst) t) O (S O) (drop_drop (Bind Abst) O c c (drop_refl c) 
t)) Abst (lift (S (S O)) O t) (lift (S (S O)) O u) (ty3_lift g c t u H (CHead 
(CHead c (Bind Abst) t) (Bind Abst) (lift (S O) O t)) O (S (S O)) (drop_S 
Abst (CHead (CHead c (Bind Abst) t) (Bind Abst) (lift (S O) O t)) c t (S O) 
(drop_drop (Bind Abst) O (CHead c (Bind Abst) t) (CHead c (Bind Abst) t) 
(drop_refl (CHead c (Bind Abst) t)) (lift (S O) O t)))) (lift (S (S O)) O x) 
(ty3_lift g c u x H0 (CHead (CHead c (Bind Abst) t) (Bind Abst) (lift (S O) O 
t)) O (S (S O)) (drop_S Abst (CHead (CHead c (Bind Abst) t) (Bind Abst) (lift 
(S O) O t)) c t (S O) (drop_drop (Bind Abst) O (CHead c (Bind Abst) t) (CHead 
c (Bind Abst) t) (drop_refl (CHead c (Bind Abst) t)) (lift (S O) O t))))) 
Abst (TLRef (S O)) (lift (S (S O)) O t) (ty3_abst g (S O) (CHead (CHead c 
(Bind Abst) t) (Bind Abst) (THead (Bind Abst) (lift (S O) O t) (lift (S (S 
O)) O t))) c t (getl_head (Bind Abst) O (CHead c (Bind Abst) t) (CHead c 
(Bind Abst) t) (getl_refl Abst c t) (THead (Bind Abst) (lift (S O) O t) (lift 
(S (S O)) O t))) u H) (lift (S (S O)) O u) (ty3_lift g c t u H (CHead (CHead 
c (Bind Abst) t) (Bind Abst) (THead (Bind Abst) (lift (S O) O t) (lift (S (S 
O)) O t))) O (S (S O)) (drop_S Abst (CHead (CHead c (Bind Abst) t) (Bind 
Abst) (THead (Bind Abst) (lift (S O) O t) (lift (S (S O)) O t))) c t (S O) 
(drop_drop (Bind Abst) O (CHead c (Bind Abst) t) (CHead c (Bind Abst) t) 
(drop_refl (CHead c (Bind Abst) t)) (THead (Bind Abst) (lift (S O) O t) (lift 
(S (S O)) O t)))))) (THead (Bind Abst) (THead (Bind Abst) (lift (S O) O t) 
(lift (S (S O)) O t)) (lift (S (S O)) O u)) (ty3_bind g (CHead c (Bind Abst) 
t) (THead (Bind Abst) (lift (S O) O t) (lift (S (S O)) O t)) (THead (Bind 
Abst) (lift (S O) O t) (lift (S (S O)) O u)) (ty3_bind g (CHead c (Bind Abst) 
t) (lift (S O) O t) (lift (S O) O u) (ty3_lift g c t u H (CHead c (Bind Abst) 
t) O (S O) (drop_drop (Bind Abst) O c c (drop_refl c) t)) Abst (lift (S (S 
O)) O t) (lift (S (S O)) O u) (ty3_lift g c t u H (CHead (CHead c (Bind Abst) 
t) (Bind Abst) (lift (S O) O t)) O (S (S O)) (drop_S Abst (CHead (CHead c 
(Bind Abst) t) (Bind Abst) (lift (S O) O t)) c t (S O) (drop_drop (Bind Abst) 
O (CHead c (Bind Abst) t) (CHead c (Bind Abst) t) (drop_refl (CHead c (Bind 
Abst) t)) (lift (S O) O t)))) (lift (S (S O)) O x) (ty3_lift g c u x H0 
(CHead (CHead c (Bind Abst) t) (Bind Abst) (lift (S O) O t)) O (S (S O)) 
(drop_S Abst (CHead (CHead c (Bind Abst) t) (Bind Abst) (lift (S O) O t)) c t 
(S O) (drop_drop (Bind Abst) O (CHead c (Bind Abst) t) (CHead c (Bind Abst) 
t) (drop_refl (CHead c (Bind Abst) t)) (lift (S O) O t))))) Abst (lift (S (S 
O)) O t) (lift (S (S O)) O u) (ty3_lift g c t u H (CHead (CHead c (Bind Abst) 
t) (Bind Abst) (THead (Bind Abst) (lift (S O) O t) (lift (S (S O)) O t))) O 
(S (S O)) (drop_S Abst (CHead (CHead c (Bind Abst) t) (Bind Abst) (THead 
(Bind Abst) (lift (S O) O t) (lift (S (S O)) O t))) c t (S O) (drop_drop 
(Bind Abst) O (CHead c (Bind Abst) t) (CHead c (Bind Abst) t) (drop_refl 
(CHead c (Bind Abst) t)) (THead (Bind Abst) (lift (S O) O t) (lift (S (S O)) 
O t))))) (lift (S (S O)) O x) (ty3_lift g c u x H0 (CHead (CHead c (Bind 
Abst) t) (Bind Abst) (THead (Bind Abst) (lift (S O) O t) (lift (S (S O)) O 
t))) O (S (S O)) (drop_S Abst (CHead (CHead c (Bind Abst) t) (Bind Abst) 
(THead (Bind Abst) (lift (S O) O t) (lift (S (S O)) O t))) c t (S O) 
(drop_drop (Bind Abst) O (CHead c (Bind Abst) t) (CHead c (Bind Abst) t) 
(drop_refl (CHead c (Bind Abst) t)) (THead (Bind Abst) (lift (S O) O t) (lift 
(S (S O)) O t))))))) (\lambda (n0: nat).(\lambda (H1: (ty3 g c (THead (Bind 
Abst) t (THead (Bind Abst) (THead (Bind Abst) (lift (S O) O t) (lift (S (S 
O)) O t)) (church_body n0))) (THead (Bind Abst) t (THead (Bind Abst) (THead 
(Bind Abst) (lift (S O) O t) (lift (S (S O)) O t)) (lift (S (S O)) O 
t))))).(let H_x \def (ty3_gen_abst_abst g c t (THead (Bind Abst) (THead (Bind 
Abst) (lift (S O) O t) (lift (S (S O)) O t)) (church_body n0)) (THead (Bind 
Abst) (THead (Bind Abst) (lift (S O) O t) (lift (S (S O)) O t)) (lift (S (S 
O)) O t)) H1) in (let H2 \def H_x in (ex2_ind T (\lambda (w: T).(ty3 g c t 
w)) (\lambda (_: T).(ty3 g (CHead c (Bind Abst) t) (THead (Bind Abst) (THead 
(Bind Abst) (lift (S O) O t) (lift (S (S O)) O t)) (church_body n0)) (THead 
(Bind Abst) (THead (Bind Abst) (lift (S O) O t) (lift (S (S O)) O t)) (lift 
(S (S O)) O t)))) (ty3 g c (THead (Bind Abst) t (THead (Bind Abst) (THead 
(Bind Abst) (lift (S O) O t) (lift (S (S O)) O t)) (THead (Flat Appl) 
(church_body n0) (TLRef O)))) (THead (Bind Abst) t (THead (Bind Abst) (THead 
(Bind Abst) (lift (S O) O t) (lift (S (S O)) O t)) (lift (S (S O)) O t)))) 
(\lambda (x0: T).(\lambda (_: (ty3 g c t x0)).(\lambda (H4: (ty3 g (CHead c 
(Bind Abst) t) (THead (Bind Abst) (THead (Bind Abst) (lift (S O) O t) (lift 
(S (S O)) O t)) (church_body n0)) (THead (Bind Abst) (THead (Bind Abst) (lift 
(S O) O t) (lift (S (S O)) O t)) (lift (S (S O)) O t)))).(let H_x0 \def 
(ty3_gen_abst_abst g (CHead c (Bind Abst) t) (THead (Bind Abst) (lift (S O) O 
t) (lift (S (S O)) O t)) (church_body n0) (lift (S (S O)) O t) H4) in (let H5 
\def H_x0 in (ex2_ind T (\lambda (w: T).(ty3 g (CHead c (Bind Abst) t) (THead 
(Bind Abst) (lift (S O) O t) (lift (S (S O)) O t)) w)) (\lambda (_: T).(ty3 g 
(CHead (CHead c (Bind Abst) t) (Bind Abst) (THead (Bind Abst) (lift (S O) O 
t) (lift (S (S O)) O t))) (church_body n0) (lift (S (S O)) O t))) (ty3 g c 
(THead (Bind Abst) t (THead (Bind Abst) (THead (Bind Abst) (lift (S O) O t) 
(lift (S (S O)) O t)) (THead (Flat Appl) (church_body n0) (TLRef O)))) (THead 
(Bind Abst) t (THead (Bind Abst) (THead (Bind Abst) (lift (S O) O t) (lift (S 
(S O)) O t)) (lift (S (S O)) O t)))) (\lambda (x1: T).(\lambda (H6: (ty3 g 
(CHead c (Bind Abst) t) (THead (Bind Abst) (lift (S O) O t) (lift (S (S O)) O 
t)) x1)).(\lambda (H7: (ty3 g (CHead (CHead c (Bind Abst) t) (Bind Abst) 
(THead (Bind Abst) (lift (S O) O t) (lift (S (S O)) O t))) (church_body n0) 
(lift (S (S O)) O t))).(ty3_bind g c t u H Abst (THead (Bind Abst) (THead 
(Bind Abst) (lift (S O) O t) (lift (S (S O)) O t)) (THead (Flat Appl) 
(church_body n0) (TLRef O))) (THead (Bind Abst) (THead (Bind Abst) (lift (S 
O) O t) (lift (S (S O)) O t)) (lift (S (S O)) O t)) (ty3_bind g (CHead c 
(Bind Abst) t) (THead (Bind Abst) (lift (S O) O t) (lift (S (S O)) O t)) 
(THead (Bind Abst) (lift (S O) O t) (lift (S (S O)) O u)) (ty3_bind g (CHead 
c (Bind Abst) t) (lift (S O) O t) (lift (S O) O u) (ty3_lift g c t u H (CHead 
c (Bind Abst) t) O (S O) (drop_drop (Bind Abst) O c c (drop_refl c) t)) Abst 
(lift (S (S O)) O t) (lift (S (S O)) O u) (ty3_lift g c t u H (CHead (CHead c 
(Bind Abst) t) (Bind Abst) (lift (S O) O t)) O (S (S O)) (drop_S Abst (CHead 
(CHead c (Bind Abst) t) (Bind Abst) (lift (S O) O t)) c t (S O) (drop_drop 
(Bind Abst) O (CHead c (Bind Abst) t) (CHead c (Bind Abst) t) (drop_refl 
(CHead c (Bind Abst) t)) (lift (S O) O t)))) (lift (S (S O)) O x) (ty3_lift g 
c u x H0 (CHead (CHead c (Bind Abst) t) (Bind Abst) (lift (S O) O t)) O (S (S 
O)) (drop_S Abst (CHead (CHead c (Bind Abst) t) (Bind Abst) (lift (S O) O t)) 
c t (S O) (drop_drop (Bind Abst) O (CHead c (Bind Abst) t) (CHead c (Bind 
Abst) t) (drop_refl (CHead c (Bind Abst) t)) (lift (S O) O t))))) Abst (THead 
(Flat Appl) (church_body n0) (TLRef O)) (lift (S (S O)) O t) (ex_ind T 
(\lambda (t0: T).(ty3 g (CHead (CHead c (Bind Abst) t) (Bind Abst) (THead 
(Bind Abst) (lift (S O) O t) (lift (S (S O)) O t))) (lift (S (S O)) O t) t0)) 
(ty3 g (CHead (CHead c (Bind Abst) t) (Bind Abst) (THead (Bind Abst) (lift (S 
O) O t) (lift (S (S O)) O t))) (THead (Flat Appl) (church_body n0) (TLRef O)) 
(lift (S (S O)) O t)) (\lambda (x2: T).(\lambda (H8: (ty3 g (CHead (CHead c 
(Bind Abst) t) (Bind Abst) (THead (Bind Abst) (lift (S O) O t) (lift (S (S 
O)) O t))) (lift (S (S O)) O t) x2)).(ty3_conv g (CHead (CHead c (Bind Abst) 
t) (Bind Abst) (THead (Bind Abst) (lift (S O) O t) (lift (S (S O)) O t))) 
(lift (S (S O)) O t) x2 H8 (THead (Flat Appl) (church_body n0) (TLRef O)) 
(THead (Flat Appl) (church_body n0) (THead (Bind Abst) (lift (S (S O)) O t) 
(lift (S O) (S O) (lift (S O) O (lift (S O) O t))))) (ty3_appl g (CHead 
(CHead c (Bind Abst) t) (Bind Abst) (THead (Bind Abst) (lift (S O) O t) (lift 
(S (S O)) O t))) (church_body n0) (lift (S (S O)) O t) H7 (TLRef O) (lift (S 
O) (S O) (lift (S O) O (lift (S O) O t))) (eq_ind_r T (lift (S O) O (lift (S 
O) O t)) (\lambda (t0: T).(ty3 g (CHead (CHead c (Bind Abst) t) (Bind Abst) 
(THead (Bind Abst) (lift (S O) O t) t0)) (TLRef O) (THead (Bind Abst) t0 
(lift (S O) (S O) (lift (S O) O (lift (S O) O t)))))) (let H9 \def (eq_ind T 
(lift (S (S O)) O t) (\lambda (t0: T).(ty3 g (CHead c (Bind Abst) t) (THead 
(Bind Abst) (lift (S O) O t) t0) x1)) H6 (lift (S O) O (lift (S O) O t)) 
(pnat_props__lift_SSO_O t)) in (eq_ind T (lift (S O) O (THead (Bind Abst) 
(lift (S O) O t) (lift (S O) O (lift (S O) O t)))) (\lambda (t0: T).(ty3 g 
(CHead (CHead c (Bind Abst) t) (Bind Abst) (THead (Bind Abst) (lift (S O) O 
t) (lift (S O) O (lift (S O) O t)))) (TLRef O) t0)) (ty3_abst g O (CHead 
(CHead c (Bind Abst) t) (Bind Abst) (THead (Bind Abst) (lift (S O) O t) (lift 
(S O) O (lift (S O) O t)))) (CHead c (Bind Abst) t) (THead (Bind Abst) (lift 
(S O) O t) (lift (S O) O (lift (S O) O t))) (getl_refl Abst (CHead c (Bind 
Abst) t) (THead (Bind Abst) (lift (S O) O t) (lift (S O) O (lift (S O) O 
t)))) x1 H9) (THead (Bind Abst) (lift (S O) O (lift (S O) O t)) (lift (S O) 
(S O) (lift (S O) O (lift (S O) O t)))) (lift_bind Abst (lift (S O) O t) 
(lift (S O) O (lift (S O) O t)) (S O) O))) (lift (S (S O)) O t) 
(pnat_props__lift_SSO_O t))) (eq_ind_r T (lift (S O) O (lift (S O) O (lift (S 
O) O t))) (\lambda (t0: T).(pc3 (CHead (CHead c (Bind Abst) t) (Bind Abst) 
(THead (Bind Abst) (lift (S O) O t) (lift (S (S O)) O t))) (THead (Flat Appl) 
(church_body n0) (THead (Bind Abst) (lift (S (S O)) O t) t0)) (lift (S (S O)) 
O t))) (eq_ind_r T (lift (S O) O (lift (S O) O t)) (\lambda (t0: T).(pc3 
(CHead (CHead c (Bind Abst) t) (Bind Abst) (THead (Bind Abst) (lift (S O) O 
t) t0)) (THead (Flat Appl) (church_body n0) (THead (Bind Abst) t0 (lift (S O) 
O (lift (S O) O (lift (S O) O t))))) t0)) (pc3_pr3_r (CHead (CHead c (Bind 
Abst) t) (Bind Abst) (THead (Bind Abst) (lift (S O) O t) (lift (S O) O (lift 
(S O) O t)))) (THead (Flat Appl) (church_body n0) (THead (Bind Abst) (lift (S 
O) O (lift (S O) O t)) (lift (S O) O (lift (S O) O (lift (S O) O t))))) (lift 
(S O) O (lift (S O) O t)) (pr3_t (THead (Bind Abbr) (church_body n0) (lift (S 
O) O (lift (S O) O (lift (S O) O t)))) (THead (Flat Appl) (church_body n0) 
(THead (Bind Abst) (lift (S O) O (lift (S O) O t)) (lift (S O) O (lift (S O) 
O (lift (S O) O t))))) (CHead (CHead c (Bind Abst) t) (Bind Abst) (THead 
(Bind Abst) (lift (S O) O t) (lift (S O) O (lift (S O) O t)))) (pr3_pr2 
(CHead (CHead c (Bind Abst) t) (Bind Abst) (THead (Bind Abst) (lift (S O) O 
t) (lift (S O) O (lift (S O) O t)))) (THead (Flat Appl) (church_body n0) 
(THead (Bind Abst) (lift (S O) O (lift (S O) O t)) (lift (S O) O (lift (S O) 
O (lift (S O) O t))))) (THead (Bind Abbr) (church_body n0) (lift (S O) O 
(lift (S O) O (lift (S O) O t)))) (pr2_free (CHead (CHead c (Bind Abst) t) 
(Bind Abst) (THead (Bind Abst) (lift (S O) O t) (lift (S O) O (lift (S O) O 
t)))) (THead (Flat Appl) (church_body n0) (THead (Bind Abst) (lift (S O) O 
(lift (S O) O t)) (lift (S O) O (lift (S O) O (lift (S O) O t))))) (THead 
(Bind Abbr) (church_body n0) (lift (S O) O (lift (S O) O (lift (S O) O t)))) 
(pr0_beta (lift (S O) O (lift (S O) O t)) (church_body n0) (church_body n0) 
(pr0_refl (church_body n0)) (lift (S O) O (lift (S O) O (lift (S O) O t))) 
(lift (S O) O (lift (S O) O (lift (S O) O t))) (pr0_refl (lift (S O) O (lift 
(S O) O (lift (S O) O t))))))) (lift (S O) O (lift (S O) O t)) (pr3_pr2 
(CHead (CHead c (Bind Abst) t) (Bind Abst) (THead (Bind Abst) (lift (S O) O 
t) (lift (S O) O (lift (S O) O t)))) (THead (Bind Abbr) (church_body n0) 
(lift (S O) O (lift (S O) O (lift (S O) O t)))) (lift (S O) O (lift (S O) O 
t)) (pr2_free (CHead (CHead c (Bind Abst) t) (Bind Abst) (THead (Bind Abst) 
(lift (S O) O t) (lift (S O) O (lift (S O) O t)))) (THead (Bind Abbr) 
(church_body n0) (lift (S O) O (lift (S O) O (lift (S O) O t)))) (lift (S O) 
O (lift (S O) O t)) (pr0_zeta Abbr not_abbr_abst (lift (S O) O (lift (S O) O 
t)) (lift (S O) O (lift (S O) O t)) (pr0_refl (lift (S O) O (lift (S O) O 
t))) (church_body n0)))))) (lift (S (S O)) O t) (pnat_props__lift_SSO_O t)) 
(lift (S O) (S O) (lift (S O) O (lift (S O) O t))) (pnat_props__lift_SO_SO 
(lift (S O) O t)))))) (ty3_correct g (CHead (CHead c (Bind Abst) t) (Bind 
Abst) (THead (Bind Abst) (lift (S O) O t) (lift (S (S O)) O t))) (church_body 
n0) (lift (S (S O)) O t) H7)) (lift (S (S O)) O u) (ty3_lift g c t u H (CHead 
(CHead c (Bind Abst) t) (Bind Abst) (THead (Bind Abst) (lift (S O) O t) (lift 
(S (S O)) O t))) O (S (S O)) (drop_S Abst (CHead (CHead c (Bind Abst) t) 
(Bind Abst) (THead (Bind Abst) (lift (S O) O t) (lift (S (S O)) O t))) c t (S 
O) (drop_drop (Bind Abst) O (CHead c (Bind Abst) t) (CHead c (Bind Abst) t) 
(drop_refl (CHead c (Bind Abst) t)) (THead (Bind Abst) (lift (S O) O t) (lift 
(S (S O)) O t)))))) (THead (Bind Abst) (THead (Bind Abst) (lift (S O) O t) 
(lift (S (S O)) O t)) (lift (S (S O)) O u)) (ty3_bind g (CHead c (Bind Abst) 
t) (THead (Bind Abst) (lift (S O) O t) (lift (S (S O)) O t)) (THead (Bind 
Abst) (lift (S O) O t) (lift (S (S O)) O u)) (ty3_bind g (CHead c (Bind Abst) 
t) (lift (S O) O t) (lift (S O) O u) (ty3_lift g c t u H (CHead c (Bind Abst) 
t) O (S O) (drop_drop (Bind Abst) O c c (drop_refl c) t)) Abst (lift (S (S 
O)) O t) (lift (S (S O)) O u) (ty3_lift g c t u H (CHead (CHead c (Bind Abst) 
t) (Bind Abst) (lift (S O) O t)) O (S (S O)) (drop_S Abst (CHead (CHead c 
(Bind Abst) t) (Bind Abst) (lift (S O) O t)) c t (S O) (drop_drop (Bind Abst) 
O (CHead c (Bind Abst) t) (CHead c (Bind Abst) t) (drop_refl (CHead c (Bind 
Abst) t)) (lift (S O) O t)))) (lift (S (S O)) O x) (ty3_lift g c u x H0 
(CHead (CHead c (Bind Abst) t) (Bind Abst) (lift (S O) O t)) O (S (S O)) 
(drop_S Abst (CHead (CHead c (Bind Abst) t) (Bind Abst) (lift (S O) O t)) c t 
(S O) (drop_drop (Bind Abst) O (CHead c (Bind Abst) t) (CHead c (Bind Abst) 
t) (drop_refl (CHead c (Bind Abst) t)) (lift (S O) O t))))) Abst (lift (S (S 
O)) O t) (lift (S (S O)) O u) (ty3_lift g c t u H (CHead (CHead c (Bind Abst) 
t) (Bind Abst) (THead (Bind Abst) (lift (S O) O t) (lift (S (S O)) O t))) O 
(S (S O)) (drop_S Abst (CHead (CHead c (Bind Abst) t) (Bind Abst) (THead 
(Bind Abst) (lift (S O) O t) (lift (S (S O)) O t))) c t (S O) (drop_drop 
(Bind Abst) O (CHead c (Bind Abst) t) (CHead c (Bind Abst) t) (drop_refl 
(CHead c (Bind Abst) t)) (THead (Bind Abst) (lift (S O) O t) (lift (S (S O)) 
O t))))) (lift (S (S O)) O x) (ty3_lift g c u x H0 (CHead (CHead c (Bind 
Abst) t) (Bind Abst) (THead (Bind Abst) (lift (S O) O t) (lift (S (S O)) O 
t))) O (S (S O)) (drop_S Abst (CHead (CHead c (Bind Abst) t) (Bind Abst) 
(THead (Bind Abst) (lift (S O) O t) (lift (S (S O)) O t))) c t (S O) 
(drop_drop (Bind Abst) O (CHead c (Bind Abst) t) (CHead c (Bind Abst) t) 
(drop_refl (CHead c (Bind Abst) t)) (THead (Bind Abst) (lift (S O) O t) (lift 
(S (S O)) O t)))))))))) H5)))))) H2))))) n)))) (ty3_correct g c t u H)))))).

