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



include "iso/defs.ma".

include "tlist/defs.ma".

theorem iso_flats_lref_bind_false:
 \forall (f: F).(\forall (b: B).(\forall (i: nat).(\forall (v: T).(\forall 
(t: T).(\forall (vs: TList).((iso (THeads (Flat f) vs (TLRef i)) (THead (Bind 
b) v t)) \to (\forall (P: Prop).P)))))))
\def
 \lambda (f: F).(\lambda (b: B).(\lambda (i: nat).(\lambda (v: T).(\lambda 
(t: T).(\lambda (vs: TList).(TList_ind (\lambda (t0: TList).((iso (THeads 
(Flat f) t0 (TLRef i)) (THead (Bind b) v t)) \to (\forall (P: Prop).P))) 
(\lambda (H: (iso (TLRef i) (THead (Bind b) v t))).(\lambda (P: Prop).(let H0 
\def (match H in iso return (\lambda (t0: T).(\lambda (t1: T).(\lambda (_: 
(iso t0 t1)).((eq T t0 (TLRef i)) \to ((eq T t1 (THead (Bind b) v t)) \to 
P))))) with [(iso_sort n1 n2) \Rightarrow (\lambda (H0: (eq T (TSort n1) 
(TLRef i))).(\lambda (H1: (eq T (TSort n2) (THead (Bind b) v t))).((let H2 
\def (eq_ind T (TSort n1) (\lambda (e: T).(match e in T return (\lambda (_: 
T).Prop) with [(TSort _) \Rightarrow True | (TLRef _) \Rightarrow False | 
(THead _ _ _) \Rightarrow False])) I (TLRef i) H0) in (False_ind ((eq T 
(TSort n2) (THead (Bind b) v t)) \to P) H2)) H1))) | (iso_lref i1 i2) 
\Rightarrow (\lambda (H0: (eq T (TLRef i1) (TLRef i))).(\lambda (H1: (eq T 
(TLRef i2) (THead (Bind b) v t))).((let H2 \def (f_equal T nat (\lambda (e: 
T).(match e in T return (\lambda (_: T).nat) with [(TSort _) \Rightarrow i1 | 
(TLRef n) \Rightarrow n | (THead _ _ _) \Rightarrow i1])) (TLRef i1) (TLRef 
i) H0) in (eq_ind nat i (\lambda (_: nat).((eq T (TLRef i2) (THead (Bind b) v 
t)) \to P)) (\lambda (H3: (eq T (TLRef i2) (THead (Bind b) v t))).(let H4 
\def (eq_ind T (TLRef i2) (\lambda (e: T).(match e in T return (\lambda (_: 
T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow True | 
(THead _ _ _) \Rightarrow False])) I (THead (Bind b) v t) H3) in (False_ind P 
H4))) i1 (sym_eq nat i1 i H2))) H1))) | (iso_head v1 v2 t1 t2 k) \Rightarrow 
(\lambda (H0: (eq T (THead k v1 t1) (TLRef i))).(\lambda (H1: (eq T (THead k 
v2 t2) (THead (Bind b) v t))).((let H2 \def (eq_ind T (THead k v1 t1) 
(\lambda (e: T).(match e in T return (\lambda (_: T).Prop) with [(TSort _) 
\Rightarrow False | (TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow 
True])) I (TLRef i) H0) in (False_ind ((eq T (THead k v2 t2) (THead (Bind b) 
v t)) \to P) H2)) H1)))]) in (H0 (refl_equal T (TLRef i)) (refl_equal T 
(THead (Bind b) v t)))))) (\lambda (t0: T).(\lambda (t1: TList).(\lambda (_: 
(((iso (THeads (Flat f) t1 (TLRef i)) (THead (Bind b) v t)) \to (\forall (P: 
Prop).P)))).(\lambda (H0: (iso (THead (Flat f) t0 (THeads (Flat f) t1 (TLRef 
i))) (THead (Bind b) v t))).(\lambda (P: Prop).(let H1 \def (match H0 in iso 
return (\lambda (t2: T).(\lambda (t3: T).(\lambda (_: (iso t2 t3)).((eq T t2 
(THead (Flat f) t0 (THeads (Flat f) t1 (TLRef i)))) \to ((eq T t3 (THead 
(Bind b) v t)) \to P))))) with [(iso_sort n1 n2) \Rightarrow (\lambda (H1: 
(eq T (TSort n1) (THead (Flat f) t0 (THeads (Flat f) t1 (TLRef 
i))))).(\lambda (H2: (eq T (TSort n2) (THead (Bind b) v t))).((let H3 \def 
(eq_ind T (TSort n1) (\lambda (e: T).(match e in T return (\lambda (_: 
T).Prop) with [(TSort _) \Rightarrow True | (TLRef _) \Rightarrow False | 
(THead _ _ _) \Rightarrow False])) I (THead (Flat f) t0 (THeads (Flat f) t1 
(TLRef i))) H1) in (False_ind ((eq T (TSort n2) (THead (Bind b) v t)) \to P) 
H3)) H2))) | (iso_lref i1 i2) \Rightarrow (\lambda (H1: (eq T (TLRef i1) 
(THead (Flat f) t0 (THeads (Flat f) t1 (TLRef i))))).(\lambda (H2: (eq T 
(TLRef i2) (THead (Bind b) v t))).((let H3 \def (eq_ind T (TLRef i1) (\lambda 
(e: T).(match e in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow 
False | (TLRef _) \Rightarrow True | (THead _ _ _) \Rightarrow False])) I 
(THead (Flat f) t0 (THeads (Flat f) t1 (TLRef i))) H1) in (False_ind ((eq T 
(TLRef i2) (THead (Bind b) v t)) \to P) H3)) H2))) | (iso_head v1 v2 t2 t3 k) 
\Rightarrow (\lambda (H1: (eq T (THead k v1 t2) (THead (Flat f) t0 (THeads 
(Flat f) t1 (TLRef i))))).(\lambda (H2: (eq T (THead k v2 t3) (THead (Bind b) 
v t))).((let H3 \def (f_equal T T (\lambda (e: T).(match e in T return 
(\lambda (_: T).T) with [(TSort _) \Rightarrow t2 | (TLRef _) \Rightarrow t2 
| (THead _ _ t4) \Rightarrow t4])) (THead k v1 t2) (THead (Flat f) t0 (THeads 
(Flat f) t1 (TLRef i))) H1) in ((let H4 \def (f_equal T T (\lambda (e: 
T).(match e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow v1 | 
(TLRef _) \Rightarrow v1 | (THead _ t4 _) \Rightarrow t4])) (THead k v1 t2) 
(THead (Flat f) t0 (THeads (Flat f) t1 (TLRef i))) H1) in ((let H5 \def 
(f_equal T K (\lambda (e: T).(match e in T return (\lambda (_: T).K) with 
[(TSort _) \Rightarrow k | (TLRef _) \Rightarrow k | (THead k0 _ _) 
\Rightarrow k0])) (THead k v1 t2) (THead (Flat f) t0 (THeads (Flat f) t1 
(TLRef i))) H1) in (eq_ind K (Flat f) (\lambda (k0: K).((eq T v1 t0) \to ((eq 
T t2 (THeads (Flat f) t1 (TLRef i))) \to ((eq T (THead k0 v2 t3) (THead (Bind 
b) v t)) \to P)))) (\lambda (H6: (eq T v1 t0)).(eq_ind T t0 (\lambda (_: 
T).((eq T t2 (THeads (Flat f) t1 (TLRef i))) \to ((eq T (THead (Flat f) v2 
t3) (THead (Bind b) v t)) \to P))) (\lambda (H7: (eq T t2 (THeads (Flat f) t1 
(TLRef i)))).(eq_ind T (THeads (Flat f) t1 (TLRef i)) (\lambda (_: T).((eq T 
(THead (Flat f) v2 t3) (THead (Bind b) v t)) \to P)) (\lambda (H8: (eq T 
(THead (Flat f) v2 t3) (THead (Bind b) v t))).(let H9 \def (eq_ind T (THead 
(Flat f) v2 t3) (\lambda (e: T).(match e in T return (\lambda (_: T).Prop) 
with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | (THead k0 _ 
_) \Rightarrow (match k0 in K return (\lambda (_: K).Prop) with [(Bind _) 
\Rightarrow False | (Flat _) \Rightarrow True])])) I (THead (Bind b) v t) H8) 
in (False_ind P H9))) t2 (sym_eq T t2 (THeads (Flat f) t1 (TLRef i)) H7))) v1 
(sym_eq T v1 t0 H6))) k (sym_eq K k (Flat f) H5))) H4)) H3)) H2)))]) in (H1 
(refl_equal T (THead (Flat f) t0 (THeads (Flat f) t1 (TLRef i)))) (refl_equal 
T (THead (Bind b) v t))))))))) vs)))))).

theorem iso_flats_flat_bind_false:
 \forall (f1: F).(\forall (f2: F).(\forall (b: B).(\forall (v: T).(\forall 
(v2: T).(\forall (t: T).(\forall (t2: T).(\forall (vs: TList).((iso (THeads 
(Flat f1) vs (THead (Flat f2) v2 t2)) (THead (Bind b) v t)) \to (\forall (P: 
Prop).P)))))))))
\def
 \lambda (f1: F).(\lambda (f2: F).(\lambda (b: B).(\lambda (v: T).(\lambda 
(v2: T).(\lambda (t: T).(\lambda (t2: T).(\lambda (vs: TList).(TList_ind 
(\lambda (t0: TList).((iso (THeads (Flat f1) t0 (THead (Flat f2) v2 t2)) 
(THead (Bind b) v t)) \to (\forall (P: Prop).P))) (\lambda (H: (iso (THead 
(Flat f2) v2 t2) (THead (Bind b) v t))).(\lambda (P: Prop).(let H0 \def 
(match H in iso return (\lambda (t0: T).(\lambda (t1: T).(\lambda (_: (iso t0 
t1)).((eq T t0 (THead (Flat f2) v2 t2)) \to ((eq T t1 (THead (Bind b) v t)) 
\to P))))) with [(iso_sort n1 n2) \Rightarrow (\lambda (H0: (eq T (TSort n1) 
(THead (Flat f2) v2 t2))).(\lambda (H1: (eq T (TSort n2) (THead (Bind b) v 
t))).((let H2 \def (eq_ind T (TSort n1) (\lambda (e: T).(match e in T return 
(\lambda (_: T).Prop) with [(TSort _) \Rightarrow True | (TLRef _) 
\Rightarrow False | (THead _ _ _) \Rightarrow False])) I (THead (Flat f2) v2 
t2) H0) in (False_ind ((eq T (TSort n2) (THead (Bind b) v t)) \to P) H2)) 
H1))) | (iso_lref i1 i2) \Rightarrow (\lambda (H0: (eq T (TLRef i1) (THead 
(Flat f2) v2 t2))).(\lambda (H1: (eq T (TLRef i2) (THead (Bind b) v 
t))).((let H2 \def (eq_ind T (TLRef i1) (\lambda (e: T).(match e in T return 
(\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow True | (THead _ _ _) \Rightarrow False])) I (THead (Flat f2) v2 
t2) H0) in (False_ind ((eq T (TLRef i2) (THead (Bind b) v t)) \to P) H2)) 
H1))) | (iso_head v1 v0 t1 t0 k) \Rightarrow (\lambda (H0: (eq T (THead k v1 
t1) (THead (Flat f2) v2 t2))).(\lambda (H1: (eq T (THead k v0 t0) (THead 
(Bind b) v t))).((let H2 \def (f_equal T T (\lambda (e: T).(match e in T 
return (\lambda (_: T).T) with [(TSort _) \Rightarrow t1 | (TLRef _) 
\Rightarrow t1 | (THead _ _ t3) \Rightarrow t3])) (THead k v1 t1) (THead 
(Flat f2) v2 t2) H0) in ((let H3 \def (f_equal T T (\lambda (e: T).(match e 
in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow v1 | (TLRef _) 
\Rightarrow v1 | (THead _ t3 _) \Rightarrow t3])) (THead k v1 t1) (THead 
(Flat f2) v2 t2) H0) in ((let H4 \def (f_equal T K (\lambda (e: T).(match e 
in T return (\lambda (_: T).K) with [(TSort _) \Rightarrow k | (TLRef _) 
\Rightarrow k | (THead k0 _ _) \Rightarrow k0])) (THead k v1 t1) (THead (Flat 
f2) v2 t2) H0) in (eq_ind K (Flat f2) (\lambda (k0: K).((eq T v1 v2) \to ((eq 
T t1 t2) \to ((eq T (THead k0 v0 t0) (THead (Bind b) v t)) \to P)))) (\lambda 
(H5: (eq T v1 v2)).(eq_ind T v2 (\lambda (_: T).((eq T t1 t2) \to ((eq T 
(THead (Flat f2) v0 t0) (THead (Bind b) v t)) \to P))) (\lambda (H6: (eq T t1 
t2)).(eq_ind T t2 (\lambda (_: T).((eq T (THead (Flat f2) v0 t0) (THead (Bind 
b) v t)) \to P)) (\lambda (H7: (eq T (THead (Flat f2) v0 t0) (THead (Bind b) 
v t))).(let H8 \def (eq_ind T (THead (Flat f2) v0 t0) (\lambda (e: T).(match 
e in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | 
(TLRef _) \Rightarrow False | (THead k0 _ _) \Rightarrow (match k0 in K 
return (\lambda (_: K).Prop) with [(Bind _) \Rightarrow False | (Flat _) 
\Rightarrow True])])) I (THead (Bind b) v t) H7) in (False_ind P H8))) t1 
(sym_eq T t1 t2 H6))) v1 (sym_eq T v1 v2 H5))) k (sym_eq K k (Flat f2) H4))) 
H3)) H2)) H1)))]) in (H0 (refl_equal T (THead (Flat f2) v2 t2)) (refl_equal T 
(THead (Bind b) v t)))))) (\lambda (t0: T).(\lambda (t1: TList).(\lambda (_: 
(((iso (THeads (Flat f1) t1 (THead (Flat f2) v2 t2)) (THead (Bind b) v t)) 
\to (\forall (P: Prop).P)))).(\lambda (H0: (iso (THead (Flat f1) t0 (THeads 
(Flat f1) t1 (THead (Flat f2) v2 t2))) (THead (Bind b) v t))).(\lambda (P: 
Prop).(let H1 \def (match H0 in iso return (\lambda (t3: T).(\lambda (t4: 
T).(\lambda (_: (iso t3 t4)).((eq T t3 (THead (Flat f1) t0 (THeads (Flat f1) 
t1 (THead (Flat f2) v2 t2)))) \to ((eq T t4 (THead (Bind b) v t)) \to P))))) 
with [(iso_sort n1 n2) \Rightarrow (\lambda (H1: (eq T (TSort n1) (THead 
(Flat f1) t0 (THeads (Flat f1) t1 (THead (Flat f2) v2 t2))))).(\lambda (H2: 
(eq T (TSort n2) (THead (Bind b) v t))).((let H3 \def (eq_ind T (TSort n1) 
(\lambda (e: T).(match e in T return (\lambda (_: T).Prop) with [(TSort _) 
\Rightarrow True | (TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow 
False])) I (THead (Flat f1) t0 (THeads (Flat f1) t1 (THead (Flat f2) v2 t2))) 
H1) in (False_ind ((eq T (TSort n2) (THead (Bind b) v t)) \to P) H3)) H2))) | 
(iso_lref i1 i2) \Rightarrow (\lambda (H1: (eq T (TLRef i1) (THead (Flat f1) 
t0 (THeads (Flat f1) t1 (THead (Flat f2) v2 t2))))).(\lambda (H2: (eq T 
(TLRef i2) (THead (Bind b) v t))).((let H3 \def (eq_ind T (TLRef i1) (\lambda 
(e: T).(match e in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow 
False | (TLRef _) \Rightarrow True | (THead _ _ _) \Rightarrow False])) I 
(THead (Flat f1) t0 (THeads (Flat f1) t1 (THead (Flat f2) v2 t2))) H1) in 
(False_ind ((eq T (TLRef i2) (THead (Bind b) v t)) \to P) H3)) H2))) | 
(iso_head v1 v0 t3 t4 k) \Rightarrow (\lambda (H1: (eq T (THead k v1 t3) 
(THead (Flat f1) t0 (THeads (Flat f1) t1 (THead (Flat f2) v2 t2))))).(\lambda 
(H2: (eq T (THead k v0 t4) (THead (Bind b) v t))).((let H3 \def (f_equal T T 
(\lambda (e: T).(match e in T return (\lambda (_: T).T) with [(TSort _) 
\Rightarrow t3 | (TLRef _) \Rightarrow t3 | (THead _ _ t5) \Rightarrow t5])) 
(THead k v1 t3) (THead (Flat f1) t0 (THeads (Flat f1) t1 (THead (Flat f2) v2 
t2))) H1) in ((let H4 \def (f_equal T T (\lambda (e: T).(match e in T return 
(\lambda (_: T).T) with [(TSort _) \Rightarrow v1 | (TLRef _) \Rightarrow v1 
| (THead _ t5 _) \Rightarrow t5])) (THead k v1 t3) (THead (Flat f1) t0 
(THeads (Flat f1) t1 (THead (Flat f2) v2 t2))) H1) in ((let H5 \def (f_equal 
T K (\lambda (e: T).(match e in T return (\lambda (_: T).K) with [(TSort _) 
\Rightarrow k | (TLRef _) \Rightarrow k | (THead k0 _ _) \Rightarrow k0])) 
(THead k v1 t3) (THead (Flat f1) t0 (THeads (Flat f1) t1 (THead (Flat f2) v2 
t2))) H1) in (eq_ind K (Flat f1) (\lambda (k0: K).((eq T v1 t0) \to ((eq T t3 
(THeads (Flat f1) t1 (THead (Flat f2) v2 t2))) \to ((eq T (THead k0 v0 t4) 
(THead (Bind b) v t)) \to P)))) (\lambda (H6: (eq T v1 t0)).(eq_ind T t0 
(\lambda (_: T).((eq T t3 (THeads (Flat f1) t1 (THead (Flat f2) v2 t2))) \to 
((eq T (THead (Flat f1) v0 t4) (THead (Bind b) v t)) \to P))) (\lambda (H7: 
(eq T t3 (THeads (Flat f1) t1 (THead (Flat f2) v2 t2)))).(eq_ind T (THeads 
(Flat f1) t1 (THead (Flat f2) v2 t2)) (\lambda (_: T).((eq T (THead (Flat f1) 
v0 t4) (THead (Bind b) v t)) \to P)) (\lambda (H8: (eq T (THead (Flat f1) v0 
t4) (THead (Bind b) v t))).(let H9 \def (eq_ind T (THead (Flat f1) v0 t4) 
(\lambda (e: T).(match e in T return (\lambda (_: T).Prop) with [(TSort _) 
\Rightarrow False | (TLRef _) \Rightarrow False | (THead k0 _ _) \Rightarrow 
(match k0 in K return (\lambda (_: K).Prop) with [(Bind _) \Rightarrow False 
| (Flat _) \Rightarrow True])])) I (THead (Bind b) v t) H8) in (False_ind P 
H9))) t3 (sym_eq T t3 (THeads (Flat f1) t1 (THead (Flat f2) v2 t2)) H7))) v1 
(sym_eq T v1 t0 H6))) k (sym_eq K k (Flat f1) H5))) H4)) H3)) H2)))]) in (H1 
(refl_equal T (THead (Flat f1) t0 (THeads (Flat f1) t1 (THead (Flat f2) v2 
t2)))) (refl_equal T (THead (Bind b) v t))))))))) vs)))))))).

theorem iso_gen_sort:
 \forall (u2: T).(\forall (n1: nat).((iso (TSort n1) u2) \to (ex nat (\lambda 
(n2: nat).(eq T u2 (TSort n2))))))
\def
 \lambda (u2: T).(\lambda (n1: nat).(\lambda (H: (iso (TSort n1) u2)).(let H0 
\def (match H in iso return (\lambda (t: T).(\lambda (t0: T).(\lambda (_: 
(iso t t0)).((eq T t (TSort n1)) \to ((eq T t0 u2) \to (ex nat (\lambda (n2: 
nat).(eq T u2 (TSort n2))))))))) with [(iso_sort n0 n2) \Rightarrow (\lambda 
(H0: (eq T (TSort n0) (TSort n1))).(\lambda (H1: (eq T (TSort n2) u2)).((let 
H2 \def (f_equal T nat (\lambda (e: T).(match e in T return (\lambda (_: 
T).nat) with [(TSort n) \Rightarrow n | (TLRef _) \Rightarrow n0 | (THead _ _ 
_) \Rightarrow n0])) (TSort n0) (TSort n1) H0) in (eq_ind nat n1 (\lambda (_: 
nat).((eq T (TSort n2) u2) \to (ex nat (\lambda (n3: nat).(eq T u2 (TSort 
n3)))))) (\lambda (H3: (eq T (TSort n2) u2)).(eq_ind T (TSort n2) (\lambda 
(t: T).(ex nat (\lambda (n3: nat).(eq T t (TSort n3))))) (ex_intro nat 
(\lambda (n3: nat).(eq T (TSort n2) (TSort n3))) n2 (refl_equal T (TSort 
n2))) u2 H3)) n0 (sym_eq nat n0 n1 H2))) H1))) | (iso_lref i1 i2) \Rightarrow 
(\lambda (H0: (eq T (TLRef i1) (TSort n1))).(\lambda (H1: (eq T (TLRef i2) 
u2)).((let H2 \def (eq_ind T (TLRef i1) (\lambda (e: T).(match e in T return 
(\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow True | (THead _ _ _) \Rightarrow False])) I (TSort n1) H0) in 
(False_ind ((eq T (TLRef i2) u2) \to (ex nat (\lambda (n2: nat).(eq T u2 
(TSort n2))))) H2)) H1))) | (iso_head v1 v2 t1 t2 k) \Rightarrow (\lambda 
(H0: (eq T (THead k v1 t1) (TSort n1))).(\lambda (H1: (eq T (THead k v2 t2) 
u2)).((let H2 \def (eq_ind T (THead k v1 t1) (\lambda (e: T).(match e in T 
return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow False | (THead _ _ _) \Rightarrow True])) I (TSort n1) H0) in 
(False_ind ((eq T (THead k v2 t2) u2) \to (ex nat (\lambda (n2: nat).(eq T u2 
(TSort n2))))) H2)) H1)))]) in (H0 (refl_equal T (TSort n1)) (refl_equal T 
u2))))).

theorem iso_gen_lref:
 \forall (u2: T).(\forall (n1: nat).((iso (TLRef n1) u2) \to (ex nat (\lambda 
(n2: nat).(eq T u2 (TLRef n2))))))
\def
 \lambda (u2: T).(\lambda (n1: nat).(\lambda (H: (iso (TLRef n1) u2)).(let H0 
\def (match H in iso return (\lambda (t: T).(\lambda (t0: T).(\lambda (_: 
(iso t t0)).((eq T t (TLRef n1)) \to ((eq T t0 u2) \to (ex nat (\lambda (n2: 
nat).(eq T u2 (TLRef n2))))))))) with [(iso_sort n0 n2) \Rightarrow (\lambda 
(H0: (eq T (TSort n0) (TLRef n1))).(\lambda (H1: (eq T (TSort n2) u2)).((let 
H2 \def (eq_ind T (TSort n0) (\lambda (e: T).(match e in T return (\lambda 
(_: T).Prop) with [(TSort _) \Rightarrow True | (TLRef _) \Rightarrow False | 
(THead _ _ _) \Rightarrow False])) I (TLRef n1) H0) in (False_ind ((eq T 
(TSort n2) u2) \to (ex nat (\lambda (n3: nat).(eq T u2 (TLRef n3))))) H2)) 
H1))) | (iso_lref i1 i2) \Rightarrow (\lambda (H0: (eq T (TLRef i1) (TLRef 
n1))).(\lambda (H1: (eq T (TLRef i2) u2)).((let H2 \def (f_equal T nat 
(\lambda (e: T).(match e in T return (\lambda (_: T).nat) with [(TSort _) 
\Rightarrow i1 | (TLRef n) \Rightarrow n | (THead _ _ _) \Rightarrow i1])) 
(TLRef i1) (TLRef n1) H0) in (eq_ind nat n1 (\lambda (_: nat).((eq T (TLRef 
i2) u2) \to (ex nat (\lambda (n2: nat).(eq T u2 (TLRef n2)))))) (\lambda (H3: 
(eq T (TLRef i2) u2)).(eq_ind T (TLRef i2) (\lambda (t: T).(ex nat (\lambda 
(n2: nat).(eq T t (TLRef n2))))) (ex_intro nat (\lambda (n2: nat).(eq T 
(TLRef i2) (TLRef n2))) i2 (refl_equal T (TLRef i2))) u2 H3)) i1 (sym_eq nat 
i1 n1 H2))) H1))) | (iso_head v1 v2 t1 t2 k) \Rightarrow (\lambda (H0: (eq T 
(THead k v1 t1) (TLRef n1))).(\lambda (H1: (eq T (THead k v2 t2) u2)).((let 
H2 \def (eq_ind T (THead k v1 t1) (\lambda (e: T).(match e in T return 
(\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow False | (THead _ _ _) \Rightarrow True])) I (TLRef n1) H0) in 
(False_ind ((eq T (THead k v2 t2) u2) \to (ex nat (\lambda (n2: nat).(eq T u2 
(TLRef n2))))) H2)) H1)))]) in (H0 (refl_equal T (TLRef n1)) (refl_equal T 
u2))))).

theorem iso_gen_head:
 \forall (k: K).(\forall (v1: T).(\forall (t1: T).(\forall (u2: T).((iso 
(THead k v1 t1) u2) \to (ex_2 T T (\lambda (v2: T).(\lambda (t2: T).(eq T u2 
(THead k v2 t2)))))))))
\def
 \lambda (k: K).(\lambda (v1: T).(\lambda (t1: T).(\lambda (u2: T).(\lambda 
(H: (iso (THead k v1 t1) u2)).(let H0 \def (match H in iso return (\lambda 
(t: T).(\lambda (t0: T).(\lambda (_: (iso t t0)).((eq T t (THead k v1 t1)) 
\to ((eq T t0 u2) \to (ex_2 T T (\lambda (v2: T).(\lambda (t2: T).(eq T u2 
(THead k v2 t2)))))))))) with [(iso_sort n1 n2) \Rightarrow (\lambda (H0: (eq 
T (TSort n1) (THead k v1 t1))).(\lambda (H1: (eq T (TSort n2) u2)).((let H2 
\def (eq_ind T (TSort n1) (\lambda (e: T).(match e in T return (\lambda (_: 
T).Prop) with [(TSort _) \Rightarrow True | (TLRef _) \Rightarrow False | 
(THead _ _ _) \Rightarrow False])) I (THead k v1 t1) H0) in (False_ind ((eq T 
(TSort n2) u2) \to (ex_2 T T (\lambda (v2: T).(\lambda (t2: T).(eq T u2 
(THead k v2 t2)))))) H2)) H1))) | (iso_lref i1 i2) \Rightarrow (\lambda (H0: 
(eq T (TLRef i1) (THead k v1 t1))).(\lambda (H1: (eq T (TLRef i2) u2)).((let 
H2 \def (eq_ind T (TLRef i1) (\lambda (e: T).(match e in T return (\lambda 
(_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow True | 
(THead _ _ _) \Rightarrow False])) I (THead k v1 t1) H0) in (False_ind ((eq T 
(TLRef i2) u2) \to (ex_2 T T (\lambda (v2: T).(\lambda (t2: T).(eq T u2 
(THead k v2 t2)))))) H2)) H1))) | (iso_head v0 v2 t0 t2 k0) \Rightarrow 
(\lambda (H0: (eq T (THead k0 v0 t0) (THead k v1 t1))).(\lambda (H1: (eq T 
(THead k0 v2 t2) u2)).((let H2 \def (f_equal T T (\lambda (e: T).(match e in 
T return (\lambda (_: T).T) with [(TSort _) \Rightarrow t0 | (TLRef _) 
\Rightarrow t0 | (THead _ _ t) \Rightarrow t])) (THead k0 v0 t0) (THead k v1 
t1) H0) in ((let H3 \def (f_equal T T (\lambda (e: T).(match e in T return 
(\lambda (_: T).T) with [(TSort _) \Rightarrow v0 | (TLRef _) \Rightarrow v0 
| (THead _ t _) \Rightarrow t])) (THead k0 v0 t0) (THead k v1 t1) H0) in 
((let H4 \def (f_equal T K (\lambda (e: T).(match e in T return (\lambda (_: 
T).K) with [(TSort _) \Rightarrow k0 | (TLRef _) \Rightarrow k0 | (THead k1 _ 
_) \Rightarrow k1])) (THead k0 v0 t0) (THead k v1 t1) H0) in (eq_ind K k 
(\lambda (k1: K).((eq T v0 v1) \to ((eq T t0 t1) \to ((eq T (THead k1 v2 t2) 
u2) \to (ex_2 T T (\lambda (v3: T).(\lambda (t3: T).(eq T u2 (THead k v3 
t3))))))))) (\lambda (H5: (eq T v0 v1)).(eq_ind T v1 (\lambda (_: T).((eq T 
t0 t1) \to ((eq T (THead k v2 t2) u2) \to (ex_2 T T (\lambda (v3: T).(\lambda 
(t3: T).(eq T u2 (THead k v3 t3)))))))) (\lambda (H6: (eq T t0 t1)).(eq_ind T 
t1 (\lambda (_: T).((eq T (THead k v2 t2) u2) \to (ex_2 T T (\lambda (v3: 
T).(\lambda (t3: T).(eq T u2 (THead k v3 t3))))))) (\lambda (H7: (eq T (THead 
k v2 t2) u2)).(eq_ind T (THead k v2 t2) (\lambda (t: T).(ex_2 T T (\lambda 
(v3: T).(\lambda (t3: T).(eq T t (THead k v3 t3)))))) (ex_2_intro T T 
(\lambda (v3: T).(\lambda (t3: T).(eq T (THead k v2 t2) (THead k v3 t3)))) v2 
t2 (refl_equal T (THead k v2 t2))) u2 H7)) t0 (sym_eq T t0 t1 H6))) v0 
(sym_eq T v0 v1 H5))) k0 (sym_eq K k0 k H4))) H3)) H2)) H1)))]) in (H0 
(refl_equal T (THead k v1 t1)) (refl_equal T u2))))))).

