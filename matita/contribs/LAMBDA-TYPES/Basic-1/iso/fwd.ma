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

include "Basic-1/iso/defs.ma".

include "Basic-1/tlist/defs.ma".

theorem iso_gen_sort:
 \forall (u2: T).(\forall (n1: nat).((iso (TSort n1) u2) \to (ex nat (\lambda 
(n2: nat).(eq T u2 (TSort n2))))))
\def
 \lambda (u2: T).(\lambda (n1: nat).(\lambda (H: (iso (TSort n1) 
u2)).(insert_eq T (TSort n1) (\lambda (t: T).(iso t u2)) (\lambda (_: T).(ex 
nat (\lambda (n2: nat).(eq T u2 (TSort n2))))) (\lambda (y: T).(\lambda (H0: 
(iso y u2)).(iso_ind (\lambda (t: T).(\lambda (t0: T).((eq T t (TSort n1)) 
\to (ex nat (\lambda (n2: nat).(eq T t0 (TSort n2))))))) (\lambda (n0: 
nat).(\lambda (n2: nat).(\lambda (H1: (eq T (TSort n0) (TSort n1))).(let H2 
\def (f_equal T nat (\lambda (e: T).(match e in T return (\lambda (_: T).nat) 
with [(TSort n) \Rightarrow n | (TLRef _) \Rightarrow n0 | (THead _ _ _) 
\Rightarrow n0])) (TSort n0) (TSort n1) H1) in (ex_intro nat (\lambda (n3: 
nat).(eq T (TSort n2) (TSort n3))) n2 (refl_equal T (TSort n2))))))) (\lambda 
(i1: nat).(\lambda (i2: nat).(\lambda (H1: (eq T (TLRef i1) (TSort n1))).(let 
H2 \def (eq_ind T (TLRef i1) (\lambda (ee: T).(match ee in T return (\lambda 
(_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow True | 
(THead _ _ _) \Rightarrow False])) I (TSort n1) H1) in (False_ind (ex nat 
(\lambda (n2: nat).(eq T (TLRef i2) (TSort n2)))) H2))))) (\lambda (v1: 
T).(\lambda (v2: T).(\lambda (t1: T).(\lambda (t2: T).(\lambda (k: 
K).(\lambda (H1: (eq T (THead k v1 t1) (TSort n1))).(let H2 \def (eq_ind T 
(THead k v1 t1) (\lambda (ee: T).(match ee in T return (\lambda (_: T).Prop) 
with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | (THead _ _ 
_) \Rightarrow True])) I (TSort n1) H1) in (False_ind (ex nat (\lambda (n2: 
nat).(eq T (THead k v2 t2) (TSort n2)))) H2)))))))) y u2 H0))) H))).
(* COMMENTS
Initial nodes: 321
END *)

theorem iso_gen_lref:
 \forall (u2: T).(\forall (n1: nat).((iso (TLRef n1) u2) \to (ex nat (\lambda 
(n2: nat).(eq T u2 (TLRef n2))))))
\def
 \lambda (u2: T).(\lambda (n1: nat).(\lambda (H: (iso (TLRef n1) 
u2)).(insert_eq T (TLRef n1) (\lambda (t: T).(iso t u2)) (\lambda (_: T).(ex 
nat (\lambda (n2: nat).(eq T u2 (TLRef n2))))) (\lambda (y: T).(\lambda (H0: 
(iso y u2)).(iso_ind (\lambda (t: T).(\lambda (t0: T).((eq T t (TLRef n1)) 
\to (ex nat (\lambda (n2: nat).(eq T t0 (TLRef n2))))))) (\lambda (n0: 
nat).(\lambda (n2: nat).(\lambda (H1: (eq T (TSort n0) (TLRef n1))).(let H2 
\def (eq_ind T (TSort n0) (\lambda (ee: T).(match ee in T return (\lambda (_: 
T).Prop) with [(TSort _) \Rightarrow True | (TLRef _) \Rightarrow False | 
(THead _ _ _) \Rightarrow False])) I (TLRef n1) H1) in (False_ind (ex nat 
(\lambda (n3: nat).(eq T (TSort n2) (TLRef n3)))) H2))))) (\lambda (i1: 
nat).(\lambda (i2: nat).(\lambda (H1: (eq T (TLRef i1) (TLRef n1))).(let H2 
\def (f_equal T nat (\lambda (e: T).(match e in T return (\lambda (_: T).nat) 
with [(TSort _) \Rightarrow i1 | (TLRef n) \Rightarrow n | (THead _ _ _) 
\Rightarrow i1])) (TLRef i1) (TLRef n1) H1) in (ex_intro nat (\lambda (n2: 
nat).(eq T (TLRef i2) (TLRef n2))) i2 (refl_equal T (TLRef i2))))))) (\lambda 
(v1: T).(\lambda (v2: T).(\lambda (t1: T).(\lambda (t2: T).(\lambda (k: 
K).(\lambda (H1: (eq T (THead k v1 t1) (TLRef n1))).(let H2 \def (eq_ind T 
(THead k v1 t1) (\lambda (ee: T).(match ee in T return (\lambda (_: T).Prop) 
with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | (THead _ _ 
_) \Rightarrow True])) I (TLRef n1) H1) in (False_ind (ex nat (\lambda (n2: 
nat).(eq T (THead k v2 t2) (TLRef n2)))) H2)))))))) y u2 H0))) H))).
(* COMMENTS
Initial nodes: 321
END *)

theorem iso_gen_head:
 \forall (k: K).(\forall (v1: T).(\forall (t1: T).(\forall (u2: T).((iso 
(THead k v1 t1) u2) \to (ex_2 T T (\lambda (v2: T).(\lambda (t2: T).(eq T u2 
(THead k v2 t2)))))))))
\def
 \lambda (k: K).(\lambda (v1: T).(\lambda (t1: T).(\lambda (u2: T).(\lambda 
(H: (iso (THead k v1 t1) u2)).(insert_eq T (THead k v1 t1) (\lambda (t: 
T).(iso t u2)) (\lambda (_: T).(ex_2 T T (\lambda (v2: T).(\lambda (t2: 
T).(eq T u2 (THead k v2 t2)))))) (\lambda (y: T).(\lambda (H0: (iso y 
u2)).(iso_ind (\lambda (t: T).(\lambda (t0: T).((eq T t (THead k v1 t1)) \to 
(ex_2 T T (\lambda (v2: T).(\lambda (t2: T).(eq T t0 (THead k v2 t2)))))))) 
(\lambda (n1: nat).(\lambda (n2: nat).(\lambda (H1: (eq T (TSort n1) (THead k 
v1 t1))).(let H2 \def (eq_ind T (TSort n1) (\lambda (ee: T).(match ee in T 
return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow True | (TLRef _) 
\Rightarrow False | (THead _ _ _) \Rightarrow False])) I (THead k v1 t1) H1) 
in (False_ind (ex_2 T T (\lambda (v2: T).(\lambda (t2: T).(eq T (TSort n2) 
(THead k v2 t2))))) H2))))) (\lambda (i1: nat).(\lambda (i2: nat).(\lambda 
(H1: (eq T (TLRef i1) (THead k v1 t1))).(let H2 \def (eq_ind T (TLRef i1) 
(\lambda (ee: T).(match ee in T return (\lambda (_: T).Prop) with [(TSort _) 
\Rightarrow False | (TLRef _) \Rightarrow True | (THead _ _ _) \Rightarrow 
False])) I (THead k v1 t1) H1) in (False_ind (ex_2 T T (\lambda (v2: 
T).(\lambda (t2: T).(eq T (TLRef i2) (THead k v2 t2))))) H2))))) (\lambda 
(v0: T).(\lambda (v2: T).(\lambda (t0: T).(\lambda (t2: T).(\lambda (k0: 
K).(\lambda (H1: (eq T (THead k0 v0 t0) (THead k v1 t1))).(let H2 \def 
(f_equal T K (\lambda (e: T).(match e in T return (\lambda (_: T).K) with 
[(TSort _) \Rightarrow k0 | (TLRef _) \Rightarrow k0 | (THead k1 _ _) 
\Rightarrow k1])) (THead k0 v0 t0) (THead k v1 t1) H1) in ((let H3 \def 
(f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) with 
[(TSort _) \Rightarrow v0 | (TLRef _) \Rightarrow v0 | (THead _ t _) 
\Rightarrow t])) (THead k0 v0 t0) (THead k v1 t1) H1) in ((let H4 \def 
(f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) with 
[(TSort _) \Rightarrow t0 | (TLRef _) \Rightarrow t0 | (THead _ _ t) 
\Rightarrow t])) (THead k0 v0 t0) (THead k v1 t1) H1) in (\lambda (_: (eq T 
v0 v1)).(\lambda (H6: (eq K k0 k)).(eq_ind_r K k (\lambda (k1: K).(ex_2 T T 
(\lambda (v3: T).(\lambda (t3: T).(eq T (THead k1 v2 t2) (THead k v3 t3)))))) 
(ex_2_intro T T (\lambda (v3: T).(\lambda (t3: T).(eq T (THead k v2 t2) 
(THead k v3 t3)))) v2 t2 (refl_equal T (THead k v2 t2))) k0 H6)))) H3)) 
H2)))))))) y u2 H0))) H))))).
(* COMMENTS
Initial nodes: 545
END *)

theorem iso_flats_lref_bind_false:
 \forall (f: F).(\forall (b: B).(\forall (i: nat).(\forall (v: T).(\forall 
(t: T).(\forall (vs: TList).((iso (THeads (Flat f) vs (TLRef i)) (THead (Bind 
b) v t)) \to (\forall (P: Prop).P)))))))
\def
 \lambda (f: F).(\lambda (b: B).(\lambda (i: nat).(\lambda (v: T).(\lambda 
(t: T).(\lambda (vs: TList).(TList_ind (\lambda (t0: TList).((iso (THeads 
(Flat f) t0 (TLRef i)) (THead (Bind b) v t)) \to (\forall (P: Prop).P))) 
(\lambda (H: (iso (TLRef i) (THead (Bind b) v t))).(\lambda (P: Prop).(let 
H_x \def (iso_gen_lref (THead (Bind b) v t) i H) in (let H0 \def H_x in 
(ex_ind nat (\lambda (n2: nat).(eq T (THead (Bind b) v t) (TLRef n2))) P 
(\lambda (x: nat).(\lambda (H1: (eq T (THead (Bind b) v t) (TLRef x))).(let 
H2 \def (eq_ind T (THead (Bind b) v t) (\lambda (ee: T).(match ee in T return 
(\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow False | (THead _ _ _) \Rightarrow True])) I (TLRef x) H1) in 
(False_ind P H2)))) H0))))) (\lambda (t0: T).(\lambda (t1: TList).(\lambda 
(_: (((iso (THeads (Flat f) t1 (TLRef i)) (THead (Bind b) v t)) \to (\forall 
(P: Prop).P)))).(\lambda (H0: (iso (THead (Flat f) t0 (THeads (Flat f) t1 
(TLRef i))) (THead (Bind b) v t))).(\lambda (P: Prop).(let H_x \def 
(iso_gen_head (Flat f) t0 (THeads (Flat f) t1 (TLRef i)) (THead (Bind b) v t) 
H0) in (let H1 \def H_x in (ex_2_ind T T (\lambda (v2: T).(\lambda (t2: 
T).(eq T (THead (Bind b) v t) (THead (Flat f) v2 t2)))) P (\lambda (x0: 
T).(\lambda (x1: T).(\lambda (H2: (eq T (THead (Bind b) v t) (THead (Flat f) 
x0 x1))).(let H3 \def (eq_ind T (THead (Bind b) v t) (\lambda (ee: T).(match 
ee in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | 
(TLRef _) \Rightarrow False | (THead k _ _) \Rightarrow (match k in K return 
(\lambda (_: K).Prop) with [(Bind _) \Rightarrow True | (Flat _) \Rightarrow 
False])])) I (THead (Flat f) x0 x1) H2) in (False_ind P H3))))) H1)))))))) 
vs)))))).
(* COMMENTS
Initial nodes: 391
END *)

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
(Flat f2) v2 t2) (THead (Bind b) v t))).(\lambda (P: Prop).(let H_x \def 
(iso_gen_head (Flat f2) v2 t2 (THead (Bind b) v t) H) in (let H0 \def H_x in 
(ex_2_ind T T (\lambda (v3: T).(\lambda (t3: T).(eq T (THead (Bind b) v t) 
(THead (Flat f2) v3 t3)))) P (\lambda (x0: T).(\lambda (x1: T).(\lambda (H1: 
(eq T (THead (Bind b) v t) (THead (Flat f2) x0 x1))).(let H2 \def (eq_ind T 
(THead (Bind b) v t) (\lambda (ee: T).(match ee in T return (\lambda (_: 
T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | 
(THead k _ _) \Rightarrow (match k in K return (\lambda (_: K).Prop) with 
[(Bind _) \Rightarrow True | (Flat _) \Rightarrow False])])) I (THead (Flat 
f2) x0 x1) H1) in (False_ind P H2))))) H0))))) (\lambda (t0: T).(\lambda (t1: 
TList).(\lambda (_: (((iso (THeads (Flat f1) t1 (THead (Flat f2) v2 t2)) 
(THead (Bind b) v t)) \to (\forall (P: Prop).P)))).(\lambda (H0: (iso (THead 
(Flat f1) t0 (THeads (Flat f1) t1 (THead (Flat f2) v2 t2))) (THead (Bind b) v 
t))).(\lambda (P: Prop).(let H_x \def (iso_gen_head (Flat f1) t0 (THeads 
(Flat f1) t1 (THead (Flat f2) v2 t2)) (THead (Bind b) v t) H0) in (let H1 
\def H_x in (ex_2_ind T T (\lambda (v3: T).(\lambda (t3: T).(eq T (THead 
(Bind b) v t) (THead (Flat f1) v3 t3)))) P (\lambda (x0: T).(\lambda (x1: 
T).(\lambda (H2: (eq T (THead (Bind b) v t) (THead (Flat f1) x0 x1))).(let H3 
\def (eq_ind T (THead (Bind b) v t) (\lambda (ee: T).(match ee in T return 
(\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow False | (THead k _ _) \Rightarrow (match k in K return (\lambda 
(_: K).Prop) with [(Bind _) \Rightarrow True | (Flat _) \Rightarrow 
False])])) I (THead (Flat f1) x0 x1) H2) in (False_ind P H3))))) H1)))))))) 
vs)))))))).
(* COMMENTS
Initial nodes: 461
END *)

