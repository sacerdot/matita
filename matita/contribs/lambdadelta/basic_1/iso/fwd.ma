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

include "basic_1/iso/defs.ma".

include "basic_1/tlist/defs.ma".

theorem iso_ind:
 \forall (P: ((T \to (T \to Prop)))).(((\forall (n1: nat).(\forall (n2: 
nat).(P (TSort n1) (TSort n2))))) \to (((\forall (i1: nat).(\forall (i2: 
nat).(P (TLRef i1) (TLRef i2))))) \to (((\forall (v1: T).(\forall (v2: 
T).(\forall (t1: T).(\forall (t2: T).(\forall (k: K).(P (THead k v1 t1) 
(THead k v2 t2)))))))) \to (\forall (t: T).(\forall (t0: T).((iso t t0) \to 
(P t t0)))))))
\def
 \lambda (P: ((T \to (T \to Prop)))).(\lambda (f: ((\forall (n1: 
nat).(\forall (n2: nat).(P (TSort n1) (TSort n2)))))).(\lambda (f0: ((\forall 
(i1: nat).(\forall (i2: nat).(P (TLRef i1) (TLRef i2)))))).(\lambda (f1: 
((\forall (v1: T).(\forall (v2: T).(\forall (t1: T).(\forall (t2: T).(\forall 
(k: K).(P (THead k v1 t1) (THead k v2 t2))))))))).(\lambda (t: T).(\lambda 
(t0: T).(\lambda (i: (iso t t0)).(match i with [(iso_sort x x0) \Rightarrow 
(f x x0) | (iso_lref x x0) \Rightarrow (f0 x x0) | (iso_head x x0 x1 x2 x3) 
\Rightarrow (f1 x x0 x1 x2 x3)]))))))).

theorem iso_gen_sort:
 \forall (u2: T).(\forall (n1: nat).((iso (TSort n1) u2) \to (ex nat (\lambda 
(n2: nat).(eq T u2 (TSort n2))))))
\def
 \lambda (u2: T).(\lambda (n1: nat).(\lambda (H: (iso (TSort n1) u2)).(let 
TMP_1 \def (TSort n1) in (let TMP_2 \def (\lambda (t: T).(iso t u2)) in (let 
TMP_5 \def (\lambda (_: T).(let TMP_4 \def (\lambda (n2: nat).(let TMP_3 \def 
(TSort n2) in (eq T u2 TMP_3))) in (ex nat TMP_4))) in (let TMP_34 \def 
(\lambda (y: T).(\lambda (H0: (iso y u2)).(let TMP_8 \def (\lambda (t: 
T).(\lambda (t0: T).((eq T t (TSort n1)) \to (let TMP_7 \def (\lambda (n2: 
nat).(let TMP_6 \def (TSort n2) in (eq T t0 TMP_6))) in (ex nat TMP_7))))) in 
(let TMP_17 \def (\lambda (n0: nat).(\lambda (n2: nat).(\lambda (H1: (eq T 
(TSort n0) (TSort n1))).(let TMP_9 \def (\lambda (e: T).(match e with [(TSort 
n) \Rightarrow n | (TLRef _) \Rightarrow n0 | (THead _ _ _) \Rightarrow n0])) 
in (let TMP_10 \def (TSort n0) in (let TMP_11 \def (TSort n1) in (let H2 \def 
(f_equal T nat TMP_9 TMP_10 TMP_11 H1) in (let TMP_14 \def (\lambda (n3: 
nat).(let TMP_12 \def (TSort n2) in (let TMP_13 \def (TSort n3) in (eq T 
TMP_12 TMP_13)))) in (let TMP_15 \def (TSort n2) in (let TMP_16 \def 
(refl_equal T TMP_15) in (ex_intro nat TMP_14 n2 TMP_16))))))))))) in (let 
TMP_25 \def (\lambda (i1: nat).(\lambda (i2: nat).(\lambda (H1: (eq T (TLRef 
i1) (TSort n1))).(let TMP_18 \def (TLRef i1) in (let TMP_19 \def (\lambda 
(ee: T).(match ee with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow 
True | (THead _ _ _) \Rightarrow False])) in (let TMP_20 \def (TSort n1) in 
(let H2 \def (eq_ind T TMP_18 TMP_19 I TMP_20 H1) in (let TMP_23 \def 
(\lambda (n2: nat).(let TMP_21 \def (TLRef i2) in (let TMP_22 \def (TSort n2) 
in (eq T TMP_21 TMP_22)))) in (let TMP_24 \def (ex nat TMP_23) in (False_ind 
TMP_24 H2)))))))))) in (let TMP_33 \def (\lambda (v1: T).(\lambda (v2: 
T).(\lambda (t1: T).(\lambda (t2: T).(\lambda (k: K).(\lambda (H1: (eq T 
(THead k v1 t1) (TSort n1))).(let TMP_26 \def (THead k v1 t1) in (let TMP_27 
\def (\lambda (ee: T).(match ee with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow False | (THead _ _ _) \Rightarrow True])) in (let TMP_28 \def 
(TSort n1) in (let H2 \def (eq_ind T TMP_26 TMP_27 I TMP_28 H1) in (let 
TMP_31 \def (\lambda (n2: nat).(let TMP_29 \def (THead k v2 t2) in (let 
TMP_30 \def (TSort n2) in (eq T TMP_29 TMP_30)))) in (let TMP_32 \def (ex nat 
TMP_31) in (False_ind TMP_32 H2))))))))))))) in (iso_ind TMP_8 TMP_17 TMP_25 
TMP_33 y u2 H0))))))) in (insert_eq T TMP_1 TMP_2 TMP_5 TMP_34 H))))))).

theorem iso_gen_lref:
 \forall (u2: T).(\forall (n1: nat).((iso (TLRef n1) u2) \to (ex nat (\lambda 
(n2: nat).(eq T u2 (TLRef n2))))))
\def
 \lambda (u2: T).(\lambda (n1: nat).(\lambda (H: (iso (TLRef n1) u2)).(let 
TMP_1 \def (TLRef n1) in (let TMP_2 \def (\lambda (t: T).(iso t u2)) in (let 
TMP_5 \def (\lambda (_: T).(let TMP_4 \def (\lambda (n2: nat).(let TMP_3 \def 
(TLRef n2) in (eq T u2 TMP_3))) in (ex nat TMP_4))) in (let TMP_34 \def 
(\lambda (y: T).(\lambda (H0: (iso y u2)).(let TMP_8 \def (\lambda (t: 
T).(\lambda (t0: T).((eq T t (TLRef n1)) \to (let TMP_7 \def (\lambda (n2: 
nat).(let TMP_6 \def (TLRef n2) in (eq T t0 TMP_6))) in (ex nat TMP_7))))) in 
(let TMP_16 \def (\lambda (n0: nat).(\lambda (n2: nat).(\lambda (H1: (eq T 
(TSort n0) (TLRef n1))).(let TMP_9 \def (TSort n0) in (let TMP_10 \def 
(\lambda (ee: T).(match ee with [(TSort _) \Rightarrow True | (TLRef _) 
\Rightarrow False | (THead _ _ _) \Rightarrow False])) in (let TMP_11 \def 
(TLRef n1) in (let H2 \def (eq_ind T TMP_9 TMP_10 I TMP_11 H1) in (let TMP_14 
\def (\lambda (n3: nat).(let TMP_12 \def (TSort n2) in (let TMP_13 \def 
(TLRef n3) in (eq T TMP_12 TMP_13)))) in (let TMP_15 \def (ex nat TMP_14) in 
(False_ind TMP_15 H2)))))))))) in (let TMP_25 \def (\lambda (i1: 
nat).(\lambda (i2: nat).(\lambda (H1: (eq T (TLRef i1) (TLRef n1))).(let 
TMP_17 \def (\lambda (e: T).(match e with [(TSort _) \Rightarrow i1 | (TLRef 
n) \Rightarrow n | (THead _ _ _) \Rightarrow i1])) in (let TMP_18 \def (TLRef 
i1) in (let TMP_19 \def (TLRef n1) in (let H2 \def (f_equal T nat TMP_17 
TMP_18 TMP_19 H1) in (let TMP_22 \def (\lambda (n2: nat).(let TMP_20 \def 
(TLRef i2) in (let TMP_21 \def (TLRef n2) in (eq T TMP_20 TMP_21)))) in (let 
TMP_23 \def (TLRef i2) in (let TMP_24 \def (refl_equal T TMP_23) in (ex_intro 
nat TMP_22 i2 TMP_24))))))))))) in (let TMP_33 \def (\lambda (v1: T).(\lambda 
(v2: T).(\lambda (t1: T).(\lambda (t2: T).(\lambda (k: K).(\lambda (H1: (eq T 
(THead k v1 t1) (TLRef n1))).(let TMP_26 \def (THead k v1 t1) in (let TMP_27 
\def (\lambda (ee: T).(match ee with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow False | (THead _ _ _) \Rightarrow True])) in (let TMP_28 \def 
(TLRef n1) in (let H2 \def (eq_ind T TMP_26 TMP_27 I TMP_28 H1) in (let 
TMP_31 \def (\lambda (n2: nat).(let TMP_29 \def (THead k v2 t2) in (let 
TMP_30 \def (TLRef n2) in (eq T TMP_29 TMP_30)))) in (let TMP_32 \def (ex nat 
TMP_31) in (False_ind TMP_32 H2))))))))))))) in (iso_ind TMP_8 TMP_16 TMP_25 
TMP_33 y u2 H0))))))) in (insert_eq T TMP_1 TMP_2 TMP_5 TMP_34 H))))))).

theorem iso_gen_head:
 \forall (k: K).(\forall (v1: T).(\forall (t1: T).(\forall (u2: T).((iso 
(THead k v1 t1) u2) \to (ex_2 T T (\lambda (v2: T).(\lambda (t2: T).(eq T u2 
(THead k v2 t2)))))))))
\def
 \lambda (k: K).(\lambda (v1: T).(\lambda (t1: T).(\lambda (u2: T).(\lambda 
(H: (iso (THead k v1 t1) u2)).(let TMP_1 \def (THead k v1 t1) in (let TMP_2 
\def (\lambda (t: T).(iso t u2)) in (let TMP_5 \def (\lambda (_: T).(let 
TMP_4 \def (\lambda (v2: T).(\lambda (t2: T).(let TMP_3 \def (THead k v2 t2) 
in (eq T u2 TMP_3)))) in (ex_2 T T TMP_4))) in (let TMP_47 \def (\lambda (y: 
T).(\lambda (H0: (iso y u2)).(let TMP_8 \def (\lambda (t: T).(\lambda (t0: 
T).((eq T t (THead k v1 t1)) \to (let TMP_7 \def (\lambda (v2: T).(\lambda 
(t2: T).(let TMP_6 \def (THead k v2 t2) in (eq T t0 TMP_6)))) in (ex_2 T T 
TMP_7))))) in (let TMP_16 \def (\lambda (n1: nat).(\lambda (n2: nat).(\lambda 
(H1: (eq T (TSort n1) (THead k v1 t1))).(let TMP_9 \def (TSort n1) in (let 
TMP_10 \def (\lambda (ee: T).(match ee with [(TSort _) \Rightarrow True | 
(TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow False])) in (let 
TMP_11 \def (THead k v1 t1) in (let H2 \def (eq_ind T TMP_9 TMP_10 I TMP_11 
H1) in (let TMP_14 \def (\lambda (v2: T).(\lambda (t2: T).(let TMP_12 \def 
(TSort n2) in (let TMP_13 \def (THead k v2 t2) in (eq T TMP_12 TMP_13))))) in 
(let TMP_15 \def (ex_2 T T TMP_14) in (False_ind TMP_15 H2)))))))))) in (let 
TMP_24 \def (\lambda (i1: nat).(\lambda (i2: nat).(\lambda (H1: (eq T (TLRef 
i1) (THead k v1 t1))).(let TMP_17 \def (TLRef i1) in (let TMP_18 \def 
(\lambda (ee: T).(match ee with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow True | (THead _ _ _) \Rightarrow False])) in (let TMP_19 \def 
(THead k v1 t1) in (let H2 \def (eq_ind T TMP_17 TMP_18 I TMP_19 H1) in (let 
TMP_22 \def (\lambda (v2: T).(\lambda (t2: T).(let TMP_20 \def (TLRef i2) in 
(let TMP_21 \def (THead k v2 t2) in (eq T TMP_20 TMP_21))))) in (let TMP_23 
\def (ex_2 T T TMP_22) in (False_ind TMP_23 H2)))))))))) in (let TMP_46 \def 
(\lambda (v0: T).(\lambda (v2: T).(\lambda (t0: T).(\lambda (t2: T).(\lambda 
(k0: K).(\lambda (H1: (eq T (THead k0 v0 t0) (THead k v1 t1))).(let TMP_25 
\def (\lambda (e: T).(match e with [(TSort _) \Rightarrow k0 | (TLRef _) 
\Rightarrow k0 | (THead k1 _ _) \Rightarrow k1])) in (let TMP_26 \def (THead 
k0 v0 t0) in (let TMP_27 \def (THead k v1 t1) in (let H2 \def (f_equal T K 
TMP_25 TMP_26 TMP_27 H1) in (let TMP_28 \def (\lambda (e: T).(match e with 
[(TSort _) \Rightarrow v0 | (TLRef _) \Rightarrow v0 | (THead _ t _) 
\Rightarrow t])) in (let TMP_29 \def (THead k0 v0 t0) in (let TMP_30 \def 
(THead k v1 t1) in (let H3 \def (f_equal T T TMP_28 TMP_29 TMP_30 H1) in (let 
TMP_31 \def (\lambda (e: T).(match e with [(TSort _) \Rightarrow t0 | (TLRef 
_) \Rightarrow t0 | (THead _ _ t) \Rightarrow t])) in (let TMP_32 \def (THead 
k0 v0 t0) in (let TMP_33 \def (THead k v1 t1) in (let H4 \def (f_equal T T 
TMP_31 TMP_32 TMP_33 H1) in (let TMP_44 \def (\lambda (_: (eq T v0 
v1)).(\lambda (H6: (eq K k0 k)).(let TMP_37 \def (\lambda (k1: K).(let TMP_36 
\def (\lambda (v3: T).(\lambda (t3: T).(let TMP_34 \def (THead k1 v2 t2) in 
(let TMP_35 \def (THead k v3 t3) in (eq T TMP_34 TMP_35))))) in (ex_2 T T 
TMP_36))) in (let TMP_40 \def (\lambda (v3: T).(\lambda (t3: T).(let TMP_38 
\def (THead k v2 t2) in (let TMP_39 \def (THead k v3 t3) in (eq T TMP_38 
TMP_39))))) in (let TMP_41 \def (THead k v2 t2) in (let TMP_42 \def 
(refl_equal T TMP_41) in (let TMP_43 \def (ex_2_intro T T TMP_40 v2 t2 
TMP_42) in (eq_ind_r K k TMP_37 TMP_43 k0 H6)))))))) in (let TMP_45 \def 
(TMP_44 H3) in (TMP_45 H2))))))))))))))))))))) in (iso_ind TMP_8 TMP_16 
TMP_24 TMP_46 y u2 H0))))))) in (insert_eq T TMP_1 TMP_2 TMP_5 TMP_47 
H))))))))).

theorem iso_flats_lref_bind_false:
 \forall (f: F).(\forall (b: B).(\forall (i: nat).(\forall (v: T).(\forall 
(t: T).(\forall (vs: TList).((iso (THeads (Flat f) vs (TLRef i)) (THead (Bind 
b) v t)) \to (\forall (P: Prop).P)))))))
\def
 \lambda (f: F).(\lambda (b: B).(\lambda (i: nat).(\lambda (v: T).(\lambda 
(t: T).(\lambda (vs: TList).(let TMP_1 \def (\lambda (t0: TList).((iso 
(THeads (Flat f) t0 (TLRef i)) (THead (Bind b) v t)) \to (\forall (P: 
Prop).P))) in (let TMP_13 \def (\lambda (H: (iso (TLRef i) (THead (Bind b) v 
t))).(\lambda (P: Prop).(let TMP_2 \def (Bind b) in (let TMP_3 \def (THead 
TMP_2 v t) in (let H_x \def (iso_gen_lref TMP_3 i H) in (let H0 \def H_x in 
(let TMP_7 \def (\lambda (n2: nat).(let TMP_4 \def (Bind b) in (let TMP_5 
\def (THead TMP_4 v t) in (let TMP_6 \def (TLRef n2) in (eq T TMP_5 
TMP_6))))) in (let TMP_12 \def (\lambda (x: nat).(\lambda (H1: (eq T (THead 
(Bind b) v t) (TLRef x))).(let TMP_8 \def (Bind b) in (let TMP_9 \def (THead 
TMP_8 v t) in (let TMP_10 \def (\lambda (ee: T).(match ee with [(TSort _) 
\Rightarrow False | (TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow 
True])) in (let TMP_11 \def (TLRef x) in (let H2 \def (eq_ind T TMP_9 TMP_10 
I TMP_11 H1) in (False_ind P H2)))))))) in (ex_ind nat TMP_7 P TMP_12 
H0))))))))) in (let TMP_31 \def (\lambda (t0: T).(\lambda (t1: 
TList).(\lambda (_: (((iso (THeads (Flat f) t1 (TLRef i)) (THead (Bind b) v 
t)) \to (\forall (P: Prop).P)))).(\lambda (H0: (iso (THead (Flat f) t0 
(THeads (Flat f) t1 (TLRef i))) (THead (Bind b) v t))).(\lambda (P: 
Prop).(let TMP_14 \def (Flat f) in (let TMP_15 \def (Flat f) in (let TMP_16 
\def (TLRef i) in (let TMP_17 \def (THeads TMP_15 t1 TMP_16) in (let TMP_18 
\def (Bind b) in (let TMP_19 \def (THead TMP_18 v t) in (let H_x \def 
(iso_gen_head TMP_14 t0 TMP_17 TMP_19 H0) in (let H1 \def H_x in (let TMP_24 
\def (\lambda (v2: T).(\lambda (t2: T).(let TMP_20 \def (Bind b) in (let 
TMP_21 \def (THead TMP_20 v t) in (let TMP_22 \def (Flat f) in (let TMP_23 
\def (THead TMP_22 v2 t2) in (eq T TMP_21 TMP_23))))))) in (let TMP_30 \def 
(\lambda (x0: T).(\lambda (x1: T).(\lambda (H2: (eq T (THead (Bind b) v t) 
(THead (Flat f) x0 x1))).(let TMP_25 \def (Bind b) in (let TMP_26 \def (THead 
TMP_25 v t) in (let TMP_27 \def (\lambda (ee: T).(match ee with [(TSort _) 
\Rightarrow False | (TLRef _) \Rightarrow False | (THead k _ _) \Rightarrow 
(match k with [(Bind _) \Rightarrow True | (Flat _) \Rightarrow False])])) in 
(let TMP_28 \def (Flat f) in (let TMP_29 \def (THead TMP_28 x0 x1) in (let H3 
\def (eq_ind T TMP_26 TMP_27 I TMP_29 H2) in (False_ind P H3)))))))))) in 
(ex_2_ind T T TMP_24 P TMP_30 H1)))))))))))))))) in (TList_ind TMP_1 TMP_13 
TMP_31 vs))))))))).

theorem iso_flats_flat_bind_false:
 \forall (f1: F).(\forall (f2: F).(\forall (b: B).(\forall (v: T).(\forall 
(v2: T).(\forall (t: T).(\forall (t2: T).(\forall (vs: TList).((iso (THeads 
(Flat f1) vs (THead (Flat f2) v2 t2)) (THead (Bind b) v t)) \to (\forall (P: 
Prop).P)))))))))
\def
 \lambda (f1: F).(\lambda (f2: F).(\lambda (b: B).(\lambda (v: T).(\lambda 
(v2: T).(\lambda (t: T).(\lambda (t2: T).(\lambda (vs: TList).(let TMP_1 \def 
(\lambda (t0: TList).((iso (THeads (Flat f1) t0 (THead (Flat f2) v2 t2)) 
(THead (Bind b) v t)) \to (\forall (P: Prop).P))) in (let TMP_16 \def 
(\lambda (H: (iso (THead (Flat f2) v2 t2) (THead (Bind b) v t))).(\lambda (P: 
Prop).(let TMP_2 \def (Flat f2) in (let TMP_3 \def (Bind b) in (let TMP_4 
\def (THead TMP_3 v t) in (let H_x \def (iso_gen_head TMP_2 v2 t2 TMP_4 H) in 
(let H0 \def H_x in (let TMP_9 \def (\lambda (v3: T).(\lambda (t3: T).(let 
TMP_5 \def (Bind b) in (let TMP_6 \def (THead TMP_5 v t) in (let TMP_7 \def 
(Flat f2) in (let TMP_8 \def (THead TMP_7 v3 t3) in (eq T TMP_6 TMP_8))))))) 
in (let TMP_15 \def (\lambda (x0: T).(\lambda (x1: T).(\lambda (H1: (eq T 
(THead (Bind b) v t) (THead (Flat f2) x0 x1))).(let TMP_10 \def (Bind b) in 
(let TMP_11 \def (THead TMP_10 v t) in (let TMP_12 \def (\lambda (ee: 
T).(match ee with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False 
| (THead k _ _) \Rightarrow (match k with [(Bind _) \Rightarrow True | (Flat 
_) \Rightarrow False])])) in (let TMP_13 \def (Flat f2) in (let TMP_14 \def 
(THead TMP_13 x0 x1) in (let H2 \def (eq_ind T TMP_11 TMP_12 I TMP_14 H1) in 
(False_ind P H2)))))))))) in (ex_2_ind T T TMP_9 P TMP_15 H0)))))))))) in 
(let TMP_35 \def (\lambda (t0: T).(\lambda (t1: TList).(\lambda (_: (((iso 
(THeads (Flat f1) t1 (THead (Flat f2) v2 t2)) (THead (Bind b) v t)) \to 
(\forall (P: Prop).P)))).(\lambda (H0: (iso (THead (Flat f1) t0 (THeads (Flat 
f1) t1 (THead (Flat f2) v2 t2))) (THead (Bind b) v t))).(\lambda (P: 
Prop).(let TMP_17 \def (Flat f1) in (let TMP_18 \def (Flat f1) in (let TMP_19 
\def (Flat f2) in (let TMP_20 \def (THead TMP_19 v2 t2) in (let TMP_21 \def 
(THeads TMP_18 t1 TMP_20) in (let TMP_22 \def (Bind b) in (let TMP_23 \def 
(THead TMP_22 v t) in (let H_x \def (iso_gen_head TMP_17 t0 TMP_21 TMP_23 H0) 
in (let H1 \def H_x in (let TMP_28 \def (\lambda (v3: T).(\lambda (t3: 
T).(let TMP_24 \def (Bind b) in (let TMP_25 \def (THead TMP_24 v t) in (let 
TMP_26 \def (Flat f1) in (let TMP_27 \def (THead TMP_26 v3 t3) in (eq T 
TMP_25 TMP_27))))))) in (let TMP_34 \def (\lambda (x0: T).(\lambda (x1: 
T).(\lambda (H2: (eq T (THead (Bind b) v t) (THead (Flat f1) x0 x1))).(let 
TMP_29 \def (Bind b) in (let TMP_30 \def (THead TMP_29 v t) in (let TMP_31 
\def (\lambda (ee: T).(match ee with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow False | (THead k _ _) \Rightarrow (match k with [(Bind _) 
\Rightarrow True | (Flat _) \Rightarrow False])])) in (let TMP_32 \def (Flat 
f1) in (let TMP_33 \def (THead TMP_32 x0 x1) in (let H3 \def (eq_ind T TMP_30 
TMP_31 I TMP_33 H2) in (False_ind P H3)))))))))) in (ex_2_ind T T TMP_28 P 
TMP_34 H1))))))))))))))))) in (TList_ind TMP_1 TMP_16 TMP_35 vs))))))))))).

