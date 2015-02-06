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

include "basic_1/lift/defs.ma".

include "basic_1/s/props.ma".

include "basic_1/T/fwd.ma".

theorem lift_sort:
 \forall (n: nat).(\forall (h: nat).(\forall (d: nat).(eq T (lift h d (TSort 
n)) (TSort n))))
\def
 \lambda (n: nat).(\lambda (_: nat).(\lambda (_: nat).(let TMP_1 \def (TSort 
n) in (refl_equal T TMP_1)))).

theorem lift_lref_lt:
 \forall (n: nat).(\forall (h: nat).(\forall (d: nat).((lt n d) \to (eq T 
(lift h d (TLRef n)) (TLRef n)))))
\def
 \lambda (n: nat).(\lambda (h: nat).(\lambda (d: nat).(\lambda (H: (lt n 
d)).(let TMP_4 \def (\lambda (b: bool).(let TMP_1 \def (match b with [true 
\Rightarrow n | false \Rightarrow (plus n h)]) in (let TMP_2 \def (TLRef 
TMP_1) in (let TMP_3 \def (TLRef n) in (eq T TMP_2 TMP_3))))) in (let TMP_5 
\def (TLRef n) in (let TMP_6 \def (refl_equal T TMP_5) in (let TMP_7 \def 
(blt n d) in (let TMP_8 \def (blt n d) in (let TMP_9 \def (lt_blt d n H) in 
(let TMP_10 \def (sym_eq bool TMP_8 true TMP_9) in (eq_ind bool true TMP_4 
TMP_6 TMP_7 TMP_10))))))))))).

theorem lift_lref_ge:
 \forall (n: nat).(\forall (h: nat).(\forall (d: nat).((le d n) \to (eq T 
(lift h d (TLRef n)) (TLRef (plus n h))))))
\def
 \lambda (n: nat).(\lambda (h: nat).(\lambda (d: nat).(\lambda (H: (le d 
n)).(let TMP_5 \def (\lambda (b: bool).(let TMP_1 \def (match b with [true 
\Rightarrow n | false \Rightarrow (plus n h)]) in (let TMP_2 \def (TLRef 
TMP_1) in (let TMP_3 \def (plus n h) in (let TMP_4 \def (TLRef TMP_3) in (eq 
T TMP_2 TMP_4)))))) in (let TMP_6 \def (plus n h) in (let TMP_7 \def (TLRef 
TMP_6) in (let TMP_8 \def (refl_equal T TMP_7) in (let TMP_9 \def (blt n d) 
in (let TMP_10 \def (blt n d) in (let TMP_11 \def (le_bge d n H) in (let 
TMP_12 \def (sym_eq bool TMP_10 false TMP_11) in (eq_ind bool false TMP_5 
TMP_8 TMP_9 TMP_12)))))))))))).

theorem lift_head:
 \forall (k: K).(\forall (u: T).(\forall (t: T).(\forall (h: nat).(\forall 
(d: nat).(eq T (lift h d (THead k u t)) (THead k (lift h d u) (lift h (s k d) 
t)))))))
\def
 \lambda (k: K).(\lambda (u: T).(\lambda (t: T).(\lambda (h: nat).(\lambda 
(d: nat).(let TMP_1 \def (lift h d u) in (let TMP_2 \def (s k d) in (let 
TMP_3 \def (lift h TMP_2 t) in (let TMP_4 \def (THead k TMP_1 TMP_3) in 
(refl_equal T TMP_4))))))))).

theorem lift_bind:
 \forall (b: B).(\forall (u: T).(\forall (t: T).(\forall (h: nat).(\forall 
(d: nat).(eq T (lift h d (THead (Bind b) u t)) (THead (Bind b) (lift h d u) 
(lift h (S d) t)))))))
\def
 \lambda (b: B).(\lambda (u: T).(\lambda (t: T).(\lambda (h: nat).(\lambda 
(d: nat).(let TMP_1 \def (Bind b) in (let TMP_2 \def (lift h d u) in (let 
TMP_3 \def (S d) in (let TMP_4 \def (lift h TMP_3 t) in (let TMP_5 \def 
(THead TMP_1 TMP_2 TMP_4) in (refl_equal T TMP_5)))))))))).

theorem lift_flat:
 \forall (f: F).(\forall (u: T).(\forall (t: T).(\forall (h: nat).(\forall 
(d: nat).(eq T (lift h d (THead (Flat f) u t)) (THead (Flat f) (lift h d u) 
(lift h d t)))))))
\def
 \lambda (f: F).(\lambda (u: T).(\lambda (t: T).(\lambda (h: nat).(\lambda 
(d: nat).(let TMP_1 \def (Flat f) in (let TMP_2 \def (lift h d u) in (let 
TMP_3 \def (lift h d t) in (let TMP_4 \def (THead TMP_1 TMP_2 TMP_3) in 
(refl_equal T TMP_4))))))))).

theorem thead_x_lift_y_y:
 \forall (k: K).(\forall (t: T).(\forall (v: T).(\forall (h: nat).(\forall 
(d: nat).((eq T (THead k v (lift h d t)) t) \to (\forall (P: Prop).P))))))
\def
 \lambda (k: K).(\lambda (t: T).(let TMP_1 \def (\lambda (t0: T).(\forall (v: 
T).(\forall (h: nat).(\forall (d: nat).((eq T (THead k v (lift h d t0)) t0) 
\to (\forall (P: Prop).P)))))) in (let TMP_7 \def (\lambda (n: nat).(\lambda 
(v: T).(\lambda (h: nat).(\lambda (d: nat).(\lambda (H: (eq T (THead k v 
(lift h d (TSort n))) (TSort n))).(\lambda (P: Prop).(let TMP_2 \def (TSort 
n) in (let TMP_3 \def (lift h d TMP_2) in (let TMP_4 \def (THead k v TMP_3) 
in (let TMP_5 \def (\lambda (ee: T).(match ee with [(TSort _) \Rightarrow 
False | (TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow True])) in 
(let TMP_6 \def (TSort n) in (let H0 \def (eq_ind T TMP_4 TMP_5 I TMP_6 H) in 
(False_ind P H0))))))))))))) in (let TMP_13 \def (\lambda (n: nat).(\lambda 
(v: T).(\lambda (h: nat).(\lambda (d: nat).(\lambda (H: (eq T (THead k v 
(lift h d (TLRef n))) (TLRef n))).(\lambda (P: Prop).(let TMP_8 \def (TLRef 
n) in (let TMP_9 \def (lift h d TMP_8) in (let TMP_10 \def (THead k v TMP_9) 
in (let TMP_11 \def (\lambda (ee: T).(match ee with [(TSort _) \Rightarrow 
False | (TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow True])) in 
(let TMP_12 \def (TLRef n) in (let H0 \def (eq_ind T TMP_10 TMP_11 I TMP_12 
H) in (False_ind P H0))))))))))))) in (let TMP_72 \def (\lambda (k0: 
K).(\lambda (t0: T).(\lambda (_: ((\forall (v: T).(\forall (h: nat).(\forall 
(d: nat).((eq T (THead k v (lift h d t0)) t0) \to (\forall (P: 
Prop).P))))))).(\lambda (t1: T).(\lambda (H0: ((\forall (v: T).(\forall (h: 
nat).(\forall (d: nat).((eq T (THead k v (lift h d t1)) t1) \to (\forall (P: 
Prop).P))))))).(\lambda (v: T).(\lambda (h: nat).(\lambda (d: nat).(\lambda 
(H1: (eq T (THead k v (lift h d (THead k0 t0 t1))) (THead k0 t0 
t1))).(\lambda (P: Prop).(let TMP_14 \def (\lambda (e: T).(match e with 
[(TSort _) \Rightarrow k | (TLRef _) \Rightarrow k | (THead k1 _ _) 
\Rightarrow k1])) in (let TMP_15 \def (THead k0 t0 t1) in (let TMP_16 \def 
(lift h d TMP_15) in (let TMP_17 \def (THead k v TMP_16) in (let TMP_18 \def 
(THead k0 t0 t1) in (let H2 \def (f_equal T K TMP_14 TMP_17 TMP_18 H1) in 
(let TMP_19 \def (\lambda (e: T).(match e with [(TSort _) \Rightarrow v | 
(TLRef _) \Rightarrow v | (THead _ t2 _) \Rightarrow t2])) in (let TMP_20 
\def (THead k0 t0 t1) in (let TMP_21 \def (lift h d TMP_20) in (let TMP_22 
\def (THead k v TMP_21) in (let TMP_23 \def (THead k0 t0 t1) in (let H3 \def 
(f_equal T T TMP_19 TMP_22 TMP_23 H1) in (let TMP_54 \def (\lambda (e: 
T).(match e with [(TSort _) \Rightarrow (let TMP_44 \def (\lambda (x: 
nat).(plus x h)) in (let TMP_45 \def (lref_map TMP_44 d t0) in (let TMP_51 
\def (\lambda (x: nat).(plus x h)) in (let TMP_52 \def (s k0 d) in (let 
TMP_53 \def (lref_map TMP_51 TMP_52 t1) in (THead k0 TMP_45 TMP_53)))))) | 
(TLRef _) \Rightarrow (let TMP_29 \def (\lambda (x: nat).(plus x h)) in (let 
TMP_30 \def (lref_map TMP_29 d t0) in (let TMP_36 \def (\lambda (x: 
nat).(plus x h)) in (let TMP_37 \def (s k0 d) in (let TMP_38 \def (lref_map 
TMP_36 TMP_37 t1) in (THead k0 TMP_30 TMP_38)))))) | (THead _ _ t2) 
\Rightarrow t2])) in (let TMP_55 \def (THead k0 t0 t1) in (let TMP_56 \def 
(lift h d TMP_55) in (let TMP_57 \def (THead k v TMP_56) in (let TMP_58 \def 
(THead k0 t0 t1) in (let H4 \def (f_equal T T TMP_54 TMP_57 TMP_58 H1) in 
(let TMP_70 \def (\lambda (_: (eq T v t0)).(\lambda (H6: (eq K k k0)).(let 
TMP_59 \def (\lambda (k1: K).(\forall (v0: T).(\forall (h0: nat).(\forall 
(d0: nat).((eq T (THead k1 v0 (lift h0 d0 t1)) t1) \to (\forall (P0: 
Prop).P0)))))) in (let H7 \def (eq_ind K k TMP_59 H0 k0 H6) in (let TMP_60 
\def (THead k0 t0 t1) in (let TMP_61 \def (lift h d TMP_60) in (let TMP_62 
\def (\lambda (t2: T).(eq T t2 t1)) in (let TMP_63 \def (lift h d t0) in (let 
TMP_64 \def (s k0 d) in (let TMP_65 \def (lift h TMP_64 t1) in (let TMP_66 
\def (THead k0 TMP_63 TMP_65) in (let TMP_67 \def (lift_head k0 t0 t1 h d) in 
(let H8 \def (eq_ind T TMP_61 TMP_62 H4 TMP_66 TMP_67) in (let TMP_68 \def 
(lift h d t0) in (let TMP_69 \def (s k0 d) in (H7 TMP_68 h TMP_69 H8 
P)))))))))))))))) in (let TMP_71 \def (TMP_70 H3) in (TMP_71 
H2))))))))))))))))))))))))))))))) in (T_ind TMP_1 TMP_7 TMP_13 TMP_72 t)))))).

theorem lift_r:
 \forall (t: T).(\forall (d: nat).(eq T (lift O d t) t))
\def
 \lambda (t: T).(let TMP_2 \def (\lambda (t0: T).(\forall (d: nat).(let TMP_1 
\def (lift O d t0) in (eq T TMP_1 t0)))) in (let TMP_4 \def (\lambda (n: 
nat).(\lambda (_: nat).(let TMP_3 \def (TSort n) in (refl_equal T TMP_3)))) 
in (let TMP_31 \def (\lambda (n: nat).(\lambda (d: nat).(let TMP_5 \def 
(TLRef n) in (let TMP_6 \def (lift O d TMP_5) in (let TMP_7 \def (TLRef n) in 
(let TMP_8 \def (eq T TMP_6 TMP_7) in (let TMP_17 \def (\lambda (H: (lt n 
d)).(let TMP_9 \def (TLRef n) in (let TMP_11 \def (\lambda (t0: T).(let 
TMP_10 \def (TLRef n) in (eq T t0 TMP_10))) in (let TMP_12 \def (TLRef n) in 
(let TMP_13 \def (refl_equal T TMP_12) in (let TMP_14 \def (TLRef n) in (let 
TMP_15 \def (lift O d TMP_14) in (let TMP_16 \def (lift_lref_lt n O d H) in 
(eq_ind_r T TMP_9 TMP_11 TMP_13 TMP_15 TMP_16))))))))) in (let TMP_30 \def 
(\lambda (H: (le d n)).(let TMP_18 \def (plus n O) in (let TMP_19 \def (TLRef 
TMP_18) in (let TMP_21 \def (\lambda (t0: T).(let TMP_20 \def (TLRef n) in 
(eq T t0 TMP_20))) in (let TMP_22 \def (plus n O) in (let TMP_23 \def (plus n 
O) in (let TMP_24 \def (plus_n_O n) in (let TMP_25 \def (sym_eq nat n TMP_23 
TMP_24) in (let TMP_26 \def (f_equal nat T TLRef TMP_22 n TMP_25) in (let 
TMP_27 \def (TLRef n) in (let TMP_28 \def (lift O d TMP_27) in (let TMP_29 
\def (lift_lref_ge n O d H) in (eq_ind_r T TMP_19 TMP_21 TMP_26 TMP_28 
TMP_29))))))))))))) in (lt_le_e n d TMP_8 TMP_17 TMP_30))))))))) in (let 
TMP_61 \def (\lambda (k: K).(\lambda (t0: T).(\lambda (H: ((\forall (d: 
nat).(eq T (lift O d t0) t0)))).(\lambda (t1: T).(\lambda (H0: ((\forall (d: 
nat).(eq T (lift O d t1) t1)))).(\lambda (d: nat).(let TMP_32 \def (lift O d 
t0) in (let TMP_33 \def (s k d) in (let TMP_34 \def (lift O TMP_33 t1) in 
(let TMP_35 \def (THead k TMP_32 TMP_34) in (let TMP_37 \def (\lambda (t2: 
T).(let TMP_36 \def (THead k t0 t1) in (eq T t2 TMP_36))) in (let TMP_38 \def 
(THead k t0 t1) in (let TMP_39 \def (lift O d t0) in (let TMP_40 \def (s k d) 
in (let TMP_41 \def (lift O TMP_40 t1) in (let TMP_42 \def (THead k TMP_39 
TMP_41) in (let TMP_43 \def (lift O d t0) in (let TMP_44 \def (s k d) in (let 
TMP_45 \def (lift O TMP_44 t1) in (let TMP_46 \def (THead k TMP_43 TMP_45) in 
(let TMP_47 \def (THead k t0 t1) in (let TMP_48 \def (lift O d t0) in (let 
TMP_49 \def (s k d) in (let TMP_50 \def (lift O TMP_49 t1) in (let TMP_51 
\def (refl_equal K k) in (let TMP_52 \def (H d) in (let TMP_53 \def (s k d) 
in (let TMP_54 \def (H0 TMP_53) in (let TMP_55 \def (f_equal3 K T T T THead k 
k TMP_48 t0 TMP_50 t1 TMP_51 TMP_52 TMP_54) in (let TMP_56 \def (sym_eq T 
TMP_46 TMP_47 TMP_55) in (let TMP_57 \def (sym_eq T TMP_38 TMP_42 TMP_56) in 
(let TMP_58 \def (THead k t0 t1) in (let TMP_59 \def (lift O d TMP_58) in 
(let TMP_60 \def (lift_head k t0 t1 O d) in (eq_ind_r T TMP_35 TMP_37 TMP_57 
TMP_59 TMP_60))))))))))))))))))))))))))))))))))) in (T_ind TMP_2 TMP_4 TMP_31 
TMP_61 t))))).

theorem lift_lref_gt:
 \forall (d: nat).(\forall (n: nat).((lt d n) \to (eq T (lift (S O) d (TLRef 
(pred n))) (TLRef n))))
\def
 \lambda (d: nat).(\lambda (n: nat).(\lambda (H: (lt d n)).(let TMP_1 \def 
(pred n) in (let TMP_2 \def (S O) in (let TMP_3 \def (plus TMP_1 TMP_2) in 
(let TMP_4 \def (TLRef TMP_3) in (let TMP_6 \def (\lambda (t: T).(let TMP_5 
\def (TLRef n) in (eq T t TMP_5))) in (let TMP_7 \def (S O) in (let TMP_8 
\def (pred n) in (let TMP_9 \def (plus TMP_7 TMP_8) in (let TMP_12 \def 
(\lambda (n0: nat).(let TMP_10 \def (TLRef n0) in (let TMP_11 \def (TLRef n) 
in (eq T TMP_10 TMP_11)))) in (let TMP_15 \def (\lambda (n0: nat).(let TMP_13 
\def (TLRef n0) in (let TMP_14 \def (TLRef n) in (eq T TMP_13 TMP_14)))) in 
(let TMP_16 \def (TLRef n) in (let TMP_17 \def (refl_equal T TMP_16) in (let 
TMP_18 \def (pred n) in (let TMP_19 \def (S TMP_18) in (let TMP_20 \def 
(S_pred n d H) in (let TMP_21 \def (eq_ind nat n TMP_15 TMP_17 TMP_19 TMP_20) 
in (let TMP_22 \def (pred n) in (let TMP_23 \def (S O) in (let TMP_24 \def 
(plus TMP_22 TMP_23) in (let TMP_25 \def (S O) in (let TMP_26 \def (pred n) 
in (let TMP_27 \def (plus_sym TMP_25 TMP_26) in (let TMP_28 \def (eq_ind nat 
TMP_9 TMP_12 TMP_21 TMP_24 TMP_27) in (let TMP_29 \def (S O) in (let TMP_30 
\def (pred n) in (let TMP_31 \def (TLRef TMP_30) in (let TMP_32 \def (lift 
TMP_29 d TMP_31) in (let TMP_33 \def (pred n) in (let TMP_34 \def (S O) in 
(let TMP_35 \def (pred n) in (let TMP_37 \def (\lambda (n0: nat).(let TMP_36 
\def (S d) in (le TMP_36 n0))) in (let TMP_38 \def (pred n) in (let TMP_39 
\def (S TMP_38) in (let TMP_40 \def (S_pred n d H) in (let TMP_41 \def 
(eq_ind nat n TMP_37 H TMP_39 TMP_40) in (let TMP_42 \def (le_S_n d TMP_35 
TMP_41) in (let TMP_43 \def (lift_lref_ge TMP_33 TMP_34 d TMP_42) in 
(eq_ind_r T TMP_4 TMP_6 TMP_28 TMP_32 
TMP_43)))))))))))))))))))))))))))))))))))))))).

theorem lift_tle:
 \forall (t: T).(\forall (h: nat).(\forall (d: nat).(tle t (lift h d t))))
\def
 \lambda (t: T).(let TMP_4 \def (\lambda (t0: T).(\forall (h: nat).(\forall 
(d: nat).(let TMP_1 \def (tweight t0) in (let TMP_2 \def (lift h d t0) in 
(let TMP_3 \def (tweight TMP_2) in (le TMP_1 TMP_3))))))) in (let TMP_6 \def 
(\lambda (_: nat).(\lambda (_: nat).(\lambda (_: nat).(let TMP_5 \def (S O) 
in (le_n TMP_5))))) in (let TMP_8 \def (\lambda (_: nat).(\lambda (_: 
nat).(\lambda (_: nat).(let TMP_7 \def (S O) in (le_n TMP_7))))) in (let 
TMP_31 \def (\lambda (k: K).(\lambda (t0: T).(\lambda (H: ((\forall (h: 
nat).(\forall (d: nat).(le (tweight t0) (tweight (lift h d t0))))))).(\lambda 
(t1: T).(\lambda (H0: ((\forall (h: nat).(\forall (d: nat).(le (tweight t1) 
(tweight (lift h d t1))))))).(\lambda (h: nat).(\lambda (d: nat).(let H_y 
\def (H h d) in (let TMP_9 \def (s k d) in (let H_y0 \def (H0 h TMP_9) in 
(let TMP_10 \def (tweight t0) in (let TMP_11 \def (tweight t1) in (let TMP_12 
\def (plus TMP_10 TMP_11) in (let TMP_13 \def (\lambda (x: nat).(plus x h)) 
in (let TMP_14 \def (lref_map TMP_13 d t0) in (let TMP_15 \def (tweight 
TMP_14) in (let TMP_16 \def (\lambda (x: nat).(plus x h)) in (let TMP_17 \def 
(s k d) in (let TMP_18 \def (lref_map TMP_16 TMP_17 t1) in (let TMP_19 \def 
(tweight TMP_18) in (let TMP_20 \def (plus TMP_15 TMP_19) in (let TMP_21 \def 
(tweight t0) in (let TMP_22 \def (\lambda (x: nat).(plus x h)) in (let TMP_23 
\def (lref_map TMP_22 d t0) in (let TMP_24 \def (tweight TMP_23) in (let 
TMP_25 \def (tweight t1) in (let TMP_26 \def (\lambda (x: nat).(plus x h)) in 
(let TMP_27 \def (s k d) in (let TMP_28 \def (lref_map TMP_26 TMP_27 t1) in 
(let TMP_29 \def (tweight TMP_28) in (let TMP_30 \def (le_plus_plus TMP_21 
TMP_24 TMP_25 TMP_29 H_y H_y0) in (le_n_S TMP_12 TMP_20 
TMP_30)))))))))))))))))))))))))))))))) in (T_ind TMP_4 TMP_6 TMP_8 TMP_31 
t))))).

theorem lifts_tapp:
 \forall (h: nat).(\forall (d: nat).(\forall (v: T).(\forall (vs: TList).(eq 
TList (lifts h d (TApp vs v)) (TApp (lifts h d vs) (lift h d v))))))
\def
 \lambda (h: nat).(\lambda (d: nat).(\lambda (v: T).(\lambda (vs: TList).(let 
TMP_6 \def (\lambda (t: TList).(let TMP_1 \def (TApp t v) in (let TMP_2 \def 
(lifts h d TMP_1) in (let TMP_3 \def (lifts h d t) in (let TMP_4 \def (lift h 
d v) in (let TMP_5 \def (TApp TMP_3 TMP_4) in (eq TList TMP_2 TMP_5))))))) in 
(let TMP_7 \def (lift h d v) in (let TMP_8 \def (TCons TMP_7 TNil) in (let 
TMP_9 \def (refl_equal TList TMP_8) in (let TMP_29 \def (\lambda (t: 
T).(\lambda (t0: TList).(\lambda (H: (eq TList (lifts h d (TApp t0 v)) (TApp 
(lifts h d t0) (lift h d v)))).(let TMP_10 \def (lifts h d t0) in (let TMP_11 
\def (lift h d v) in (let TMP_12 \def (TApp TMP_10 TMP_11) in (let TMP_20 
\def (\lambda (t1: TList).(let TMP_13 \def (lift h d t) in (let TMP_14 \def 
(TCons TMP_13 t1) in (let TMP_15 \def (lift h d t) in (let TMP_16 \def (lifts 
h d t0) in (let TMP_17 \def (lift h d v) in (let TMP_18 \def (TApp TMP_16 
TMP_17) in (let TMP_19 \def (TCons TMP_15 TMP_18) in (eq TList TMP_14 
TMP_19))))))))) in (let TMP_21 \def (lift h d t) in (let TMP_22 \def (lifts h 
d t0) in (let TMP_23 \def (lift h d v) in (let TMP_24 \def (TApp TMP_22 
TMP_23) in (let TMP_25 \def (TCons TMP_21 TMP_24) in (let TMP_26 \def 
(refl_equal TList TMP_25) in (let TMP_27 \def (TApp t0 v) in (let TMP_28 \def 
(lifts h d TMP_27) in (eq_ind_r TList TMP_12 TMP_20 TMP_26 TMP_28 
H)))))))))))))))) in (TList_ind TMP_6 TMP_9 TMP_29 vs))))))))).

theorem lift_free:
 \forall (t: T).(\forall (h: nat).(\forall (k: nat).(\forall (d: 
nat).(\forall (e: nat).((le e (plus d h)) \to ((le d e) \to (eq T (lift k e 
(lift h d t)) (lift (plus k h) d t))))))))
\def
 \lambda (t: T).(let TMP_5 \def (\lambda (t0: T).(\forall (h: nat).(\forall 
(k: nat).(\forall (d: nat).(\forall (e: nat).((le e (plus d h)) \to ((le d e) 
\to (let TMP_1 \def (lift h d t0) in (let TMP_2 \def (lift k e TMP_1) in (let 
TMP_3 \def (plus k h) in (let TMP_4 \def (lift TMP_3 d t0) in (eq T TMP_2 
TMP_4)))))))))))) in (let TMP_35 \def (\lambda (n: nat).(\lambda (h: 
nat).(\lambda (k: nat).(\lambda (d: nat).(\lambda (e: nat).(\lambda (_: (le e 
(plus d h))).(\lambda (_: (le d e)).(let TMP_6 \def (TSort n) in (let TMP_11 
\def (\lambda (t0: T).(let TMP_7 \def (lift k e t0) in (let TMP_8 \def (plus 
k h) in (let TMP_9 \def (TSort n) in (let TMP_10 \def (lift TMP_8 d TMP_9) in 
(eq T TMP_7 TMP_10)))))) in (let TMP_12 \def (TSort n) in (let TMP_16 \def 
(\lambda (t0: T).(let TMP_13 \def (plus k h) in (let TMP_14 \def (TSort n) in 
(let TMP_15 \def (lift TMP_13 d TMP_14) in (eq T t0 TMP_15))))) in (let 
TMP_17 \def (TSort n) in (let TMP_19 \def (\lambda (t0: T).(let TMP_18 \def 
(TSort n) in (eq T TMP_18 t0))) in (let TMP_20 \def (TSort n) in (let TMP_21 
\def (refl_equal T TMP_20) in (let TMP_22 \def (plus k h) in (let TMP_23 \def 
(TSort n) in (let TMP_24 \def (lift TMP_22 d TMP_23) in (let TMP_25 \def 
(plus k h) in (let TMP_26 \def (lift_sort n TMP_25 d) in (let TMP_27 \def 
(eq_ind_r T TMP_17 TMP_19 TMP_21 TMP_24 TMP_26) in (let TMP_28 \def (TSort n) 
in (let TMP_29 \def (lift k e TMP_28) in (let TMP_30 \def (lift_sort n k e) 
in (let TMP_31 \def (eq_ind_r T TMP_12 TMP_16 TMP_27 TMP_29 TMP_30) in (let 
TMP_32 \def (TSort n) in (let TMP_33 \def (lift h d TMP_32) in (let TMP_34 
\def (lift_sort n h d) in (eq_ind_r T TMP_6 TMP_11 TMP_31 TMP_33 
TMP_34))))))))))))))))))))))))))))) in (let TMP_122 \def (\lambda (n: 
nat).(\lambda (h: nat).(\lambda (k: nat).(\lambda (d: nat).(\lambda (e: 
nat).(\lambda (H: (le e (plus d h))).(\lambda (H0: (le d e)).(let TMP_36 \def 
(TLRef n) in (let TMP_37 \def (lift h d TMP_36) in (let TMP_38 \def (lift k e 
TMP_37) in (let TMP_39 \def (plus k h) in (let TMP_40 \def (TLRef n) in (let 
TMP_41 \def (lift TMP_39 d TMP_40) in (let TMP_42 \def (eq T TMP_38 TMP_41) 
in (let TMP_73 \def (\lambda (H1: (lt n d)).(let TMP_43 \def (TLRef n) in 
(let TMP_48 \def (\lambda (t0: T).(let TMP_44 \def (lift k e t0) in (let 
TMP_45 \def (plus k h) in (let TMP_46 \def (TLRef n) in (let TMP_47 \def 
(lift TMP_45 d TMP_46) in (eq T TMP_44 TMP_47)))))) in (let TMP_49 \def 
(TLRef n) in (let TMP_53 \def (\lambda (t0: T).(let TMP_50 \def (plus k h) in 
(let TMP_51 \def (TLRef n) in (let TMP_52 \def (lift TMP_50 d TMP_51) in (eq 
T t0 TMP_52))))) in (let TMP_54 \def (TLRef n) in (let TMP_56 \def (\lambda 
(t0: T).(let TMP_55 \def (TLRef n) in (eq T TMP_55 t0))) in (let TMP_57 \def 
(TLRef n) in (let TMP_58 \def (refl_equal T TMP_57) in (let TMP_59 \def (plus 
k h) in (let TMP_60 \def (TLRef n) in (let TMP_61 \def (lift TMP_59 d TMP_60) 
in (let TMP_62 \def (plus k h) in (let TMP_63 \def (lift_lref_lt n TMP_62 d 
H1) in (let TMP_64 \def (eq_ind_r T TMP_54 TMP_56 TMP_58 TMP_61 TMP_63) in 
(let TMP_65 \def (TLRef n) in (let TMP_66 \def (lift k e TMP_65) in (let 
TMP_67 \def (lt_le_trans n d e H1 H0) in (let TMP_68 \def (lift_lref_lt n k e 
TMP_67) in (let TMP_69 \def (eq_ind_r T TMP_49 TMP_53 TMP_64 TMP_66 TMP_68) 
in (let TMP_70 \def (TLRef n) in (let TMP_71 \def (lift h d TMP_70) in (let 
TMP_72 \def (lift_lref_lt n h d H1) in (eq_ind_r T TMP_43 TMP_48 TMP_69 
TMP_71 TMP_72)))))))))))))))))))))))) in (let TMP_121 \def (\lambda (H1: (le 
d n)).(let TMP_74 \def (plus n h) in (let TMP_75 \def (TLRef TMP_74) in (let 
TMP_80 \def (\lambda (t0: T).(let TMP_76 \def (lift k e t0) in (let TMP_77 
\def (plus k h) in (let TMP_78 \def (TLRef n) in (let TMP_79 \def (lift 
TMP_77 d TMP_78) in (eq T TMP_76 TMP_79)))))) in (let TMP_81 \def (plus n h) 
in (let TMP_82 \def (plus TMP_81 k) in (let TMP_83 \def (TLRef TMP_82) in 
(let TMP_87 \def (\lambda (t0: T).(let TMP_84 \def (plus k h) in (let TMP_85 
\def (TLRef n) in (let TMP_86 \def (lift TMP_84 d TMP_85) in (eq T t0 
TMP_86))))) in (let TMP_88 \def (plus k h) in (let TMP_89 \def (plus n 
TMP_88) in (let TMP_90 \def (TLRef TMP_89) in (let TMP_94 \def (\lambda (t0: 
T).(let TMP_91 \def (plus n h) in (let TMP_92 \def (plus TMP_91 k) in (let 
TMP_93 \def (TLRef TMP_92) in (eq T TMP_93 t0))))) in (let TMP_95 \def (plus 
n h) in (let TMP_96 \def (plus TMP_95 k) in (let TMP_97 \def (plus k h) in 
(let TMP_98 \def (plus n TMP_97) in (let TMP_99 \def 
(plus_permute_2_in_3_assoc n h k) in (let TMP_100 \def (f_equal nat T TLRef 
TMP_96 TMP_98 TMP_99) in (let TMP_101 \def (plus k h) in (let TMP_102 \def 
(TLRef n) in (let TMP_103 \def (lift TMP_101 d TMP_102) in (let TMP_104 \def 
(plus k h) in (let TMP_105 \def (lift_lref_ge n TMP_104 d H1) in (let TMP_106 
\def (eq_ind_r T TMP_90 TMP_94 TMP_100 TMP_103 TMP_105) in (let TMP_107 \def 
(plus n h) in (let TMP_108 \def (TLRef TMP_107) in (let TMP_109 \def (lift k 
e TMP_108) in (let TMP_110 \def (plus n h) in (let TMP_111 \def (plus d h) in 
(let TMP_112 \def (plus n h) in (let TMP_113 \def (le_n h) in (let TMP_114 
\def (le_plus_plus d n h h H1 TMP_113) in (let TMP_115 \def (le_trans e 
TMP_111 TMP_112 H TMP_114) in (let TMP_116 \def (lift_lref_ge TMP_110 k e 
TMP_115) in (let TMP_117 \def (eq_ind_r T TMP_83 TMP_87 TMP_106 TMP_109 
TMP_116) in (let TMP_118 \def (TLRef n) in (let TMP_119 \def (lift h d 
TMP_118) in (let TMP_120 \def (lift_lref_ge n h d H1) in (eq_ind_r T TMP_75 
TMP_80 TMP_117 TMP_119 TMP_120))))))))))))))))))))))))))))))))))))))) in 
(lt_le_e n d TMP_42 TMP_73 TMP_121))))))))))))))))) in (let TMP_204 \def 
(\lambda (k: K).(\lambda (t0: T).(\lambda (H: ((\forall (h: nat).(\forall 
(k0: nat).(\forall (d: nat).(\forall (e: nat).((le e (plus d h)) \to ((le d 
e) \to (eq T (lift k0 e (lift h d t0)) (lift (plus k0 h) d 
t0)))))))))).(\lambda (t1: T).(\lambda (H0: ((\forall (h: nat).(\forall (k0: 
nat).(\forall (d: nat).(\forall (e: nat).((le e (plus d h)) \to ((le d e) \to 
(eq T (lift k0 e (lift h d t1)) (lift (plus k0 h) d t1)))))))))).(\lambda (h: 
nat).(\lambda (k0: nat).(\lambda (d: nat).(\lambda (e: nat).(\lambda (H1: (le 
e (plus d h))).(\lambda (H2: (le d e)).(let TMP_123 \def (lift h d t0) in 
(let TMP_124 \def (s k d) in (let TMP_125 \def (lift h TMP_124 t1) in (let 
TMP_126 \def (THead k TMP_123 TMP_125) in (let TMP_131 \def (\lambda (t2: 
T).(let TMP_127 \def (lift k0 e t2) in (let TMP_128 \def (plus k0 h) in (let 
TMP_129 \def (THead k t0 t1) in (let TMP_130 \def (lift TMP_128 d TMP_129) in 
(eq T TMP_127 TMP_130)))))) in (let TMP_132 \def (lift h d t0) in (let 
TMP_133 \def (lift k0 e TMP_132) in (let TMP_134 \def (s k e) in (let TMP_135 
\def (s k d) in (let TMP_136 \def (lift h TMP_135 t1) in (let TMP_137 \def 
(lift k0 TMP_134 TMP_136) in (let TMP_138 \def (THead k TMP_133 TMP_137) in 
(let TMP_142 \def (\lambda (t2: T).(let TMP_139 \def (plus k0 h) in (let 
TMP_140 \def (THead k t0 t1) in (let TMP_141 \def (lift TMP_139 d TMP_140) in 
(eq T t2 TMP_141))))) in (let TMP_143 \def (plus k0 h) in (let TMP_144 \def 
(lift TMP_143 d t0) in (let TMP_145 \def (plus k0 h) in (let TMP_146 \def (s 
k d) in (let TMP_147 \def (lift TMP_145 TMP_146 t1) in (let TMP_148 \def 
(THead k TMP_144 TMP_147) in (let TMP_156 \def (\lambda (t2: T).(let TMP_149 
\def (lift h d t0) in (let TMP_150 \def (lift k0 e TMP_149) in (let TMP_151 
\def (s k e) in (let TMP_152 \def (s k d) in (let TMP_153 \def (lift h 
TMP_152 t1) in (let TMP_154 \def (lift k0 TMP_151 TMP_153) in (let TMP_155 
\def (THead k TMP_150 TMP_154) in (eq T TMP_155 t2))))))))) in (let TMP_157 
\def (lift h d t0) in (let TMP_158 \def (lift k0 e TMP_157) in (let TMP_159 
\def (plus k0 h) in (let TMP_160 \def (lift TMP_159 d t0) in (let TMP_161 
\def (s k e) in (let TMP_162 \def (s k d) in (let TMP_163 \def (lift h 
TMP_162 t1) in (let TMP_164 \def (lift k0 TMP_161 TMP_163) in (let TMP_165 
\def (plus k0 h) in (let TMP_166 \def (s k d) in (let TMP_167 \def (lift 
TMP_165 TMP_166 t1) in (let TMP_168 \def (refl_equal K k) in (let TMP_169 
\def (H h k0 d e H1 H2) in (let TMP_170 \def (s k d) in (let TMP_171 \def (s 
k e) in (let TMP_172 \def (plus d h) in (let TMP_173 \def (s k TMP_172) in 
(let TMP_175 \def (\lambda (n: nat).(let TMP_174 \def (s k e) in (le TMP_174 
n))) in (let TMP_176 \def (plus d h) in (let TMP_177 \def (s_le k e TMP_176 
H1) in (let TMP_178 \def (s k d) in (let TMP_179 \def (plus TMP_178 h) in 
(let TMP_180 \def (s_plus k d h) in (let TMP_181 \def (eq_ind nat TMP_173 
TMP_175 TMP_177 TMP_179 TMP_180) in (let TMP_182 \def (s_le k d e H2) in (let 
TMP_183 \def (H0 h k0 TMP_170 TMP_171 TMP_181 TMP_182) in (let TMP_184 \def 
(f_equal3 K T T T THead k k TMP_158 TMP_160 TMP_164 TMP_167 TMP_168 TMP_169 
TMP_183) in (let TMP_185 \def (plus k0 h) in (let TMP_186 \def (THead k t0 
t1) in (let TMP_187 \def (lift TMP_185 d TMP_186) in (let TMP_188 \def (plus 
k0 h) in (let TMP_189 \def (lift_head k t0 t1 TMP_188 d) in (let TMP_190 \def 
(eq_ind_r T TMP_148 TMP_156 TMP_184 TMP_187 TMP_189) in (let TMP_191 \def 
(lift h d t0) in (let TMP_192 \def (s k d) in (let TMP_193 \def (lift h 
TMP_192 t1) in (let TMP_194 \def (THead k TMP_191 TMP_193) in (let TMP_195 
\def (lift k0 e TMP_194) in (let TMP_196 \def (lift h d t0) in (let TMP_197 
\def (s k d) in (let TMP_198 \def (lift h TMP_197 t1) in (let TMP_199 \def 
(lift_head k TMP_196 TMP_198 k0 e) in (let TMP_200 \def (eq_ind_r T TMP_138 
TMP_142 TMP_190 TMP_195 TMP_199) in (let TMP_201 \def (THead k t0 t1) in (let 
TMP_202 \def (lift h d TMP_201) in (let TMP_203 \def (lift_head k t0 t1 h d) 
in (eq_ind_r T TMP_126 TMP_131 TMP_200 TMP_202 
TMP_203)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
))))))) in (T_ind TMP_5 TMP_35 TMP_122 TMP_204 t))))).

theorem lift_free_sym:
 \forall (t: T).(\forall (h: nat).(\forall (k: nat).(\forall (d: 
nat).(\forall (e: nat).((le e (plus d h)) \to ((le d e) \to (eq T (lift k e 
(lift h d t)) (lift (plus h k) d t))))))))
\def
 \lambda (t: T).(\lambda (h: nat).(\lambda (k: nat).(\lambda (d: 
nat).(\lambda (e: nat).(\lambda (H: (le e (plus d h))).(\lambda (H0: (le d 
e)).(let TMP_1 \def (plus k h) in (let TMP_5 \def (\lambda (n: nat).(let 
TMP_2 \def (lift h d t) in (let TMP_3 \def (lift k e TMP_2) in (let TMP_4 
\def (lift n d t) in (eq T TMP_3 TMP_4))))) in (let TMP_6 \def (lift_free t h 
k d e H H0) in (let TMP_7 \def (plus h k) in (let TMP_8 \def (plus_sym h k) 
in (eq_ind_r nat TMP_1 TMP_5 TMP_6 TMP_7 TMP_8)))))))))))).

theorem lift_d:
 \forall (t: T).(\forall (h: nat).(\forall (k: nat).(\forall (d: 
nat).(\forall (e: nat).((le e d) \to (eq T (lift h (plus k d) (lift k e t)) 
(lift k e (lift h d t))))))))
\def
 \lambda (t: T).(let TMP_6 \def (\lambda (t0: T).(\forall (h: nat).(\forall 
(k: nat).(\forall (d: nat).(\forall (e: nat).((le e d) \to (let TMP_1 \def 
(plus k d) in (let TMP_2 \def (lift k e t0) in (let TMP_3 \def (lift h TMP_1 
TMP_2) in (let TMP_4 \def (lift h d t0) in (let TMP_5 \def (lift k e TMP_4) 
in (eq T TMP_3 TMP_5)))))))))))) in (let TMP_45 \def (\lambda (n: 
nat).(\lambda (h: nat).(\lambda (k: nat).(\lambda (d: nat).(\lambda (e: 
nat).(\lambda (_: (le e d)).(let TMP_7 \def (TSort n) in (let TMP_13 \def 
(\lambda (t0: T).(let TMP_8 \def (plus k d) in (let TMP_9 \def (lift h TMP_8 
t0) in (let TMP_10 \def (TSort n) in (let TMP_11 \def (lift h d TMP_10) in 
(let TMP_12 \def (lift k e TMP_11) in (eq T TMP_9 TMP_12))))))) in (let 
TMP_14 \def (TSort n) in (let TMP_18 \def (\lambda (t0: T).(let TMP_15 \def 
(TSort n) in (let TMP_16 \def (lift h d TMP_15) in (let TMP_17 \def (lift k e 
TMP_16) in (eq T t0 TMP_17))))) in (let TMP_19 \def (TSort n) in (let TMP_22 
\def (\lambda (t0: T).(let TMP_20 \def (TSort n) in (let TMP_21 \def (lift k 
e t0) in (eq T TMP_20 TMP_21)))) in (let TMP_23 \def (TSort n) in (let TMP_25 
\def (\lambda (t0: T).(let TMP_24 \def (TSort n) in (eq T TMP_24 t0))) in 
(let TMP_26 \def (TSort n) in (let TMP_27 \def (refl_equal T TMP_26) in (let 
TMP_28 \def (TSort n) in (let TMP_29 \def (lift k e TMP_28) in (let TMP_30 
\def (lift_sort n k e) in (let TMP_31 \def (eq_ind_r T TMP_23 TMP_25 TMP_27 
TMP_29 TMP_30) in (let TMP_32 \def (TSort n) in (let TMP_33 \def (lift h d 
TMP_32) in (let TMP_34 \def (lift_sort n h d) in (let TMP_35 \def (eq_ind_r T 
TMP_19 TMP_22 TMP_31 TMP_33 TMP_34) in (let TMP_36 \def (plus k d) in (let 
TMP_37 \def (TSort n) in (let TMP_38 \def (lift h TMP_36 TMP_37) in (let 
TMP_39 \def (plus k d) in (let TMP_40 \def (lift_sort n h TMP_39) in (let 
TMP_41 \def (eq_ind_r T TMP_14 TMP_18 TMP_35 TMP_38 TMP_40) in (let TMP_42 
\def (TSort n) in (let TMP_43 \def (lift k e TMP_42) in (let TMP_44 \def 
(lift_sort n k e) in (eq_ind_r T TMP_7 TMP_13 TMP_41 TMP_43 
TMP_44)))))))))))))))))))))))))))))))))) in (let TMP_212 \def (\lambda (n: 
nat).(\lambda (h: nat).(\lambda (k: nat).(\lambda (d: nat).(\lambda (e: 
nat).(\lambda (H: (le e d)).(let TMP_46 \def (plus k d) in (let TMP_47 \def 
(TLRef n) in (let TMP_48 \def (lift k e TMP_47) in (let TMP_49 \def (lift h 
TMP_46 TMP_48) in (let TMP_50 \def (TLRef n) in (let TMP_51 \def (lift h d 
TMP_50) in (let TMP_52 \def (lift k e TMP_51) in (let TMP_53 \def (eq T 
TMP_49 TMP_52) in (let TMP_95 \def (\lambda (H0: (lt n e)).(let H1 \def 
(lt_le_trans n e d H0 H) in (let TMP_54 \def (TLRef n) in (let TMP_60 \def 
(\lambda (t0: T).(let TMP_55 \def (plus k d) in (let TMP_56 \def (lift h 
TMP_55 t0) in (let TMP_57 \def (TLRef n) in (let TMP_58 \def (lift h d 
TMP_57) in (let TMP_59 \def (lift k e TMP_58) in (eq T TMP_56 TMP_59))))))) 
in (let TMP_61 \def (TLRef n) in (let TMP_65 \def (\lambda (t0: T).(let 
TMP_62 \def (TLRef n) in (let TMP_63 \def (lift h d TMP_62) in (let TMP_64 
\def (lift k e TMP_63) in (eq T t0 TMP_64))))) in (let TMP_66 \def (TLRef n) 
in (let TMP_69 \def (\lambda (t0: T).(let TMP_67 \def (TLRef n) in (let 
TMP_68 \def (lift k e t0) in (eq T TMP_67 TMP_68)))) in (let TMP_70 \def 
(TLRef n) in (let TMP_72 \def (\lambda (t0: T).(let TMP_71 \def (TLRef n) in 
(eq T TMP_71 t0))) in (let TMP_73 \def (TLRef n) in (let TMP_74 \def 
(refl_equal T TMP_73) in (let TMP_75 \def (TLRef n) in (let TMP_76 \def (lift 
k e TMP_75) in (let TMP_77 \def (lift_lref_lt n k e H0) in (let TMP_78 \def 
(eq_ind_r T TMP_70 TMP_72 TMP_74 TMP_76 TMP_77) in (let TMP_79 \def (TLRef n) 
in (let TMP_80 \def (lift h d TMP_79) in (let TMP_81 \def (lift_lref_lt n h d 
H1) in (let TMP_82 \def (eq_ind_r T TMP_66 TMP_69 TMP_78 TMP_80 TMP_81) in 
(let TMP_83 \def (plus k d) in (let TMP_84 \def (TLRef n) in (let TMP_85 \def 
(lift h TMP_83 TMP_84) in (let TMP_86 \def (plus k d) in (let TMP_87 \def 
(plus k d) in (let TMP_88 \def (le_plus_r k d) in (let TMP_89 \def 
(lt_le_trans n d TMP_87 H1 TMP_88) in (let TMP_90 \def (lift_lref_lt n h 
TMP_86 TMP_89) in (let TMP_91 \def (eq_ind_r T TMP_61 TMP_65 TMP_82 TMP_85 
TMP_90) in (let TMP_92 \def (TLRef n) in (let TMP_93 \def (lift k e TMP_92) 
in (let TMP_94 \def (lift_lref_lt n k e H0) in (eq_ind_r T TMP_54 TMP_60 
TMP_91 TMP_93 TMP_94))))))))))))))))))))))))))))))))) in (let TMP_211 \def 
(\lambda (H0: (le e n)).(let TMP_96 \def (plus n k) in (let TMP_97 \def 
(TLRef TMP_96) in (let TMP_103 \def (\lambda (t0: T).(let TMP_98 \def (plus k 
d) in (let TMP_99 \def (lift h TMP_98 t0) in (let TMP_100 \def (TLRef n) in 
(let TMP_101 \def (lift h d TMP_100) in (let TMP_102 \def (lift k e TMP_101) 
in (eq T TMP_99 TMP_102))))))) in (let TMP_104 \def (plus d k) in (let 
TMP_111 \def (\lambda (n0: nat).(let TMP_105 \def (plus n k) in (let TMP_106 
\def (TLRef TMP_105) in (let TMP_107 \def (lift h n0 TMP_106) in (let TMP_108 
\def (TLRef n) in (let TMP_109 \def (lift h d TMP_108) in (let TMP_110 \def 
(lift k e TMP_109) in (eq T TMP_107 TMP_110)))))))) in (let TMP_112 \def 
(plus d k) in (let TMP_113 \def (plus n k) in (let TMP_114 \def (TLRef 
TMP_113) in (let TMP_115 \def (lift h TMP_112 TMP_114) in (let TMP_116 \def 
(TLRef n) in (let TMP_117 \def (lift h d TMP_116) in (let TMP_118 \def (lift 
k e TMP_117) in (let TMP_119 \def (eq T TMP_115 TMP_118) in (let TMP_155 \def 
(\lambda (H1: (lt n d)).(let TMP_120 \def (plus n k) in (let TMP_121 \def 
(TLRef TMP_120) in (let TMP_125 \def (\lambda (t0: T).(let TMP_122 \def 
(TLRef n) in (let TMP_123 \def (lift h d TMP_122) in (let TMP_124 \def (lift 
k e TMP_123) in (eq T t0 TMP_124))))) in (let TMP_126 \def (TLRef n) in (let 
TMP_130 \def (\lambda (t0: T).(let TMP_127 \def (plus n k) in (let TMP_128 
\def (TLRef TMP_127) in (let TMP_129 \def (lift k e t0) in (eq T TMP_128 
TMP_129))))) in (let TMP_131 \def (plus n k) in (let TMP_132 \def (TLRef 
TMP_131) in (let TMP_135 \def (\lambda (t0: T).(let TMP_133 \def (plus n k) 
in (let TMP_134 \def (TLRef TMP_133) in (eq T TMP_134 t0)))) in (let TMP_136 
\def (plus n k) in (let TMP_137 \def (TLRef TMP_136) in (let TMP_138 \def 
(refl_equal T TMP_137) in (let TMP_139 \def (TLRef n) in (let TMP_140 \def 
(lift k e TMP_139) in (let TMP_141 \def (lift_lref_ge n k e H0) in (let 
TMP_142 \def (eq_ind_r T TMP_132 TMP_135 TMP_138 TMP_140 TMP_141) in (let 
TMP_143 \def (TLRef n) in (let TMP_144 \def (lift h d TMP_143) in (let 
TMP_145 \def (lift_lref_lt n h d H1) in (let TMP_146 \def (eq_ind_r T TMP_126 
TMP_130 TMP_142 TMP_144 TMP_145) in (let TMP_147 \def (plus d k) in (let 
TMP_148 \def (plus n k) in (let TMP_149 \def (TLRef TMP_148) in (let TMP_150 
\def (lift h TMP_147 TMP_149) in (let TMP_151 \def (plus n k) in (let TMP_152 
\def (plus d k) in (let TMP_153 \def (lt_reg_r n d k H1) in (let TMP_154 \def 
(lift_lref_lt TMP_151 h TMP_152 TMP_153) in (eq_ind_r T TMP_121 TMP_125 
TMP_146 TMP_150 TMP_154))))))))))))))))))))))))))))) in (let TMP_203 \def 
(\lambda (H1: (le d n)).(let TMP_156 \def (plus n k) in (let TMP_157 \def 
(plus TMP_156 h) in (let TMP_158 \def (TLRef TMP_157) in (let TMP_162 \def 
(\lambda (t0: T).(let TMP_159 \def (TLRef n) in (let TMP_160 \def (lift h d 
TMP_159) in (let TMP_161 \def (lift k e TMP_160) in (eq T t0 TMP_161))))) in 
(let TMP_163 \def (plus n h) in (let TMP_164 \def (TLRef TMP_163) in (let 
TMP_169 \def (\lambda (t0: T).(let TMP_165 \def (plus n k) in (let TMP_166 
\def (plus TMP_165 h) in (let TMP_167 \def (TLRef TMP_166) in (let TMP_168 
\def (lift k e t0) in (eq T TMP_167 TMP_168)))))) in (let TMP_170 \def (plus 
n h) in (let TMP_171 \def (plus TMP_170 k) in (let TMP_172 \def (TLRef 
TMP_171) in (let TMP_176 \def (\lambda (t0: T).(let TMP_173 \def (plus n k) 
in (let TMP_174 \def (plus TMP_173 h) in (let TMP_175 \def (TLRef TMP_174) in 
(eq T TMP_175 t0))))) in (let TMP_177 \def (plus n k) in (let TMP_178 \def 
(plus TMP_177 h) in (let TMP_179 \def (plus n h) in (let TMP_180 \def (plus 
TMP_179 k) in (let TMP_181 \def (plus_permute_2_in_3 n k h) in (let TMP_182 
\def (f_equal nat T TLRef TMP_178 TMP_180 TMP_181) in (let TMP_183 \def (plus 
n h) in (let TMP_184 \def (TLRef TMP_183) in (let TMP_185 \def (lift k e 
TMP_184) in (let TMP_186 \def (plus n h) in (let TMP_187 \def (le_plus_trans 
e n h H0) in (let TMP_188 \def (lift_lref_ge TMP_186 k e TMP_187) in (let 
TMP_189 \def (eq_ind_r T TMP_172 TMP_176 TMP_182 TMP_185 TMP_188) in (let 
TMP_190 \def (TLRef n) in (let TMP_191 \def (lift h d TMP_190) in (let 
TMP_192 \def (lift_lref_ge n h d H1) in (let TMP_193 \def (eq_ind_r T TMP_164 
TMP_169 TMP_189 TMP_191 TMP_192) in (let TMP_194 \def (plus d k) in (let 
TMP_195 \def (plus n k) in (let TMP_196 \def (TLRef TMP_195) in (let TMP_197 
\def (lift h TMP_194 TMP_196) in (let TMP_198 \def (plus n k) in (let TMP_199 
\def (plus d k) in (let TMP_200 \def (le_n k) in (let TMP_201 \def 
(le_plus_plus d n k k H1 TMP_200) in (let TMP_202 \def (lift_lref_ge TMP_198 
h TMP_199 TMP_201) in (eq_ind_r T TMP_158 TMP_162 TMP_193 TMP_197 
TMP_202))))))))))))))))))))))))))))))))))))))) in (let TMP_204 \def (lt_le_e 
n d TMP_119 TMP_155 TMP_203) in (let TMP_205 \def (plus k d) in (let TMP_206 
\def (plus_sym k d) in (let TMP_207 \def (eq_ind_r nat TMP_104 TMP_111 
TMP_204 TMP_205 TMP_206) in (let TMP_208 \def (TLRef n) in (let TMP_209 \def 
(lift k e TMP_208) in (let TMP_210 \def (lift_lref_ge n k e H0) in (eq_ind_r 
T TMP_97 TMP_103 TMP_207 TMP_209 TMP_210)))))))))))))))))))))))) in (lt_le_e 
n e TMP_53 TMP_95 TMP_211))))))))))))))))) in (let TMP_339 \def (\lambda (k: 
K).(\lambda (t0: T).(\lambda (H: ((\forall (h: nat).(\forall (k0: 
nat).(\forall (d: nat).(\forall (e: nat).((le e d) \to (eq T (lift h (plus k0 
d) (lift k0 e t0)) (lift k0 e (lift h d t0)))))))))).(\lambda (t1: 
T).(\lambda (H0: ((\forall (h: nat).(\forall (k0: nat).(\forall (d: 
nat).(\forall (e: nat).((le e d) \to (eq T (lift h (plus k0 d) (lift k0 e 
t1)) (lift k0 e (lift h d t1)))))))))).(\lambda (h: nat).(\lambda (k0: 
nat).(\lambda (d: nat).(\lambda (e: nat).(\lambda (H1: (le e d)).(let TMP_213 
\def (lift k0 e t0) in (let TMP_214 \def (s k e) in (let TMP_215 \def (lift 
k0 TMP_214 t1) in (let TMP_216 \def (THead k TMP_213 TMP_215) in (let TMP_222 
\def (\lambda (t2: T).(let TMP_217 \def (plus k0 d) in (let TMP_218 \def 
(lift h TMP_217 t2) in (let TMP_219 \def (THead k t0 t1) in (let TMP_220 \def 
(lift h d TMP_219) in (let TMP_221 \def (lift k0 e TMP_220) in (eq T TMP_218 
TMP_221))))))) in (let TMP_223 \def (plus k0 d) in (let TMP_224 \def (lift k0 
e t0) in (let TMP_225 \def (lift h TMP_223 TMP_224) in (let TMP_226 \def 
(plus k0 d) in (let TMP_227 \def (s k TMP_226) in (let TMP_228 \def (s k e) 
in (let TMP_229 \def (lift k0 TMP_228 t1) in (let TMP_230 \def (lift h 
TMP_227 TMP_229) in (let TMP_231 \def (THead k TMP_225 TMP_230) in (let 
TMP_235 \def (\lambda (t2: T).(let TMP_232 \def (THead k t0 t1) in (let 
TMP_233 \def (lift h d TMP_232) in (let TMP_234 \def (lift k0 e TMP_233) in 
(eq T t2 TMP_234))))) in (let TMP_236 \def (lift h d t0) in (let TMP_237 \def 
(s k d) in (let TMP_238 \def (lift h TMP_237 t1) in (let TMP_239 \def (THead 
k TMP_236 TMP_238) in (let TMP_250 \def (\lambda (t2: T).(let TMP_240 \def 
(plus k0 d) in (let TMP_241 \def (lift k0 e t0) in (let TMP_242 \def (lift h 
TMP_240 TMP_241) in (let TMP_243 \def (plus k0 d) in (let TMP_244 \def (s k 
TMP_243) in (let TMP_245 \def (s k e) in (let TMP_246 \def (lift k0 TMP_245 
t1) in (let TMP_247 \def (lift h TMP_244 TMP_246) in (let TMP_248 \def (THead 
k TMP_242 TMP_247) in (let TMP_249 \def (lift k0 e t2) in (eq T TMP_248 
TMP_249)))))))))))) in (let TMP_251 \def (lift h d t0) in (let TMP_252 \def 
(lift k0 e TMP_251) in (let TMP_253 \def (s k e) in (let TMP_254 \def (s k d) 
in (let TMP_255 \def (lift h TMP_254 t1) in (let TMP_256 \def (lift k0 
TMP_253 TMP_255) in (let TMP_257 \def (THead k TMP_252 TMP_256) in (let 
TMP_267 \def (\lambda (t2: T).(let TMP_258 \def (plus k0 d) in (let TMP_259 
\def (lift k0 e t0) in (let TMP_260 \def (lift h TMP_258 TMP_259) in (let 
TMP_261 \def (plus k0 d) in (let TMP_262 \def (s k TMP_261) in (let TMP_263 
\def (s k e) in (let TMP_264 \def (lift k0 TMP_263 t1) in (let TMP_265 \def 
(lift h TMP_262 TMP_264) in (let TMP_266 \def (THead k TMP_260 TMP_265) in 
(eq T TMP_266 t2))))))))))) in (let TMP_268 \def (s k d) in (let TMP_269 \def 
(plus k0 TMP_268) in (let TMP_284 \def (\lambda (n: nat).(let TMP_270 \def 
(plus k0 d) in (let TMP_271 \def (lift k0 e t0) in (let TMP_272 \def (lift h 
TMP_270 TMP_271) in (let TMP_273 \def (s k e) in (let TMP_274 \def (lift k0 
TMP_273 t1) in (let TMP_275 \def (lift h n TMP_274) in (let TMP_276 \def 
(THead k TMP_272 TMP_275) in (let TMP_277 \def (lift h d t0) in (let TMP_278 
\def (lift k0 e TMP_277) in (let TMP_279 \def (s k e) in (let TMP_280 \def (s 
k d) in (let TMP_281 \def (lift h TMP_280 t1) in (let TMP_282 \def (lift k0 
TMP_279 TMP_281) in (let TMP_283 \def (THead k TMP_278 TMP_282) in (eq T 
TMP_276 TMP_283)))))))))))))))) in (let TMP_285 \def (plus k0 d) in (let 
TMP_286 \def (lift k0 e t0) in (let TMP_287 \def (lift h TMP_285 TMP_286) in 
(let TMP_288 \def (lift h d t0) in (let TMP_289 \def (lift k0 e TMP_288) in 
(let TMP_290 \def (s k d) in (let TMP_291 \def (plus k0 TMP_290) in (let 
TMP_292 \def (s k e) in (let TMP_293 \def (lift k0 TMP_292 t1) in (let 
TMP_294 \def (lift h TMP_291 TMP_293) in (let TMP_295 \def (s k e) in (let 
TMP_296 \def (s k d) in (let TMP_297 \def (lift h TMP_296 t1) in (let TMP_298 
\def (lift k0 TMP_295 TMP_297) in (let TMP_299 \def (refl_equal K k) in (let 
TMP_300 \def (H h k0 d e H1) in (let TMP_301 \def (s k d) in (let TMP_302 
\def (s k e) in (let TMP_303 \def (s_le k e d H1) in (let TMP_304 \def (H0 h 
k0 TMP_301 TMP_302 TMP_303) in (let TMP_305 \def (f_equal3 K T T T THead k k 
TMP_287 TMP_289 TMP_294 TMP_298 TMP_299 TMP_300 TMP_304) in (let TMP_306 \def 
(plus k0 d) in (let TMP_307 \def (s k TMP_306) in (let TMP_308 \def 
(s_plus_sym k k0 d) in (let TMP_309 \def (eq_ind_r nat TMP_269 TMP_284 
TMP_305 TMP_307 TMP_308) in (let TMP_310 \def (lift h d t0) in (let TMP_311 
\def (s k d) in (let TMP_312 \def (lift h TMP_311 t1) in (let TMP_313 \def 
(THead k TMP_310 TMP_312) in (let TMP_314 \def (lift k0 e TMP_313) in (let 
TMP_315 \def (lift h d t0) in (let TMP_316 \def (s k d) in (let TMP_317 \def 
(lift h TMP_316 t1) in (let TMP_318 \def (lift_head k TMP_315 TMP_317 k0 e) 
in (let TMP_319 \def (eq_ind_r T TMP_257 TMP_267 TMP_309 TMP_314 TMP_318) in 
(let TMP_320 \def (THead k t0 t1) in (let TMP_321 \def (lift h d TMP_320) in 
(let TMP_322 \def (lift_head k t0 t1 h d) in (let TMP_323 \def (eq_ind_r T 
TMP_239 TMP_250 TMP_319 TMP_321 TMP_322) in (let TMP_324 \def (plus k0 d) in 
(let TMP_325 \def (lift k0 e t0) in (let TMP_326 \def (s k e) in (let TMP_327 
\def (lift k0 TMP_326 t1) in (let TMP_328 \def (THead k TMP_325 TMP_327) in 
(let TMP_329 \def (lift h TMP_324 TMP_328) in (let TMP_330 \def (lift k0 e 
t0) in (let TMP_331 \def (s k e) in (let TMP_332 \def (lift k0 TMP_331 t1) in 
(let TMP_333 \def (plus k0 d) in (let TMP_334 \def (lift_head k TMP_330 
TMP_332 h TMP_333) in (let TMP_335 \def (eq_ind_r T TMP_231 TMP_235 TMP_323 
TMP_329 TMP_334) in (let TMP_336 \def (THead k t0 t1) in (let TMP_337 \def 
(lift k0 e TMP_336) in (let TMP_338 \def (lift_head k t0 t1 k0 e) in 
(eq_ind_r T TMP_216 TMP_222 TMP_335 TMP_337 
TMP_338)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
))))))))))))))))))))))))) in (T_ind TMP_6 TMP_45 TMP_212 TMP_339 t))))).

