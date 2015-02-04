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

include "basic_1/T/defs.ma".

let rec T_rect (P: (T \to Type[0])) (f: (\forall (n: nat).(P (TSort n)))) 
(f0: (\forall (n: nat).(P (TLRef n)))) (f1: (\forall (k: K).(\forall (t: 
T).((P t) \to (\forall (t0: T).((P t0) \to (P (THead k t t0)))))))) (t: T) on 
t: P t \def match t with [(TSort n) \Rightarrow (f n) | (TLRef n) \Rightarrow 
(f0 n) | (THead k t0 t1) \Rightarrow (let TMP_1 \def ((T_rect P f f0 f1) t0) 
in (let TMP_2 \def ((T_rect P f f0 f1) t1) in (f1 k t0 TMP_1 t1 TMP_2)))].

theorem T_ind:
 \forall (P: ((T \to Prop))).(((\forall (n: nat).(P (TSort n)))) \to 
(((\forall (n: nat).(P (TLRef n)))) \to (((\forall (k: K).(\forall (t: T).((P 
t) \to (\forall (t0: T).((P t0) \to (P (THead k t t0)))))))) \to (\forall (t: 
T).(P t)))))
\def
 \lambda (P: ((T \to Prop))).(T_rect P).

theorem thead_x_y_y:
 \forall (k: K).(\forall (v: T).(\forall (t: T).((eq T (THead k v t) t) \to 
(\forall (P: Prop).P))))
\def
 \lambda (k: K).(\lambda (v: T).(\lambda (t: T).(let TMP_1 \def (\lambda (t0: 
T).((eq T (THead k v t0) t0) \to (\forall (P: Prop).P))) in (let TMP_6 \def 
(\lambda (n: nat).(\lambda (H: (eq T (THead k v (TSort n)) (TSort 
n))).(\lambda (P: Prop).(let TMP_2 \def (TSort n) in (let TMP_3 \def (THead k 
v TMP_2) in (let TMP_4 \def (\lambda (ee: T).(match ee with [(TSort _) 
\Rightarrow False | (TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow 
True])) in (let TMP_5 \def (TSort n) in (let H0 \def (eq_ind T TMP_3 TMP_4 I 
TMP_5 H) in (False_ind P H0))))))))) in (let TMP_11 \def (\lambda (n: 
nat).(\lambda (H: (eq T (THead k v (TLRef n)) (TLRef n))).(\lambda (P: 
Prop).(let TMP_7 \def (TLRef n) in (let TMP_8 \def (THead k v TMP_7) in (let 
TMP_9 \def (\lambda (ee: T).(match ee with [(TSort _) \Rightarrow False | 
(TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow True])) in (let 
TMP_10 \def (TLRef n) in (let H0 \def (eq_ind T TMP_8 TMP_9 I TMP_10 H) in 
(False_ind P H0))))))))) in (let TMP_28 \def (\lambda (k0: K).(\lambda (t0: 
T).(\lambda (_: (((eq T (THead k v t0) t0) \to (\forall (P: 
Prop).P)))).(\lambda (t1: T).(\lambda (H0: (((eq T (THead k v t1) t1) \to 
(\forall (P: Prop).P)))).(\lambda (H1: (eq T (THead k v (THead k0 t0 t1)) 
(THead k0 t0 t1))).(\lambda (P: Prop).(let TMP_12 \def (\lambda (e: T).(match 
e with [(TSort _) \Rightarrow k | (TLRef _) \Rightarrow k | (THead k1 _ _) 
\Rightarrow k1])) in (let TMP_13 \def (THead k0 t0 t1) in (let TMP_14 \def 
(THead k v TMP_13) in (let TMP_15 \def (THead k0 t0 t1) in (let H2 \def 
(f_equal T K TMP_12 TMP_14 TMP_15 H1) in (let TMP_16 \def (\lambda (e: 
T).(match e with [(TSort _) \Rightarrow v | (TLRef _) \Rightarrow v | (THead 
_ t2 _) \Rightarrow t2])) in (let TMP_17 \def (THead k0 t0 t1) in (let TMP_18 
\def (THead k v TMP_17) in (let TMP_19 \def (THead k0 t0 t1) in (let H3 \def 
(f_equal T T TMP_16 TMP_18 TMP_19 H1) in (let TMP_20 \def (\lambda (e: 
T).(match e with [(TSort _) \Rightarrow (THead k0 t0 t1) | (TLRef _) 
\Rightarrow (THead k0 t0 t1) | (THead _ _ t2) \Rightarrow t2])) in (let 
TMP_21 \def (THead k0 t0 t1) in (let TMP_22 \def (THead k v TMP_21) in (let 
TMP_23 \def (THead k0 t0 t1) in (let H4 \def (f_equal T T TMP_20 TMP_22 
TMP_23 H1) in (let TMP_26 \def (\lambda (H5: (eq T v t0)).(\lambda (H6: (eq K 
k k0)).(let TMP_24 \def (\lambda (t2: T).((eq T (THead k t2 t1) t1) \to 
(\forall (P0: Prop).P0))) in (let H7 \def (eq_ind T v TMP_24 H0 t0 H5) in 
(let TMP_25 \def (\lambda (k1: K).((eq T (THead k1 t0 t1) t1) \to (\forall 
(P0: Prop).P0))) in (let H8 \def (eq_ind K k TMP_25 H7 k0 H6) in (H8 H4 
P))))))) in (let TMP_27 \def (TMP_26 H3) in (TMP_27 
H2))))))))))))))))))))))))) in (T_ind TMP_1 TMP_6 TMP_11 TMP_28 t))))))).

