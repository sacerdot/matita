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

implied rec lemma T_rect (P: (T \to Type[0])) (f: (\forall (n: nat).(P (TSort 
n)))) (f0: (\forall (n: nat).(P (TLRef n)))) (f1: (\forall (k: K).(\forall 
(t: T).((P t) \to (\forall (t0: T).((P t0) \to (P (THead k t t0)))))))) (t: 
T) on t: P t \def match t with [(TSort n) \Rightarrow (f n) | (TLRef n) 
\Rightarrow (f0 n) | (THead k t0 t1) \Rightarrow (f1 k t0 ((T_rect P f f0 f1) 
t0) t1 ((T_rect P f f0 f1) t1))].

implied lemma T_ind:
 \forall (P: ((T \to Prop))).(((\forall (n: nat).(P (TSort n)))) \to 
(((\forall (n: nat).(P (TLRef n)))) \to (((\forall (k: K).(\forall (t: T).((P 
t) \to (\forall (t0: T).((P t0) \to (P (THead k t t0)))))))) \to (\forall (t: 
T).(P t)))))
\def
 \lambda (P: ((T \to Prop))).(T_rect P).

lemma thead_x_y_y:
 \forall (k: K).(\forall (v: T).(\forall (t: T).((eq T (THead k v t) t) \to 
(\forall (P: Prop).P))))
\def
 \lambda (k: K).(\lambda (v: T).(\lambda (t: T).(T_ind (\lambda (t0: T).((eq 
T (THead k v t0) t0) \to (\forall (P: Prop).P))) (\lambda (n: nat).(\lambda 
(H: (eq T (THead k v (TSort n)) (TSort n))).(\lambda (P: Prop).(let H0 \def 
(eq_ind T (THead k v (TSort n)) (\lambda (ee: T).(match ee with [(TSort _) 
\Rightarrow False | (TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow 
True])) I (TSort n) H) in (False_ind P H0))))) (\lambda (n: nat).(\lambda (H: 
(eq T (THead k v (TLRef n)) (TLRef n))).(\lambda (P: Prop).(let H0 \def 
(eq_ind T (THead k v (TLRef n)) (\lambda (ee: T).(match ee with [(TSort _) 
\Rightarrow False | (TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow 
True])) I (TLRef n) H) in (False_ind P H0))))) (\lambda (k0: K).(\lambda (t0: 
T).(\lambda (_: (((eq T (THead k v t0) t0) \to (\forall (P: 
Prop).P)))).(\lambda (t1: T).(\lambda (H0: (((eq T (THead k v t1) t1) \to 
(\forall (P: Prop).P)))).(\lambda (H1: (eq T (THead k v (THead k0 t0 t1)) 
(THead k0 t0 t1))).(\lambda (P: Prop).(let H2 \def (f_equal T K (\lambda (e: 
T).(match e with [(TSort _) \Rightarrow k | (TLRef _) \Rightarrow k | (THead 
k1 _ _) \Rightarrow k1])) (THead k v (THead k0 t0 t1)) (THead k0 t0 t1) H1) 
in ((let H3 \def (f_equal T T (\lambda (e: T).(match e with [(TSort _) 
\Rightarrow v | (TLRef _) \Rightarrow v | (THead _ t2 _) \Rightarrow t2])) 
(THead k v (THead k0 t0 t1)) (THead k0 t0 t1) H1) in ((let H4 \def (f_equal T 
T (\lambda (e: T).(match e with [(TSort _) \Rightarrow (THead k0 t0 t1) | 
(TLRef _) \Rightarrow (THead k0 t0 t1) | (THead _ _ t2) \Rightarrow t2])) 
(THead k v (THead k0 t0 t1)) (THead k0 t0 t1) H1) in (\lambda (H5: (eq T v 
t0)).(\lambda (H6: (eq K k k0)).(let H7 \def (eq_ind T v (\lambda (t2: 
T).((eq T (THead k t2 t1) t1) \to (\forall (P0: Prop).P0))) H0 t0 H5) in (let 
H8 \def (eq_ind K k (\lambda (k1: K).((eq T (THead k1 t0 t1) t1) \to (\forall 
(P0: Prop).P0))) H7 k0 H6) in (H8 H4 P)))))) H3)) H2))))))))) t))).

