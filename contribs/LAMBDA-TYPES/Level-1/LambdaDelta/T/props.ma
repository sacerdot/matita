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

set "baseuri" "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/T/props".

include "T/defs.ma".

theorem not_abbr_abst:
 not (eq B Abbr Abst)
\def
 \lambda (H: (eq B Abbr Abst)).(let H0 \def (eq_ind B Abbr (\lambda (ee: 
B).(match ee in B return (\lambda (_: B).Prop) with [Abbr \Rightarrow True | 
Abst \Rightarrow False | Void \Rightarrow False])) I Abst H) in (False_ind 
False H0)).

theorem not_void_abst:
 not (eq B Void Abst)
\def
 \lambda (H: (eq B Void Abst)).(let H0 \def (eq_ind B Void (\lambda (ee: 
B).(match ee in B return (\lambda (_: B).Prop) with [Abbr \Rightarrow False | 
Abst \Rightarrow False | Void \Rightarrow True])) I Abst H) in (False_ind 
False H0)).

theorem thead_x_y_y:
 \forall (k: K).(\forall (v: T).(\forall (t: T).((eq T (THead k v t) t) \to 
(\forall (P: Prop).P))))
\def
 \lambda (k: K).(\lambda (v: T).(\lambda (t: T).(T_ind (\lambda (t0: T).((eq 
T (THead k v t0) t0) \to (\forall (P: Prop).P))) (\lambda (n: nat).(\lambda 
(H: (eq T (THead k v (TSort n)) (TSort n))).(\lambda (P: Prop).(let H0 \def 
(eq_ind T (THead k v (TSort n)) (\lambda (ee: T).(match ee in T return 
(\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow False | (THead _ _ _) \Rightarrow True])) I (TSort n) H) in 
(False_ind P H0))))) (\lambda (n: nat).(\lambda (H: (eq T (THead k v (TLRef 
n)) (TLRef n))).(\lambda (P: Prop).(let H0 \def (eq_ind T (THead k v (TLRef 
n)) (\lambda (ee: T).(match ee in T return (\lambda (_: T).Prop) with [(TSort 
_) \Rightarrow False | (TLRef _) \Rightarrow False | (THead _ _ _) 
\Rightarrow True])) I (TLRef n) H) in (False_ind P H0))))) (\lambda (k0: 
K).(\lambda (t0: T).(\lambda (_: (((eq T (THead k v t0) t0) \to (\forall (P: 
Prop).P)))).(\lambda (t1: T).(\lambda (H0: (((eq T (THead k v t1) t1) \to 
(\forall (P: Prop).P)))).(\lambda (H1: (eq T (THead k v (THead k0 t0 t1)) 
(THead k0 t0 t1))).(\lambda (P: Prop).(let H2 \def (f_equal T K (\lambda (e: 
T).(match e in T return (\lambda (_: T).K) with [(TSort _) \Rightarrow k | 
(TLRef _) \Rightarrow k | (THead k _ _) \Rightarrow k])) (THead k v (THead k0 
t0 t1)) (THead k0 t0 t1) H1) in ((let H3 \def (f_equal T T (\lambda (e: 
T).(match e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow v | 
(TLRef _) \Rightarrow v | (THead _ t _) \Rightarrow t])) (THead k v (THead k0 
t0 t1)) (THead k0 t0 t1) H1) in ((let H4 \def (f_equal T T (\lambda (e: 
T).(match e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow (THead 
k0 t0 t1) | (TLRef _) \Rightarrow (THead k0 t0 t1) | (THead _ _ t) 
\Rightarrow t])) (THead k v (THead k0 t0 t1)) (THead k0 t0 t1) H1) in 
(\lambda (H5: (eq T v t0)).(\lambda (H6: (eq K k k0)).(let H7 \def (eq_ind T 
v (\lambda (t: T).((eq T (THead k t t1) t1) \to (\forall (P: Prop).P))) H0 t0 
H5) in (let H8 \def (eq_ind K k (\lambda (k: K).((eq T (THead k t0 t1) t1) 
\to (\forall (P: Prop).P))) H7 k0 H6) in (H8 H4 P)))))) H3)) H2))))))))) t))).

