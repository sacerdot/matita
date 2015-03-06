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

include "basic_1/T/fwd.ma".

theorem not_abbr_abst:
 not (eq B Abbr Abst)
\def
 \lambda (H: (eq B Abbr Abst)).(let H0 \def (eq_ind B Abbr (\lambda (ee: 
B).(match ee with [Abbr \Rightarrow True | Abst \Rightarrow False | Void 
\Rightarrow False])) I Abst H) in (False_ind False H0)).

theorem not_void_abst:
 not (eq B Void Abst)
\def
 \lambda (H: (eq B Void Abst)).(let H0 \def (eq_ind B Void (\lambda (ee: 
B).(match ee with [Abbr \Rightarrow False | Abst \Rightarrow False | Void 
\Rightarrow True])) I Abst H) in (False_ind False H0)).

theorem not_abbr_void:
 not (eq B Abbr Void)
\def
 \lambda (H: (eq B Abbr Void)).(let H0 \def (eq_ind B Abbr (\lambda (ee: 
B).(match ee with [Abbr \Rightarrow True | Abst \Rightarrow False | Void 
\Rightarrow False])) I Void H) in (False_ind False H0)).

theorem not_abst_void:
 not (eq B Abst Void)
\def
 \lambda (H: (eq B Abst Void)).(let H0 \def (eq_ind B Abst (\lambda (ee: 
B).(match ee with [Abbr \Rightarrow False | Abst \Rightarrow True | Void 
\Rightarrow False])) I Void H) in (False_ind False H0)).

theorem tweight_lt:
 \forall (t: T).(lt O (tweight t))
\def
 \lambda (t: T).(T_ind (\lambda (t0: T).(lt O (tweight t0))) (\lambda (_: 
nat).(le_n (S O))) (\lambda (_: nat).(le_n (S O))) (\lambda (_: K).(\lambda 
(t0: T).(\lambda (H: (lt O (tweight t0))).(\lambda (t1: T).(\lambda (_: (lt O 
(tweight t1))).(le_S (S O) (plus (tweight t0) (tweight t1)) (le_plus_trans (S 
O) (tweight t0) (tweight t1) H))))))) t).

theorem tle_r:
 \forall (t: T).(tle t t)
\def
 \lambda (t: T).(T_ind (\lambda (t0: T).(le (tweight t0) (tweight t0))) 
(\lambda (_: nat).(le_n (S O))) (\lambda (_: nat).(le_n (S O))) (\lambda (_: 
K).(\lambda (t0: T).(\lambda (_: (le (tweight t0) (tweight t0))).(\lambda 
(t1: T).(\lambda (_: (le (tweight t1) (tweight t1))).(le_n (S (plus (tweight 
t0) (tweight t1))))))))) t).

