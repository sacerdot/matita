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
 \lambda (H: (eq B Abbr Abst)).(let TMP_1 \def (\lambda (ee: B).(match ee 
with [Abbr \Rightarrow True | Abst \Rightarrow False | Void \Rightarrow 
False])) in (let H0 \def (eq_ind B Abbr TMP_1 I Abst H) in (False_ind False 
H0))).

theorem not_void_abst:
 not (eq B Void Abst)
\def
 \lambda (H: (eq B Void Abst)).(let TMP_1 \def (\lambda (ee: B).(match ee 
with [Abbr \Rightarrow False | Abst \Rightarrow False | Void \Rightarrow 
True])) in (let H0 \def (eq_ind B Void TMP_1 I Abst H) in (False_ind False 
H0))).

theorem not_abbr_void:
 not (eq B Abbr Void)
\def
 \lambda (H: (eq B Abbr Void)).(let TMP_1 \def (\lambda (ee: B).(match ee 
with [Abbr \Rightarrow True | Abst \Rightarrow False | Void \Rightarrow 
False])) in (let H0 \def (eq_ind B Abbr TMP_1 I Void H) in (False_ind False 
H0))).

theorem not_abst_void:
 not (eq B Abst Void)
\def
 \lambda (H: (eq B Abst Void)).(let TMP_1 \def (\lambda (ee: B).(match ee 
with [Abbr \Rightarrow False | Abst \Rightarrow True | Void \Rightarrow 
False])) in (let H0 \def (eq_ind B Abst TMP_1 I Void H) in (False_ind False 
H0))).

theorem tweight_lt:
 \forall (t: T).(lt O (tweight t))
\def
 \lambda (t: T).(let TMP_2 \def (\lambda (t0: T).(let TMP_1 \def (tweight t0) 
in (lt O TMP_1))) in (let TMP_4 \def (\lambda (_: nat).(let TMP_3 \def (S O) 
in (le_n TMP_3))) in (let TMP_6 \def (\lambda (_: nat).(let TMP_5 \def (S O) 
in (le_n TMP_5))) in (let TMP_15 \def (\lambda (_: K).(\lambda (t0: 
T).(\lambda (H: (lt O (tweight t0))).(\lambda (t1: T).(\lambda (_: (lt O 
(tweight t1))).(let TMP_7 \def (S O) in (let TMP_8 \def (tweight t0) in (let 
TMP_9 \def (tweight t1) in (let TMP_10 \def (plus TMP_8 TMP_9) in (let TMP_11 
\def (S O) in (let TMP_12 \def (tweight t0) in (let TMP_13 \def (tweight t1) 
in (let TMP_14 \def (le_plus_trans TMP_11 TMP_12 TMP_13 H) in (le_S TMP_7 
TMP_10 TMP_14)))))))))))))) in (T_ind TMP_2 TMP_4 TMP_6 TMP_15 t))))).

theorem tle_r:
 \forall (t: T).(tle t t)
\def
 \lambda (t: T).(let TMP_3 \def (\lambda (t0: T).(let TMP_1 \def (tweight t0) 
in (let TMP_2 \def (tweight t0) in (le TMP_1 TMP_2)))) in (let TMP_5 \def 
(\lambda (_: nat).(let TMP_4 \def (S O) in (le_n TMP_4))) in (let TMP_7 \def 
(\lambda (_: nat).(let TMP_6 \def (S O) in (le_n TMP_6))) in (let TMP_12 \def 
(\lambda (_: K).(\lambda (t0: T).(\lambda (_: (le (tweight t0) (tweight 
t0))).(\lambda (t1: T).(\lambda (_: (le (tweight t1) (tweight t1))).(let 
TMP_8 \def (tweight t0) in (let TMP_9 \def (tweight t1) in (let TMP_10 \def 
(plus TMP_8 TMP_9) in (let TMP_11 \def (S TMP_10) in (le_n TMP_11)))))))))) 
in (T_ind TMP_3 TMP_5 TMP_7 TMP_12 t))))).

