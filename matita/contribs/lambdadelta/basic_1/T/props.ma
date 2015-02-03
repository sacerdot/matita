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
 \lambda (H: (eq B Abbr Abst)).(let TMP_1 \def (\lambda (ee: B).(match ee in 
B with [Abbr \Rightarrow True | Abst \Rightarrow False | Void \Rightarrow 
False])) in (let H0 \def (eq_ind B Abbr TMP_1 I Abst H) in (False_ind False 
H0))).

theorem not_void_abst:
 not (eq B Void Abst)
\def
 \lambda (H: (eq B Void Abst)).(let TMP_2 \def (\lambda (ee: B).(match ee in 
B with [Abbr \Rightarrow False | Abst \Rightarrow False | Void \Rightarrow 
True])) in (let H0 \def (eq_ind B Void TMP_2 I Abst H) in (False_ind False 
H0))).

theorem not_abbr_void:
 not (eq B Abbr Void)
\def
 \lambda (H: (eq B Abbr Void)).(let TMP_3 \def (\lambda (ee: B).(match ee in 
B with [Abbr \Rightarrow True | Abst \Rightarrow False | Void \Rightarrow 
False])) in (let H0 \def (eq_ind B Abbr TMP_3 I Void H) in (False_ind False 
H0))).

theorem not_abst_void:
 not (eq B Abst Void)
\def
 \lambda (H: (eq B Abst Void)).(let TMP_4 \def (\lambda (ee: B).(match ee in 
B with [Abbr \Rightarrow False | Abst \Rightarrow True | Void \Rightarrow 
False])) in (let H0 \def (eq_ind B Abst TMP_4 I Void H) in (False_ind False 
H0))).

theorem tweight_lt:
 \forall (t: T).(lt O (tweight t))
\def
 \lambda (t: T).(let TMP_1848 \def (\lambda (t0: T).(let TMP_1847 \def 
(tweight t0) in (lt O TMP_1847))) in (let TMP_1846 \def (\lambda (_: 
nat).(let TMP_1845 \def (S O) in (le_n TMP_1845))) in (let TMP_1844 \def 
(\lambda (_: nat).(let TMP_1843 \def (S O) in (le_n TMP_1843))) in (let 
TMP_1842 \def (\lambda (_: K).(\lambda (t0: T).(\lambda (H: (lt O (tweight 
t0))).(\lambda (t1: T).(\lambda (_: (lt O (tweight t1))).(let TMP_1841 \def 
(S O) in (let TMP_1839 \def (tweight t0) in (let TMP_1838 \def (tweight t1) 
in (let TMP_1840 \def (plus TMP_1839 TMP_1838) in (let TMP_1836 \def (S O) in 
(let TMP_1835 \def (tweight t0) in (let TMP_1834 \def (tweight t1) in (let 
TMP_1837 \def (le_plus_trans TMP_1836 TMP_1835 TMP_1834 H) in (le_S TMP_1841 
TMP_1840 TMP_1837)))))))))))))) in (T_ind TMP_1848 TMP_1846 TMP_1844 TMP_1842 
t))))).

