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

include "basic_1/pc3/defs.ma".

include "basic_1/pc1/defs.ma".

include "basic_1/pr3/pr1.ma".

theorem pc3_pc1:
 \forall (t1: T).(\forall (t2: T).((pc1 t1 t2) \to (\forall (c: C).(pc3 c t1 
t2))))
\def
 \lambda (t1: T).(\lambda (t2: T).(\lambda (H: (pc1 t1 t2)).(\lambda (c: 
C).(let H0 \def H in (let TMP_1 \def (\lambda (t: T).(pr1 t1 t)) in (let 
TMP_2 \def (\lambda (t: T).(pr1 t2 t)) in (let TMP_3 \def (pc3 c t1 t2) in 
(let TMP_8 \def (\lambda (x: T).(\lambda (H1: (pr1 t1 x)).(\lambda (H2: (pr1 
t2 x)).(let TMP_4 \def (\lambda (t: T).(pr3 c t1 t)) in (let TMP_5 \def 
(\lambda (t: T).(pr3 c t2 t)) in (let TMP_6 \def (pr3_pr1 t1 x H1 c) in (let 
TMP_7 \def (pr3_pr1 t2 x H2 c) in (ex_intro2 T TMP_4 TMP_5 x TMP_6 
TMP_7)))))))) in (ex2_ind T TMP_1 TMP_2 TMP_3 TMP_8 H0))))))))).

