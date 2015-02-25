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

include "basic_1/pr3/defs.ma".

include "basic_1/pr1/fwd.ma".

theorem pr3_pr1:
 \forall (t1: T).(\forall (t2: T).((pr1 t1 t2) \to (\forall (c: C).(pr3 c t1 
t2))))
\def
 \lambda (t1: T).(\lambda (t2: T).(\lambda (H: (pr1 t1 t2)).(let TMP_1 \def 
(\lambda (t: T).(\lambda (t0: T).(\forall (c: C).(pr3 c t t0)))) in (let 
TMP_2 \def (\lambda (t: T).(\lambda (c: C).(pr3_refl c t))) in (let TMP_5 
\def (\lambda (t0: T).(\lambda (t3: T).(\lambda (H0: (pr0 t3 t0)).(\lambda 
(t4: T).(\lambda (_: (pr1 t0 t4)).(\lambda (H2: ((\forall (c: C).(pr3 c t0 
t4)))).(\lambda (c: C).(let TMP_3 \def (pr2_free c t3 t0 H0) in (let TMP_4 
\def (H2 c) in (pr3_sing c t0 t3 TMP_3 t4 TMP_4)))))))))) in (pr1_ind TMP_1 
TMP_2 TMP_5 t1 t2 H)))))).

