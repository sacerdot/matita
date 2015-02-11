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

include "basic_1/csubv/defs.ma".

include "basic_1/C/fwd.ma".

include "basic_1/T/props.ma".

theorem csubv_bind_same:
 \forall (c1: C).(\forall (c2: C).((csubv c1 c2) \to (\forall (b: B).(\forall 
(v1: T).(\forall (v2: T).(csubv (CHead c1 (Bind b) v1) (CHead c2 (Bind b) 
v2)))))))
\def
 \lambda (c1: C).(\lambda (c2: C).(\lambda (H: (csubv c1 c2)).(\lambda (b: 
B).(let TMP_5 \def (\lambda (b0: B).(\forall (v1: T).(\forall (v2: T).(let 
TMP_1 \def (Bind b0) in (let TMP_2 \def (CHead c1 TMP_1 v1) in (let TMP_3 
\def (Bind b0) in (let TMP_4 \def (CHead c2 TMP_3 v2) in (csubv TMP_2 
TMP_4)))))))) in (let TMP_6 \def (\lambda (v1: T).(\lambda (v2: 
T).(csubv_bind c1 c2 H Abbr not_abbr_void Abbr v1 v2))) in (let TMP_7 \def 
(\lambda (v1: T).(\lambda (v2: T).(csubv_bind c1 c2 H Abst not_abst_void Abst 
v1 v2))) in (let TMP_8 \def (\lambda (v1: T).(\lambda (v2: T).(csubv_void c1 
c2 H v1 v2))) in (B_ind TMP_5 TMP_6 TMP_7 TMP_8 b)))))))).

theorem csubv_refl:
 \forall (c: C).(csubv c c)
\def
 \lambda (c: C).(let TMP_1 \def (\lambda (c0: C).(csubv c0 c0)) in (let TMP_2 
\def (\lambda (n: nat).(csubv_sort n)) in (let TMP_8 \def (\lambda (c0: 
C).(\lambda (H: (csubv c0 c0)).(\lambda (k: K).(let TMP_5 \def (\lambda (k0: 
K).(\forall (t: T).(let TMP_3 \def (CHead c0 k0 t) in (let TMP_4 \def (CHead 
c0 k0 t) in (csubv TMP_3 TMP_4))))) in (let TMP_6 \def (\lambda (b: 
B).(\lambda (t: T).(csubv_bind_same c0 c0 H b t t))) in (let TMP_7 \def 
(\lambda (f: F).(\lambda (t: T).(csubv_flat c0 c0 H f f t t))) in (K_ind 
TMP_5 TMP_6 TMP_7 k))))))) in (C_ind TMP_1 TMP_2 TMP_8 c)))).

