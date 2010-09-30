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

include "Basic-1/csubv/defs.ma".

include "Basic-1/T/props.ma".

theorem csubv_bind_same:
 \forall (c1: C).(\forall (c2: C).((csubv c1 c2) \to (\forall (b: B).(\forall 
(v1: T).(\forall (v2: T).(csubv (CHead c1 (Bind b) v1) (CHead c2 (Bind b) 
v2)))))))
\def
 \lambda (c1: C).(\lambda (c2: C).(\lambda (H: (csubv c1 c2)).(\lambda (b: 
B).(B_ind (\lambda (b0: B).(\forall (v1: T).(\forall (v2: T).(csubv (CHead c1 
(Bind b0) v1) (CHead c2 (Bind b0) v2))))) (\lambda (v1: T).(\lambda (v2: 
T).(csubv_bind c1 c2 H Abbr (\lambda (H0: (eq B Abbr Void)).(not_abbr_void 
H0)) Abbr v1 v2))) (\lambda (v1: T).(\lambda (v2: T).(csubv_bind c1 c2 H Abst 
(sym_not_eq B Void Abst not_void_abst) Abst v1 v2))) (\lambda (v1: 
T).(\lambda (v2: T).(csubv_void c1 c2 H v1 v2))) b)))).
(* COMMENTS
Initial nodes: 121
END *)

theorem csubv_refl:
 \forall (c: C).(csubv c c)
\def
 \lambda (c: C).(C_ind (\lambda (c0: C).(csubv c0 c0)) (\lambda (n: 
nat).(csubv_sort n)) (\lambda (c0: C).(\lambda (H: (csubv c0 c0)).(\lambda 
(k: K).(K_ind (\lambda (k0: K).(\forall (t: T).(csubv (CHead c0 k0 t) (CHead 
c0 k0 t)))) (\lambda (b: B).(\lambda (t: T).(csubv_bind_same c0 c0 H b t t))) 
(\lambda (f: F).(\lambda (t: T).(csubv_flat c0 c0 H f f t t))) k)))) c).
(* COMMENTS
Initial nodes: 93
END *)

