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

include "Basic-1/fsubst0/defs.ma".

theorem fsubst0_gen_base:
 \forall (c1: C).(\forall (c2: C).(\forall (t1: T).(\forall (t2: T).(\forall 
(v: T).(\forall (i: nat).((fsubst0 i v c1 t1 c2 t2) \to (or3 (land (eq C c1 
c2) (subst0 i v t1 t2)) (land (eq T t1 t2) (csubst0 i v c1 c2)) (land (subst0 
i v t1 t2) (csubst0 i v c1 c2)))))))))
\def
 \lambda (c1: C).(\lambda (c2: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda 
(v: T).(\lambda (i: nat).(\lambda (H: (fsubst0 i v c1 t1 c2 t2)).(fsubst0_ind 
i v c1 t1 (\lambda (c: C).(\lambda (t: T).(or3 (land (eq C c1 c) (subst0 i v 
t1 t)) (land (eq T t1 t) (csubst0 i v c1 c)) (land (subst0 i v t1 t) (csubst0 
i v c1 c))))) (\lambda (t0: T).(\lambda (H0: (subst0 i v t1 t0)).(or3_intro0 
(land (eq C c1 c1) (subst0 i v t1 t0)) (land (eq T t1 t0) (csubst0 i v c1 
c1)) (land (subst0 i v t1 t0) (csubst0 i v c1 c1)) (conj (eq C c1 c1) (subst0 
i v t1 t0) (refl_equal C c1) H0)))) (\lambda (c0: C).(\lambda (H0: (csubst0 i 
v c1 c0)).(or3_intro1 (land (eq C c1 c0) (subst0 i v t1 t1)) (land (eq T t1 
t1) (csubst0 i v c1 c0)) (land (subst0 i v t1 t1) (csubst0 i v c1 c0)) (conj 
(eq T t1 t1) (csubst0 i v c1 c0) (refl_equal T t1) H0)))) (\lambda (t0: 
T).(\lambda (H0: (subst0 i v t1 t0)).(\lambda (c0: C).(\lambda (H1: (csubst0 
i v c1 c0)).(or3_intro2 (land (eq C c1 c0) (subst0 i v t1 t0)) (land (eq T t1 
t0) (csubst0 i v c1 c0)) (land (subst0 i v t1 t0) (csubst0 i v c1 c0)) (conj 
(subst0 i v t1 t0) (csubst0 i v c1 c0) H0 H1)))))) c2 t2 H))))))).
(* COMMENTS
Initial nodes: 431
END *)

