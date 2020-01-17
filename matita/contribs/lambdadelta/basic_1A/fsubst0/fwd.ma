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

include "basic_1A/fsubst0/defs.ma".

implied lemma fsubst0_ind:
 \forall (i: nat).(\forall (v: T).(\forall (c1: C).(\forall (t1: T).(\forall 
(P: ((C \to (T \to Prop)))).(((\forall (t2: T).((subst0 i v t1 t2) \to (P c1 
t2)))) \to (((\forall (c2: C).((csubst0 i v c1 c2) \to (P c2 t1)))) \to 
(((\forall (t2: T).((subst0 i v t1 t2) \to (\forall (c2: C).((csubst0 i v c1 
c2) \to (P c2 t2)))))) \to (\forall (c: C).(\forall (t: T).((fsubst0 i v c1 
t1 c t) \to (P c t)))))))))))
\def
 \lambda (i: nat).(\lambda (v: T).(\lambda (c1: C).(\lambda (t1: T).(\lambda 
(P: ((C \to (T \to Prop)))).(\lambda (f: ((\forall (t2: T).((subst0 i v t1 
t2) \to (P c1 t2))))).(\lambda (f0: ((\forall (c2: C).((csubst0 i v c1 c2) 
\to (P c2 t1))))).(\lambda (f1: ((\forall (t2: T).((subst0 i v t1 t2) \to 
(\forall (c2: C).((csubst0 i v c1 c2) \to (P c2 t2))))))).(\lambda (c: 
C).(\lambda (t: T).(\lambda (f2: (fsubst0 i v c1 t1 c t)).(match f2 with 
[(fsubst0_snd x x0) \Rightarrow (f x x0) | (fsubst0_fst x x0) \Rightarrow (f0 
x x0) | (fsubst0_both x x0 x1 x2) \Rightarrow (f1 x x0 x1 x2)]))))))))))).

lemma fsubst0_gen_base:
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

