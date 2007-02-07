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

set "baseuri" "cic:/matita/LAMBDA-TYPES/LambdaDelta-1/fsubst0/fwd".

include "fsubst0/defs.ma".

theorem fsubst0_gen_base:
 \forall (c1: C).(\forall (c2: C).(\forall (t1: T).(\forall (t2: T).(\forall 
(v: T).(\forall (i: nat).((fsubst0 i v c1 t1 c2 t2) \to (or3 (land (eq C c1 
c2) (subst0 i v t1 t2)) (land (eq T t1 t2) (csubst0 i v c1 c2)) (land (subst0 
i v t1 t2) (csubst0 i v c1 c2)))))))))
\def
 \lambda (c1: C).(\lambda (c2: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda 
(v: T).(\lambda (i: nat).(\lambda (H: (fsubst0 i v c1 t1 c2 t2)).(let H0 \def 
(match H in fsubst0 return (\lambda (c: C).(\lambda (t: T).(\lambda (_: 
(fsubst0 ? ? ? ? c t)).((eq C c c2) \to ((eq T t t2) \to (or3 (land (eq C c1 
c2) (subst0 i v t1 t2)) (land (eq T t1 t2) (csubst0 i v c1 c2)) (land (subst0 
i v t1 t2) (csubst0 i v c1 c2)))))))) with [(fsubst0_snd t0 H0) \Rightarrow 
(\lambda (H1: (eq C c1 c2)).(\lambda (H2: (eq T t0 t2)).(eq_ind C c2 (\lambda 
(c: C).((eq T t0 t2) \to ((subst0 i v t1 t0) \to (or3 (land (eq C c c2) 
(subst0 i v t1 t2)) (land (eq T t1 t2) (csubst0 i v c c2)) (land (subst0 i v 
t1 t2) (csubst0 i v c c2)))))) (\lambda (H3: (eq T t0 t2)).(eq_ind T t2 
(\lambda (t: T).((subst0 i v t1 t) \to (or3 (land (eq C c2 c2) (subst0 i v t1 
t2)) (land (eq T t1 t2) (csubst0 i v c2 c2)) (land (subst0 i v t1 t2) 
(csubst0 i v c2 c2))))) (\lambda (H4: (subst0 i v t1 t2)).(or3_intro0 (land 
(eq C c2 c2) (subst0 i v t1 t2)) (land (eq T t1 t2) (csubst0 i v c2 c2)) 
(land (subst0 i v t1 t2) (csubst0 i v c2 c2)) (conj (eq C c2 c2) (subst0 i v 
t1 t2) (refl_equal C c2) H4))) t0 (sym_eq T t0 t2 H3))) c1 (sym_eq C c1 c2 
H1) H2 H0))) | (fsubst0_fst c0 H0) \Rightarrow (\lambda (H1: (eq C c0 
c2)).(\lambda (H2: (eq T t1 t2)).(eq_ind C c2 (\lambda (c: C).((eq T t1 t2) 
\to ((csubst0 i v c1 c) \to (or3 (land (eq C c1 c2) (subst0 i v t1 t2)) (land 
(eq T t1 t2) (csubst0 i v c1 c2)) (land (subst0 i v t1 t2) (csubst0 i v c1 
c2)))))) (\lambda (H3: (eq T t1 t2)).(eq_ind T t2 (\lambda (t: T).((csubst0 i 
v c1 c2) \to (or3 (land (eq C c1 c2) (subst0 i v t t2)) (land (eq T t t2) 
(csubst0 i v c1 c2)) (land (subst0 i v t t2) (csubst0 i v c1 c2))))) (\lambda 
(H4: (csubst0 i v c1 c2)).(or3_intro1 (land (eq C c1 c2) (subst0 i v t2 t2)) 
(land (eq T t2 t2) (csubst0 i v c1 c2)) (land (subst0 i v t2 t2) (csubst0 i v 
c1 c2)) (conj (eq T t2 t2) (csubst0 i v c1 c2) (refl_equal T t2) H4))) t1 
(sym_eq T t1 t2 H3))) c0 (sym_eq C c0 c2 H1) H2 H0))) | (fsubst0_both t0 H0 
c0 H1) \Rightarrow (\lambda (H2: (eq C c0 c2)).(\lambda (H3: (eq T t0 
t2)).(eq_ind C c2 (\lambda (c: C).((eq T t0 t2) \to ((subst0 i v t1 t0) \to 
((csubst0 i v c1 c) \to (or3 (land (eq C c1 c2) (subst0 i v t1 t2)) (land (eq 
T t1 t2) (csubst0 i v c1 c2)) (land (subst0 i v t1 t2) (csubst0 i v c1 
c2))))))) (\lambda (H4: (eq T t0 t2)).(eq_ind T t2 (\lambda (t: T).((subst0 i 
v t1 t) \to ((csubst0 i v c1 c2) \to (or3 (land (eq C c1 c2) (subst0 i v t1 
t2)) (land (eq T t1 t2) (csubst0 i v c1 c2)) (land (subst0 i v t1 t2) 
(csubst0 i v c1 c2)))))) (\lambda (H5: (subst0 i v t1 t2)).(\lambda (H6: 
(csubst0 i v c1 c2)).(or3_intro2 (land (eq C c1 c2) (subst0 i v t1 t2)) (land 
(eq T t1 t2) (csubst0 i v c1 c2)) (land (subst0 i v t1 t2) (csubst0 i v c1 
c2)) (conj (subst0 i v t1 t2) (csubst0 i v c1 c2) H5 H6)))) t0 (sym_eq T t0 
t2 H4))) c0 (sym_eq C c0 c2 H2) H3 H0 H1)))]) in (H0 (refl_equal C c2) 
(refl_equal T t2))))))))).

