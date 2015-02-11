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

include "basic_1/fsubst0/defs.ma".

theorem fsubst0_ind:
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

theorem fsubst0_gen_base:
 \forall (c1: C).(\forall (c2: C).(\forall (t1: T).(\forall (t2: T).(\forall 
(v: T).(\forall (i: nat).((fsubst0 i v c1 t1 c2 t2) \to (or3 (land (eq C c1 
c2) (subst0 i v t1 t2)) (land (eq T t1 t2) (csubst0 i v c1 c2)) (land (subst0 
i v t1 t2) (csubst0 i v c1 c2)))))))))
\def
 \lambda (c1: C).(\lambda (c2: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda 
(v: T).(\lambda (i: nat).(\lambda (H: (fsubst0 i v c1 t1 c2 t2)).(let TMP_10 
\def (\lambda (c: C).(\lambda (t: T).(let TMP_1 \def (eq C c1 c) in (let 
TMP_2 \def (subst0 i v t1 t) in (let TMP_3 \def (land TMP_1 TMP_2) in (let 
TMP_4 \def (eq T t1 t) in (let TMP_5 \def (csubst0 i v c1 c) in (let TMP_6 
\def (land TMP_4 TMP_5) in (let TMP_7 \def (subst0 i v t1 t) in (let TMP_8 
\def (csubst0 i v c1 c) in (let TMP_9 \def (land TMP_7 TMP_8) in (or3 TMP_3 
TMP_6 TMP_9)))))))))))) in (let TMP_24 \def (\lambda (t0: T).(\lambda (H0: 
(subst0 i v t1 t0)).(let TMP_11 \def (eq C c1 c1) in (let TMP_12 \def (subst0 
i v t1 t0) in (let TMP_13 \def (land TMP_11 TMP_12) in (let TMP_14 \def (eq T 
t1 t0) in (let TMP_15 \def (csubst0 i v c1 c1) in (let TMP_16 \def (land 
TMP_14 TMP_15) in (let TMP_17 \def (subst0 i v t1 t0) in (let TMP_18 \def 
(csubst0 i v c1 c1) in (let TMP_19 \def (land TMP_17 TMP_18) in (let TMP_20 
\def (eq C c1 c1) in (let TMP_21 \def (subst0 i v t1 t0) in (let TMP_22 \def 
(refl_equal C c1) in (let TMP_23 \def (conj TMP_20 TMP_21 TMP_22 H0) in 
(or3_intro0 TMP_13 TMP_16 TMP_19 TMP_23)))))))))))))))) in (let TMP_38 \def 
(\lambda (c0: C).(\lambda (H0: (csubst0 i v c1 c0)).(let TMP_25 \def (eq C c1 
c0) in (let TMP_26 \def (subst0 i v t1 t1) in (let TMP_27 \def (land TMP_25 
TMP_26) in (let TMP_28 \def (eq T t1 t1) in (let TMP_29 \def (csubst0 i v c1 
c0) in (let TMP_30 \def (land TMP_28 TMP_29) in (let TMP_31 \def (subst0 i v 
t1 t1) in (let TMP_32 \def (csubst0 i v c1 c0) in (let TMP_33 \def (land 
TMP_31 TMP_32) in (let TMP_34 \def (eq T t1 t1) in (let TMP_35 \def (csubst0 
i v c1 c0) in (let TMP_36 \def (refl_equal T t1) in (let TMP_37 \def (conj 
TMP_34 TMP_35 TMP_36 H0) in (or3_intro1 TMP_27 TMP_30 TMP_33 
TMP_37)))))))))))))))) in (let TMP_51 \def (\lambda (t0: T).(\lambda (H0: 
(subst0 i v t1 t0)).(\lambda (c0: C).(\lambda (H1: (csubst0 i v c1 c0)).(let 
TMP_39 \def (eq C c1 c0) in (let TMP_40 \def (subst0 i v t1 t0) in (let 
TMP_41 \def (land TMP_39 TMP_40) in (let TMP_42 \def (eq T t1 t0) in (let 
TMP_43 \def (csubst0 i v c1 c0) in (let TMP_44 \def (land TMP_42 TMP_43) in 
(let TMP_45 \def (subst0 i v t1 t0) in (let TMP_46 \def (csubst0 i v c1 c0) 
in (let TMP_47 \def (land TMP_45 TMP_46) in (let TMP_48 \def (subst0 i v t1 
t0) in (let TMP_49 \def (csubst0 i v c1 c0) in (let TMP_50 \def (conj TMP_48 
TMP_49 H0 H1) in (or3_intro2 TMP_41 TMP_44 TMP_47 TMP_50))))))))))))))))) in 
(fsubst0_ind i v c1 t1 TMP_10 TMP_24 TMP_38 TMP_51 c2 t2 H))))))))))).

