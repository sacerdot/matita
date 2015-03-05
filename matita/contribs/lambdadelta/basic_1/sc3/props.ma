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

include "basic_1/sc3/defs.ma".

include "basic_1/sn3/lift1.ma".

include "basic_1/nf2/lift1.ma".

include "basic_1/csuba/arity.ma".

include "basic_1/arity/lift1.ma".

include "basic_1/arity/aprem.ma".

include "basic_1/llt/props.ma".

include "basic_1/llt/fwd.ma".

include "basic_1/drop1/getl.ma".

include "basic_1/drop1/props.ma".

include "basic_1/lift1/drop1.ma".

theorem sc3_arity_gen:
 \forall (g: G).(\forall (c: C).(\forall (t: T).(\forall (a: A).((sc3 g a c 
t) \to (arity g c t a)))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (t: T).(\lambda (a: A).(let TMP_1 
\def (\lambda (a0: A).((sc3 g a0 c t) \to (arity g c t a0))) in (let TMP_8 
\def (\lambda (n: nat).(\lambda (n0: nat).(\lambda (H: (land (arity g c t 
(ASort n n0)) (sn3 c t))).(let H0 \def H in (let TMP_2 \def (ASort n n0) in 
(let TMP_3 \def (arity g c t TMP_2) in (let TMP_4 \def (sn3 c t) in (let 
TMP_5 \def (ASort n n0) in (let TMP_6 \def (arity g c t TMP_5) in (let TMP_7 
\def (\lambda (H1: (arity g c t (ASort n n0))).(\lambda (_: (sn3 c t)).H1)) 
in (land_ind TMP_3 TMP_4 TMP_6 TMP_7 H0))))))))))) in (let TMP_18 \def 
(\lambda (a0: A).(\lambda (_: (((sc3 g a0 c t) \to (arity g c t 
a0)))).(\lambda (a1: A).(\lambda (_: (((sc3 g a1 c t) \to (arity g c t 
a1)))).(\lambda (H1: (land (arity g c t (AHead a0 a1)) (\forall (d: 
C).(\forall (w: T).((sc3 g a0 d w) \to (\forall (is: PList).((drop1 is d c) 
\to (sc3 g a1 d (THead (Flat Appl) w (lift1 is t)))))))))).(let H2 \def H1 in 
(let TMP_9 \def (AHead a0 a1) in (let TMP_10 \def (arity g c t TMP_9) in (let 
TMP_14 \def (\forall (d: C).(\forall (w: T).((sc3 g a0 d w) \to (\forall (is: 
PList).((drop1 is d c) \to (let TMP_11 \def (Flat Appl) in (let TMP_12 \def 
(lift1 is t) in (let TMP_13 \def (THead TMP_11 w TMP_12) in (sc3 g a1 d 
TMP_13))))))))) in (let TMP_15 \def (AHead a0 a1) in (let TMP_16 \def (arity 
g c t TMP_15) in (let TMP_17 \def (\lambda (H3: (arity g c t (AHead a0 
a1))).(\lambda (_: ((\forall (d: C).(\forall (w: T).((sc3 g a0 d w) \to 
(\forall (is: PList).((drop1 is d c) \to (sc3 g a1 d (THead (Flat Appl) w 
(lift1 is t)))))))))).H3)) in (land_ind TMP_10 TMP_14 TMP_16 TMP_17 
H2))))))))))))) in (A_ind TMP_1 TMP_8 TMP_18 a))))))).

theorem sc3_repl:
 \forall (g: G).(\forall (a1: A).(\forall (c: C).(\forall (t: T).((sc3 g a1 c 
t) \to (\forall (a2: A).((leq g a1 a2) \to (sc3 g a2 c t)))))))
\def
 \lambda (g: G).(\lambda (a1: A).(let TMP_1 \def (\lambda (a: A).(\forall (c: 
C).(\forall (t: T).((sc3 g a c t) \to (\forall (a2: A).((leq g a a2) \to (sc3 
g a2 c t))))))) in (let TMP_73 \def (\lambda (a2: A).(let TMP_2 \def (\lambda 
(a: A).(((\forall (a3: A).((llt a3 a) \to (\forall (c: C).(\forall (t: 
T).((sc3 g a3 c t) \to (\forall (a4: A).((leq g a3 a4) \to (sc3 g a4 c 
t))))))))) \to (\forall (c: C).(\forall (t: T).((sc3 g a c t) \to (\forall 
(a3: A).((leq g a a3) \to (sc3 g a3 c t)))))))) in (let TMP_28 \def (\lambda 
(n: nat).(\lambda (n0: nat).(\lambda (_: ((\forall (a3: A).((llt a3 (ASort n 
n0)) \to (\forall (c: C).(\forall (t: T).((sc3 g a3 c t) \to (\forall (a4: 
A).((leq g a3 a4) \to (sc3 g a4 c t)))))))))).(\lambda (c: C).(\lambda (t: 
T).(\lambda (H0: (land (arity g c t (ASort n n0)) (sn3 c t))).(\lambda (a3: 
A).(\lambda (H1: (leq g (ASort n n0) a3)).(let H2 \def H0 in (let TMP_3 \def 
(ASort n n0) in (let TMP_4 \def (arity g c t TMP_3) in (let TMP_5 \def (sn3 c 
t) in (let TMP_6 \def (sc3 g a3 c t) in (let TMP_27 \def (\lambda (H3: (arity 
g c t (ASort n n0))).(\lambda (H4: (sn3 c t)).(let TMP_7 \def (ASort n n0) in 
(let H_y \def (arity_repl g c t TMP_7 H3 a3 H1) in (let H_x \def 
(leq_gen_sort1 g n n0 a3 H1) in (let H5 \def H_x in (let TMP_12 \def (\lambda 
(n2: nat).(\lambda (h2: nat).(\lambda (k: nat).(let TMP_8 \def (ASort n n0) 
in (let TMP_9 \def (aplus g TMP_8 k) in (let TMP_10 \def (ASort h2 n2) in 
(let TMP_11 \def (aplus g TMP_10 k) in (eq A TMP_9 TMP_11)))))))) in (let 
TMP_14 \def (\lambda (n2: nat).(\lambda (h2: nat).(\lambda (_: nat).(let 
TMP_13 \def (ASort h2 n2) in (eq A a3 TMP_13))))) in (let TMP_15 \def (sc3 g 
a3 c t) in (let TMP_26 \def (\lambda (x0: nat).(\lambda (x1: nat).(\lambda 
(x2: nat).(\lambda (_: (eq A (aplus g (ASort n n0) x2) (aplus g (ASort x1 x0) 
x2))).(\lambda (H7: (eq A a3 (ASort x1 x0))).(let TMP_16 \def (\lambda (e: 
A).e) in (let TMP_17 \def (ASort x1 x0) in (let H8 \def (f_equal A A TMP_16 
a3 TMP_17 H7) in (let TMP_18 \def (\lambda (a: A).(arity g c t a)) in (let 
TMP_19 \def (ASort x1 x0) in (let H9 \def (eq_ind A a3 TMP_18 H_y TMP_19 H8) 
in (let TMP_20 \def (ASort x1 x0) in (let TMP_21 \def (\lambda (a: A).(sc3 g 
a c t)) in (let TMP_22 \def (ASort x1 x0) in (let TMP_23 \def (arity g c t 
TMP_22) in (let TMP_24 \def (sn3 c t) in (let TMP_25 \def (conj TMP_23 TMP_24 
H9 H4) in (eq_ind_r A TMP_20 TMP_21 TMP_25 a3 H8)))))))))))))))))) in 
(ex2_3_ind nat nat nat TMP_12 TMP_14 TMP_15 TMP_26 H5))))))))))) in (land_ind 
TMP_4 TMP_5 TMP_6 TMP_27 H2))))))))))))))) in (let TMP_72 \def (\lambda (a: 
A).(\lambda (_: ((((\forall (a3: A).((llt a3 a) \to (\forall (c: C).(\forall 
(t: T).((sc3 g a3 c t) \to (\forall (a4: A).((leq g a3 a4) \to (sc3 g a4 c 
t))))))))) \to (\forall (c: C).(\forall (t: T).((sc3 g a c t) \to (\forall 
(a3: A).((leq g a a3) \to (sc3 g a3 c t))))))))).(\lambda (a0: A).(\lambda 
(H0: ((((\forall (a3: A).((llt a3 a0) \to (\forall (c: C).(\forall (t: 
T).((sc3 g a3 c t) \to (\forall (a4: A).((leq g a3 a4) \to (sc3 g a4 c 
t))))))))) \to (\forall (c: C).(\forall (t: T).((sc3 g a0 c t) \to (\forall 
(a3: A).((leq g a0 a3) \to (sc3 g a3 c t))))))))).(\lambda (H1: ((\forall 
(a3: A).((llt a3 (AHead a a0)) \to (\forall (c: C).(\forall (t: T).((sc3 g a3 
c t) \to (\forall (a4: A).((leq g a3 a4) \to (sc3 g a4 c t)))))))))).(\lambda 
(c: C).(\lambda (t: T).(\lambda (H2: (land (arity g c t (AHead a a0)) 
(\forall (d: C).(\forall (w: T).((sc3 g a d w) \to (\forall (is: 
PList).((drop1 is d c) \to (sc3 g a0 d (THead (Flat Appl) w (lift1 is 
t)))))))))).(\lambda (a3: A).(\lambda (H3: (leq g (AHead a a0) a3)).(let H4 
\def H2 in (let TMP_29 \def (AHead a a0) in (let TMP_30 \def (arity g c t 
TMP_29) in (let TMP_34 \def (\forall (d: C).(\forall (w: T).((sc3 g a d w) 
\to (\forall (is: PList).((drop1 is d c) \to (let TMP_31 \def (Flat Appl) in 
(let TMP_32 \def (lift1 is t) in (let TMP_33 \def (THead TMP_31 w TMP_32) in 
(sc3 g a0 d TMP_33))))))))) in (let TMP_35 \def (sc3 g a3 c t) in (let TMP_71 
\def (\lambda (H5: (arity g c t (AHead a a0))).(\lambda (H6: ((\forall (d: 
C).(\forall (w: T).((sc3 g a d w) \to (\forall (is: PList).((drop1 is d c) 
\to (sc3 g a0 d (THead (Flat Appl) w (lift1 is t)))))))))).(let H_x \def 
(leq_gen_head1 g a a0 a3 H3) in (let H7 \def H_x in (let TMP_36 \def (\lambda 
(a4: A).(\lambda (_: A).(leq g a a4))) in (let TMP_37 \def (\lambda (_: 
A).(\lambda (a5: A).(leq g a0 a5))) in (let TMP_39 \def (\lambda (a4: 
A).(\lambda (a5: A).(let TMP_38 \def (AHead a4 a5) in (eq A a3 TMP_38)))) in 
(let TMP_40 \def (sc3 g a3 c t) in (let TMP_70 \def (\lambda (x0: A).(\lambda 
(x1: A).(\lambda (H8: (leq g a x0)).(\lambda (H9: (leq g a0 x1)).(\lambda 
(H10: (eq A a3 (AHead x0 x1))).(let TMP_41 \def (\lambda (e: A).e) in (let 
TMP_42 \def (AHead x0 x1) in (let H11 \def (f_equal A A TMP_41 a3 TMP_42 H10) 
in (let TMP_43 \def (AHead x0 x1) in (let TMP_44 \def (\lambda (a4: A).(sc3 g 
a4 c t)) in (let TMP_45 \def (AHead x0 x1) in (let TMP_46 \def (arity g c t 
TMP_45) in (let TMP_50 \def (\forall (d: C).(\forall (w: T).((sc3 g x0 d w) 
\to (\forall (is: PList).((drop1 is d c) \to (let TMP_47 \def (Flat Appl) in 
(let TMP_48 \def (lift1 is t) in (let TMP_49 \def (THead TMP_47 w TMP_48) in 
(sc3 g x1 d TMP_49))))))))) in (let TMP_51 \def (AHead a a0) in (let TMP_52 
\def (AHead x0 x1) in (let TMP_53 \def (leq_head g a x0 H8 a0 x1 H9) in (let 
TMP_54 \def (arity_repl g c t TMP_51 H5 TMP_52 TMP_53) in (let TMP_68 \def 
(\lambda (d: C).(\lambda (w: T).(\lambda (H12: (sc3 g x0 d w)).(\lambda (is: 
PList).(\lambda (H13: (drop1 is d c)).(let TMP_58 \def (\lambda (a4: 
A).(\lambda (H14: (llt a4 a0)).(\lambda (c0: C).(\lambda (t0: T).(\lambda 
(H15: (sc3 g a4 c0 t0)).(\lambda (a5: A).(\lambda (H16: (leq g a4 a5)).(let 
TMP_55 \def (AHead a a0) in (let TMP_56 \def (llt_head_dx a a0) in (let 
TMP_57 \def (llt_trans a4 a0 TMP_55 H14 TMP_56) in (H1 a4 TMP_57 c0 t0 H15 a5 
H16))))))))))) in (let TMP_59 \def (Flat Appl) in (let TMP_60 \def (lift1 is 
t) in (let TMP_61 \def (THead TMP_59 w TMP_60) in (let TMP_62 \def (AHead a 
a0) in (let TMP_63 \def (llt_head_sx a a0) in (let TMP_64 \def (llt_repl g a 
x0 H8 TMP_62 TMP_63) in (let TMP_65 \def (leq_sym g a x0 H8) in (let TMP_66 
\def (H1 x0 TMP_64 d w H12 a TMP_65) in (let TMP_67 \def (H6 d w TMP_66 is 
H13) in (H0 TMP_58 d TMP_61 TMP_67 x1 H9)))))))))))))))) in (let TMP_69 \def 
(conj TMP_46 TMP_50 TMP_54 TMP_68) in (eq_ind_r A TMP_43 TMP_44 TMP_69 a3 
H11)))))))))))))))))))) in (ex3_2_ind A A TMP_36 TMP_37 TMP_39 TMP_40 TMP_70 
H7)))))))))) in (land_ind TMP_30 TMP_34 TMP_35 TMP_71 H4))))))))))))))))) in 
(A_ind TMP_2 TMP_28 TMP_72 a2))))) in (llt_wf_ind TMP_1 TMP_73 a1)))).

theorem sc3_lift:
 \forall (g: G).(\forall (a: A).(\forall (e: C).(\forall (t: T).((sc3 g a e 
t) \to (\forall (c: C).(\forall (h: nat).(\forall (d: nat).((drop h d c e) 
\to (sc3 g a c (lift h d t))))))))))
\def
 \lambda (g: G).(\lambda (a: A).(let TMP_2 \def (\lambda (a0: A).(\forall (e: 
C).(\forall (t: T).((sc3 g a0 e t) \to (\forall (c: C).(\forall (h: 
nat).(\forall (d: nat).((drop h d c e) \to (let TMP_1 \def (lift h d t) in 
(sc3 g a0 c TMP_1)))))))))) in (let TMP_21 \def (\lambda (n: nat).(\lambda 
(n0: nat).(\lambda (e: C).(\lambda (t: T).(\lambda (H: (land (arity g e t 
(ASort n n0)) (sn3 e t))).(\lambda (c: C).(\lambda (h: nat).(\lambda (d: 
nat).(\lambda (H0: (drop h d c e)).(let H1 \def H in (let TMP_3 \def (ASort n 
n0) in (let TMP_4 \def (arity g e t TMP_3) in (let TMP_5 \def (sn3 e t) in 
(let TMP_6 \def (lift h d t) in (let TMP_7 \def (ASort n n0) in (let TMP_8 
\def (arity g c TMP_6 TMP_7) in (let TMP_9 \def (lift h d t) in (let TMP_10 
\def (sn3 c TMP_9) in (let TMP_11 \def (land TMP_8 TMP_10) in (let TMP_20 
\def (\lambda (H2: (arity g e t (ASort n n0))).(\lambda (H3: (sn3 e t)).(let 
TMP_12 \def (lift h d t) in (let TMP_13 \def (ASort n n0) in (let TMP_14 \def 
(arity g c TMP_12 TMP_13) in (let TMP_15 \def (lift h d t) in (let TMP_16 
\def (sn3 c TMP_15) in (let TMP_17 \def (ASort n n0) in (let TMP_18 \def 
(arity_lift g e t TMP_17 H2 c h d H0) in (let TMP_19 \def (sn3_lift e t H3 c 
h d H0) in (conj TMP_14 TMP_16 TMP_18 TMP_19))))))))))) in (land_ind TMP_4 
TMP_5 TMP_11 TMP_20 H1))))))))))))))))))))) in (let TMP_60 \def (\lambda (a0: 
A).(\lambda (_: ((\forall (e: C).(\forall (t: T).((sc3 g a0 e t) \to (\forall 
(c: C).(\forall (h: nat).(\forall (d: nat).((drop h d c e) \to (sc3 g a0 c 
(lift h d t))))))))))).(\lambda (a1: A).(\lambda (_: ((\forall (e: 
C).(\forall (t: T).((sc3 g a1 e t) \to (\forall (c: C).(\forall (h: 
nat).(\forall (d: nat).((drop h d c e) \to (sc3 g a1 c (lift h d 
t))))))))))).(\lambda (e: C).(\lambda (t: T).(\lambda (H1: (land (arity g e t 
(AHead a0 a1)) (\forall (d: C).(\forall (w: T).((sc3 g a0 d w) \to (\forall 
(is: PList).((drop1 is d e) \to (sc3 g a1 d (THead (Flat Appl) w (lift1 is 
t)))))))))).(\lambda (c: C).(\lambda (h: nat).(\lambda (d: nat).(\lambda (H2: 
(drop h d c e)).(let H3 \def H1 in (let TMP_22 \def (AHead a0 a1) in (let 
TMP_23 \def (arity g e t TMP_22) in (let TMP_27 \def (\forall (d0: 
C).(\forall (w: T).((sc3 g a0 d0 w) \to (\forall (is: PList).((drop1 is d0 e) 
\to (let TMP_24 \def (Flat Appl) in (let TMP_25 \def (lift1 is t) in (let 
TMP_26 \def (THead TMP_24 w TMP_25) in (sc3 g a1 d0 TMP_26))))))))) in (let 
TMP_28 \def (lift h d t) in (let TMP_29 \def (AHead a0 a1) in (let TMP_30 
\def (arity g c TMP_28 TMP_29) in (let TMP_35 \def (\forall (d0: C).(\forall 
(w: T).((sc3 g a0 d0 w) \to (\forall (is: PList).((drop1 is d0 c) \to (let 
TMP_31 \def (Flat Appl) in (let TMP_32 \def (lift h d t) in (let TMP_33 \def 
(lift1 is TMP_32) in (let TMP_34 \def (THead TMP_31 w TMP_33) in (sc3 g a1 d0 
TMP_34)))))))))) in (let TMP_36 \def (land TMP_30 TMP_35) in (let TMP_59 \def 
(\lambda (H4: (arity g e t (AHead a0 a1))).(\lambda (H5: ((\forall (d0: 
C).(\forall (w: T).((sc3 g a0 d0 w) \to (\forall (is: PList).((drop1 is d0 e) 
\to (sc3 g a1 d0 (THead (Flat Appl) w (lift1 is t)))))))))).(let TMP_37 \def 
(lift h d t) in (let TMP_38 \def (AHead a0 a1) in (let TMP_39 \def (arity g c 
TMP_37 TMP_38) in (let TMP_44 \def (\forall (d0: C).(\forall (w: T).((sc3 g 
a0 d0 w) \to (\forall (is: PList).((drop1 is d0 c) \to (let TMP_40 \def (Flat 
Appl) in (let TMP_41 \def (lift h d t) in (let TMP_42 \def (lift1 is TMP_41) 
in (let TMP_43 \def (THead TMP_40 w TMP_42) in (sc3 g a1 d0 TMP_43)))))))))) 
in (let TMP_45 \def (AHead a0 a1) in (let TMP_46 \def (arity_lift g e t 
TMP_45 H4 c h d H2) in (let TMP_58 \def (\lambda (d0: C).(\lambda (w: 
T).(\lambda (H6: (sc3 g a0 d0 w)).(\lambda (is: PList).(\lambda (H7: (drop1 
is d0 c)).(let TMP_47 \def (PConsTail is h d) in (let H_y \def (H5 d0 w H6 
TMP_47) in (let TMP_48 \def (PConsTail is h d) in (let TMP_49 \def (lift1 
TMP_48 t) in (let TMP_52 \def (\lambda (t0: T).(let TMP_50 \def (Flat Appl) 
in (let TMP_51 \def (THead TMP_50 w t0) in (sc3 g a1 d0 TMP_51)))) in (let 
TMP_53 \def (drop1_cons_tail c e h d H2 is d0 H7) in (let TMP_54 \def (H_y 
TMP_53) in (let TMP_55 \def (lift h d t) in (let TMP_56 \def (lift1 is 
TMP_55) in (let TMP_57 \def (lift1_cons_tail t h d is) in (eq_ind T TMP_49 
TMP_52 TMP_54 TMP_56 TMP_57)))))))))))))))) in (conj TMP_39 TMP_44 TMP_46 
TMP_58)))))))))) in (land_ind TMP_23 TMP_27 TMP_36 TMP_59 
H3)))))))))))))))))))))) in (A_ind TMP_2 TMP_21 TMP_60 a))))).

theorem sc3_lift1:
 \forall (g: G).(\forall (e: C).(\forall (a: A).(\forall (hds: 
PList).(\forall (c: C).(\forall (t: T).((sc3 g a e t) \to ((drop1 hds c e) 
\to (sc3 g a c (lift1 hds t)))))))))
\def
 \lambda (g: G).(\lambda (e: C).(\lambda (a: A).(\lambda (hds: PList).(let 
TMP_2 \def (\lambda (p: PList).(\forall (c: C).(\forall (t: T).((sc3 g a e t) 
\to ((drop1 p c e) \to (let TMP_1 \def (lift1 p t) in (sc3 g a c TMP_1))))))) 
in (let TMP_4 \def (\lambda (c: C).(\lambda (t: T).(\lambda (H: (sc3 g a e 
t)).(\lambda (H0: (drop1 PNil c e)).(let H_y \def (drop1_gen_pnil c e H0) in 
(let TMP_3 \def (\lambda (c0: C).(sc3 g a c0 t)) in (eq_ind_r C e TMP_3 H c 
H_y))))))) in (let TMP_13 \def (\lambda (n: nat).(\lambda (n0: nat).(\lambda 
(p: PList).(\lambda (H: ((\forall (c: C).(\forall (t: T).((sc3 g a e t) \to 
((drop1 p c e) \to (sc3 g a c (lift1 p t)))))))).(\lambda (c: C).(\lambda (t: 
T).(\lambda (H0: (sc3 g a e t)).(\lambda (H1: (drop1 (PCons n n0 p) c 
e)).(let H_x \def (drop1_gen_pcons c e p n n0 H1) in (let H2 \def H_x in (let 
TMP_5 \def (\lambda (c2: C).(drop n n0 c c2)) in (let TMP_6 \def (\lambda 
(c2: C).(drop1 p c2 e)) in (let TMP_7 \def (lift1 p t) in (let TMP_8 \def 
(lift n n0 TMP_7) in (let TMP_9 \def (sc3 g a c TMP_8) in (let TMP_12 \def 
(\lambda (x: C).(\lambda (H3: (drop n n0 c x)).(\lambda (H4: (drop1 p x 
e)).(let TMP_10 \def (lift1 p t) in (let TMP_11 \def (H x t H0 H4) in 
(sc3_lift g a x TMP_10 TMP_11 c n n0 H3)))))) in (ex2_ind C TMP_5 TMP_6 TMP_9 
TMP_12 H2))))))))))))))))) in (PList_ind TMP_2 TMP_4 TMP_13 hds))))))).

theorem sc3_abbr:
 \forall (g: G).(\forall (a: A).(\forall (vs: TList).(\forall (i: 
nat).(\forall (d: C).(\forall (v: T).(\forall (c: C).((sc3 g a c (THeads 
(Flat Appl) vs (lift (S i) O v))) \to ((getl i c (CHead d (Bind Abbr) v)) \to 
(sc3 g a c (THeads (Flat Appl) vs (TLRef i)))))))))))
\def
 \lambda (g: G).(\lambda (a: A).(let TMP_4 \def (\lambda (a0: A).(\forall 
(vs: TList).(\forall (i: nat).(\forall (d: C).(\forall (v: T).(\forall (c: 
C).((sc3 g a0 c (THeads (Flat Appl) vs (lift (S i) O v))) \to ((getl i c 
(CHead d (Bind Abbr) v)) \to (let TMP_1 \def (Flat Appl) in (let TMP_2 \def 
(TLRef i) in (let TMP_3 \def (THeads TMP_1 vs TMP_2) in (sc3 g a0 c 
TMP_3)))))))))))) in (let TMP_39 \def (\lambda (n: nat).(\lambda (n0: 
nat).(\lambda (vs: TList).(\lambda (i: nat).(\lambda (d: C).(\lambda (v: 
T).(\lambda (c: C).(\lambda (H: (land (arity g c (THeads (Flat Appl) vs (lift 
(S i) O v)) (ASort n n0)) (sn3 c (THeads (Flat Appl) vs (lift (S i) O 
v))))).(\lambda (H0: (getl i c (CHead d (Bind Abbr) v))).(let H1 \def H in 
(let TMP_5 \def (Flat Appl) in (let TMP_6 \def (S i) in (let TMP_7 \def (lift 
TMP_6 O v) in (let TMP_8 \def (THeads TMP_5 vs TMP_7) in (let TMP_9 \def 
(ASort n n0) in (let TMP_10 \def (arity g c TMP_8 TMP_9) in (let TMP_11 \def 
(Flat Appl) in (let TMP_12 \def (S i) in (let TMP_13 \def (lift TMP_12 O v) 
in (let TMP_14 \def (THeads TMP_11 vs TMP_13) in (let TMP_15 \def (sn3 c 
TMP_14) in (let TMP_16 \def (Flat Appl) in (let TMP_17 \def (TLRef i) in (let 
TMP_18 \def (THeads TMP_16 vs TMP_17) in (let TMP_19 \def (ASort n n0) in 
(let TMP_20 \def (arity g c TMP_18 TMP_19) in (let TMP_21 \def (Flat Appl) in 
(let TMP_22 \def (TLRef i) in (let TMP_23 \def (THeads TMP_21 vs TMP_22) in 
(let TMP_24 \def (sn3 c TMP_23) in (let TMP_25 \def (land TMP_20 TMP_24) in 
(let TMP_38 \def (\lambda (H2: (arity g c (THeads (Flat Appl) vs (lift (S i) 
O v)) (ASort n n0))).(\lambda (H3: (sn3 c (THeads (Flat Appl) vs (lift (S i) 
O v)))).(let TMP_26 \def (Flat Appl) in (let TMP_27 \def (TLRef i) in (let 
TMP_28 \def (THeads TMP_26 vs TMP_27) in (let TMP_29 \def (ASort n n0) in 
(let TMP_30 \def (arity g c TMP_28 TMP_29) in (let TMP_31 \def (Flat Appl) in 
(let TMP_32 \def (TLRef i) in (let TMP_33 \def (THeads TMP_31 vs TMP_32) in 
(let TMP_34 \def (sn3 c TMP_33) in (let TMP_35 \def (ASort n n0) in (let 
TMP_36 \def (arity_appls_abbr g c d v i H0 vs TMP_35 H2) in (let TMP_37 \def 
(sn3_appls_abbr c d v i H0 vs H3) in (conj TMP_30 TMP_34 TMP_36 
TMP_37))))))))))))))) in (land_ind TMP_10 TMP_15 TMP_25 TMP_38 
H1))))))))))))))))))))))))))))))))) in (let TMP_166 \def (\lambda (a0: 
A).(\lambda (_: ((\forall (vs: TList).(\forall (i: nat).(\forall (d: 
C).(\forall (v: T).(\forall (c: C).((sc3 g a0 c (THeads (Flat Appl) vs (lift 
(S i) O v))) \to ((getl i c (CHead d (Bind Abbr) v)) \to (sc3 g a0 c (THeads 
(Flat Appl) vs (TLRef i)))))))))))).(\lambda (a1: A).(\lambda (H0: ((\forall 
(vs: TList).(\forall (i: nat).(\forall (d: C).(\forall (v: T).(\forall (c: 
C).((sc3 g a1 c (THeads (Flat Appl) vs (lift (S i) O v))) \to ((getl i c 
(CHead d (Bind Abbr) v)) \to (sc3 g a1 c (THeads (Flat Appl) vs (TLRef 
i)))))))))))).(\lambda (vs: TList).(\lambda (i: nat).(\lambda (d: C).(\lambda 
(v: T).(\lambda (c: C).(\lambda (H1: (land (arity g c (THeads (Flat Appl) vs 
(lift (S i) O v)) (AHead a0 a1)) (\forall (d0: C).(\forall (w: T).((sc3 g a0 
d0 w) \to (\forall (is: PList).((drop1 is d0 c) \to (sc3 g a1 d0 (THead (Flat 
Appl) w (lift1 is (THeads (Flat Appl) vs (lift (S i) O v)))))))))))).(\lambda 
(H2: (getl i c (CHead d (Bind Abbr) v))).(let H3 \def H1 in (let TMP_40 \def 
(Flat Appl) in (let TMP_41 \def (S i) in (let TMP_42 \def (lift TMP_41 O v) 
in (let TMP_43 \def (THeads TMP_40 vs TMP_42) in (let TMP_44 \def (AHead a0 
a1) in (let TMP_45 \def (arity g c TMP_43 TMP_44) in (let TMP_53 \def 
(\forall (d0: C).(\forall (w: T).((sc3 g a0 d0 w) \to (\forall (is: 
PList).((drop1 is d0 c) \to (let TMP_46 \def (Flat Appl) in (let TMP_47 \def 
(Flat Appl) in (let TMP_48 \def (S i) in (let TMP_49 \def (lift TMP_48 O v) 
in (let TMP_50 \def (THeads TMP_47 vs TMP_49) in (let TMP_51 \def (lift1 is 
TMP_50) in (let TMP_52 \def (THead TMP_46 w TMP_51) in (sc3 g a1 d0 
TMP_52))))))))))))) in (let TMP_54 \def (Flat Appl) in (let TMP_55 \def 
(TLRef i) in (let TMP_56 \def (THeads TMP_54 vs TMP_55) in (let TMP_57 \def 
(AHead a0 a1) in (let TMP_58 \def (arity g c TMP_56 TMP_57) in (let TMP_65 
\def (\forall (d0: C).(\forall (w: T).((sc3 g a0 d0 w) \to (\forall (is: 
PList).((drop1 is d0 c) \to (let TMP_59 \def (Flat Appl) in (let TMP_60 \def 
(Flat Appl) in (let TMP_61 \def (TLRef i) in (let TMP_62 \def (THeads TMP_60 
vs TMP_61) in (let TMP_63 \def (lift1 is TMP_62) in (let TMP_64 \def (THead 
TMP_59 w TMP_63) in (sc3 g a1 d0 TMP_64)))))))))))) in (let TMP_66 \def (land 
TMP_58 TMP_65) in (let TMP_165 \def (\lambda (H4: (arity g c (THeads (Flat 
Appl) vs (lift (S i) O v)) (AHead a0 a1))).(\lambda (H5: ((\forall (d0: 
C).(\forall (w: T).((sc3 g a0 d0 w) \to (\forall (is: PList).((drop1 is d0 c) 
\to (sc3 g a1 d0 (THead (Flat Appl) w (lift1 is (THeads (Flat Appl) vs (lift 
(S i) O v)))))))))))).(let TMP_67 \def (Flat Appl) in (let TMP_68 \def (TLRef 
i) in (let TMP_69 \def (THeads TMP_67 vs TMP_68) in (let TMP_70 \def (AHead 
a0 a1) in (let TMP_71 \def (arity g c TMP_69 TMP_70) in (let TMP_78 \def 
(\forall (d0: C).(\forall (w: T).((sc3 g a0 d0 w) \to (\forall (is: 
PList).((drop1 is d0 c) \to (let TMP_72 \def (Flat Appl) in (let TMP_73 \def 
(Flat Appl) in (let TMP_74 \def (TLRef i) in (let TMP_75 \def (THeads TMP_73 
vs TMP_74) in (let TMP_76 \def (lift1 is TMP_75) in (let TMP_77 \def (THead 
TMP_72 w TMP_76) in (sc3 g a1 d0 TMP_77)))))))))))) in (let TMP_79 \def 
(AHead a0 a1) in (let TMP_80 \def (arity_appls_abbr g c d v i H2 vs TMP_79 
H4) in (let TMP_164 \def (\lambda (d0: C).(\lambda (w: T).(\lambda (H6: (sc3 
g a0 d0 w)).(\lambda (is: PList).(\lambda (H7: (drop1 is d0 c)).(let H_x \def 
(drop1_getl_trans is c d0 H7 Abbr d v i H2) in (let H8 \def H_x in (let 
TMP_82 \def (\lambda (e2: C).(let TMP_81 \def (ptrans is i) in (drop1 TMP_81 
e2 d))) in (let TMP_88 \def (\lambda (e2: C).(let TMP_83 \def (trans is i) in 
(let TMP_84 \def (Bind Abbr) in (let TMP_85 \def (ptrans is i) in (let TMP_86 
\def (lift1 TMP_85 v) in (let TMP_87 \def (CHead e2 TMP_84 TMP_86) in (getl 
TMP_83 d0 TMP_87))))))) in (let TMP_89 \def (Flat Appl) in (let TMP_90 \def 
(Flat Appl) in (let TMP_91 \def (TLRef i) in (let TMP_92 \def (THeads TMP_90 
vs TMP_91) in (let TMP_93 \def (lift1 is TMP_92) in (let TMP_94 \def (THead 
TMP_89 w TMP_93) in (let TMP_95 \def (sc3 g a1 d0 TMP_94) in (let TMP_163 
\def (\lambda (x: C).(\lambda (_: (drop1 (ptrans is i) x d)).(\lambda (H10: 
(getl (trans is i) d0 (CHead x (Bind Abbr) (lift1 (ptrans is i) v)))).(let 
TMP_96 \def (lifts1 is vs) in (let TMP_97 \def (TCons w TMP_96) in (let H_y 
\def (H0 TMP_97) in (let TMP_98 \def (Flat Appl) in (let TMP_99 \def (lifts1 
is vs) in (let TMP_100 \def (TLRef i) in (let TMP_101 \def (lift1 is TMP_100) 
in (let TMP_102 \def (THeads TMP_98 TMP_99 TMP_101) in (let TMP_105 \def 
(\lambda (t: T).(let TMP_103 \def (Flat Appl) in (let TMP_104 \def (THead 
TMP_103 w t) in (sc3 g a1 d0 TMP_104)))) in (let TMP_106 \def (trans is i) in 
(let TMP_107 \def (TLRef TMP_106) in (let TMP_113 \def (\lambda (t: T).(let 
TMP_108 \def (Flat Appl) in (let TMP_109 \def (Flat Appl) in (let TMP_110 
\def (lifts1 is vs) in (let TMP_111 \def (THeads TMP_109 TMP_110 t) in (let 
TMP_112 \def (THead TMP_108 w TMP_111) in (sc3 g a1 d0 TMP_112))))))) in (let 
TMP_114 \def (trans is i) in (let TMP_115 \def (ptrans is i) in (let TMP_116 
\def (lift1 TMP_115 v) in (let TMP_117 \def (S i) in (let TMP_118 \def (lift 
TMP_117 O v) in (let TMP_119 \def (lift1 is TMP_118) in (let TMP_125 \def 
(\lambda (t: T).(let TMP_120 \def (Flat Appl) in (let TMP_121 \def (Flat 
Appl) in (let TMP_122 \def (lifts1 is vs) in (let TMP_123 \def (THeads 
TMP_121 TMP_122 t) in (let TMP_124 \def (THead TMP_120 w TMP_123) in (sc3 g 
a1 d0 TMP_124))))))) in (let TMP_126 \def (Flat Appl) in (let TMP_127 \def (S 
i) in (let TMP_128 \def (lift TMP_127 O v) in (let TMP_129 \def (THeads 
TMP_126 vs TMP_128) in (let TMP_130 \def (lift1 is TMP_129) in (let TMP_133 
\def (\lambda (t: T).(let TMP_131 \def (Flat Appl) in (let TMP_132 \def 
(THead TMP_131 w t) in (sc3 g a1 d0 TMP_132)))) in (let TMP_134 \def (H5 d0 w 
H6 is H7) in (let TMP_135 \def (Flat Appl) in (let TMP_136 \def (lifts1 is 
vs) in (let TMP_137 \def (S i) in (let TMP_138 \def (lift TMP_137 O v) in 
(let TMP_139 \def (lift1 is TMP_138) in (let TMP_140 \def (THeads TMP_135 
TMP_136 TMP_139) in (let TMP_141 \def (S i) in (let TMP_142 \def (lift 
TMP_141 O v) in (let TMP_143 \def (lifts1_flat Appl is TMP_142 vs) in (let 
TMP_144 \def (eq_ind T TMP_130 TMP_133 TMP_134 TMP_140 TMP_143) in (let 
TMP_145 \def (trans is i) in (let TMP_146 \def (S TMP_145) in (let TMP_147 
\def (ptrans is i) in (let TMP_148 \def (lift1 TMP_147 v) in (let TMP_149 
\def (lift TMP_146 O TMP_148) in (let TMP_150 \def (lift1_free is i v) in 
(let TMP_151 \def (eq_ind T TMP_119 TMP_125 TMP_144 TMP_149 TMP_150) in (let 
TMP_152 \def (H_y TMP_114 x TMP_116 d0 TMP_151 H10) in (let TMP_153 \def 
(TLRef i) in (let TMP_154 \def (lift1 is TMP_153) in (let TMP_155 \def 
(lift1_lref is i) in (let TMP_156 \def (eq_ind_r T TMP_107 TMP_113 TMP_152 
TMP_154 TMP_155) in (let TMP_157 \def (Flat Appl) in (let TMP_158 \def (TLRef 
i) in (let TMP_159 \def (THeads TMP_157 vs TMP_158) in (let TMP_160 \def 
(lift1 is TMP_159) in (let TMP_161 \def (TLRef i) in (let TMP_162 \def 
(lifts1_flat Appl is TMP_161 vs) in (eq_ind_r T TMP_102 TMP_105 TMP_156 
TMP_160 TMP_162)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) in 
(ex2_ind C TMP_82 TMP_88 TMP_95 TMP_163 H8)))))))))))))))))) in (conj TMP_71 
TMP_78 TMP_80 TMP_164)))))))))))) in (land_ind TMP_45 TMP_53 TMP_66 TMP_165 
H3)))))))))))))))))))))))))))) in (A_ind TMP_4 TMP_39 TMP_166 a))))).

theorem sc3_cast:
 \forall (g: G).(\forall (a: A).(\forall (vs: TList).(\forall (c: C).(\forall 
(u: T).((sc3 g (asucc g a) c (THeads (Flat Appl) vs u)) \to (\forall (t: 
T).((sc3 g a c (THeads (Flat Appl) vs t)) \to (sc3 g a c (THeads (Flat Appl) 
vs (THead (Flat Cast) u t))))))))))
\def
 \lambda (g: G).(\lambda (a: A).(let TMP_5 \def (\lambda (a0: A).(\forall 
(vs: TList).(\forall (c: C).(\forall (u: T).((sc3 g (asucc g a0) c (THeads 
(Flat Appl) vs u)) \to (\forall (t: T).((sc3 g a0 c (THeads (Flat Appl) vs 
t)) \to (let TMP_1 \def (Flat Appl) in (let TMP_2 \def (Flat Cast) in (let 
TMP_3 \def (THead TMP_2 u t) in (let TMP_4 \def (THeads TMP_1 vs TMP_3) in 
(sc3 g a0 c TMP_4)))))))))))) in (let TMP_134 \def (\lambda (n: nat).(\lambda 
(n0: nat).(\lambda (vs: TList).(\lambda (c: C).(\lambda (u: T).(\lambda (H: 
(sc3 g (match n with [O \Rightarrow (ASort O (next g n0)) | (S h) \Rightarrow 
(ASort h n0)]) c (THeads (Flat Appl) vs u))).(\lambda (t: T).(\lambda (H0: 
(land (arity g c (THeads (Flat Appl) vs t) (ASort n n0)) (sn3 c (THeads (Flat 
Appl) vs t)))).(let TMP_17 \def (\lambda (n1: nat).((sc3 g (match n1 with [O 
\Rightarrow (ASort O (next g n0)) | (S h) \Rightarrow (ASort h n0)]) c 
(THeads (Flat Appl) vs u)) \to ((land (arity g c (THeads (Flat Appl) vs t) 
(ASort n1 n0)) (sn3 c (THeads (Flat Appl) vs t))) \to (let TMP_6 \def (Flat 
Appl) in (let TMP_7 \def (Flat Cast) in (let TMP_8 \def (THead TMP_7 u t) in 
(let TMP_9 \def (THeads TMP_6 vs TMP_8) in (let TMP_10 \def (ASort n1 n0) in 
(let TMP_11 \def (arity g c TMP_9 TMP_10) in (let TMP_12 \def (Flat Appl) in 
(let TMP_13 \def (Flat Cast) in (let TMP_14 \def (THead TMP_13 u t) in (let 
TMP_15 \def (THeads TMP_12 vs TMP_14) in (let TMP_16 \def (sn3 c TMP_15) in 
(land TMP_11 TMP_16))))))))))))))) in (let TMP_73 \def (\lambda (H1: (sc3 g 
(ASort O (next g n0)) c (THeads (Flat Appl) vs u))).(\lambda (H2: (land 
(arity g c (THeads (Flat Appl) vs t) (ASort O n0)) (sn3 c (THeads (Flat Appl) 
vs t)))).(let H3 \def H1 in (let TMP_18 \def (Flat Appl) in (let TMP_19 \def 
(THeads TMP_18 vs u) in (let TMP_20 \def (next g n0) in (let TMP_21 \def 
(ASort O TMP_20) in (let TMP_22 \def (arity g c TMP_19 TMP_21) in (let TMP_23 
\def (Flat Appl) in (let TMP_24 \def (THeads TMP_23 vs u) in (let TMP_25 \def 
(sn3 c TMP_24) in (let TMP_26 \def (Flat Appl) in (let TMP_27 \def (Flat 
Cast) in (let TMP_28 \def (THead TMP_27 u t) in (let TMP_29 \def (THeads 
TMP_26 vs TMP_28) in (let TMP_30 \def (ASort O n0) in (let TMP_31 \def (arity 
g c TMP_29 TMP_30) in (let TMP_32 \def (Flat Appl) in (let TMP_33 \def (Flat 
Cast) in (let TMP_34 \def (THead TMP_33 u t) in (let TMP_35 \def (THeads 
TMP_32 vs TMP_34) in (let TMP_36 \def (sn3 c TMP_35) in (let TMP_37 \def 
(land TMP_31 TMP_36) in (let TMP_72 \def (\lambda (H4: (arity g c (THeads 
(Flat Appl) vs u) (ASort O (next g n0)))).(\lambda (H5: (sn3 c (THeads (Flat 
Appl) vs u))).(let H6 \def H2 in (let TMP_38 \def (Flat Appl) in (let TMP_39 
\def (THeads TMP_38 vs t) in (let TMP_40 \def (ASort O n0) in (let TMP_41 
\def (arity g c TMP_39 TMP_40) in (let TMP_42 \def (Flat Appl) in (let TMP_43 
\def (THeads TMP_42 vs t) in (let TMP_44 \def (sn3 c TMP_43) in (let TMP_45 
\def (Flat Appl) in (let TMP_46 \def (Flat Cast) in (let TMP_47 \def (THead 
TMP_46 u t) in (let TMP_48 \def (THeads TMP_45 vs TMP_47) in (let TMP_49 \def 
(ASort O n0) in (let TMP_50 \def (arity g c TMP_48 TMP_49) in (let TMP_51 
\def (Flat Appl) in (let TMP_52 \def (Flat Cast) in (let TMP_53 \def (THead 
TMP_52 u t) in (let TMP_54 \def (THeads TMP_51 vs TMP_53) in (let TMP_55 \def 
(sn3 c TMP_54) in (let TMP_56 \def (land TMP_50 TMP_55) in (let TMP_71 \def 
(\lambda (H7: (arity g c (THeads (Flat Appl) vs t) (ASort O n0))).(\lambda 
(H8: (sn3 c (THeads (Flat Appl) vs t))).(let TMP_57 \def (Flat Appl) in (let 
TMP_58 \def (Flat Cast) in (let TMP_59 \def (THead TMP_58 u t) in (let TMP_60 
\def (THeads TMP_57 vs TMP_59) in (let TMP_61 \def (ASort O n0) in (let 
TMP_62 \def (arity g c TMP_60 TMP_61) in (let TMP_63 \def (Flat Appl) in (let 
TMP_64 \def (Flat Cast) in (let TMP_65 \def (THead TMP_64 u t) in (let TMP_66 
\def (THeads TMP_63 vs TMP_65) in (let TMP_67 \def (sn3 c TMP_66) in (let 
TMP_68 \def (ASort O n0) in (let TMP_69 \def (arity_appls_cast g c u t vs 
TMP_68 H4 H7) in (let TMP_70 \def (sn3_appls_cast c vs u H5 t H8) in (conj 
TMP_62 TMP_67 TMP_69 TMP_70))))))))))))))))) in (land_ind TMP_41 TMP_44 
TMP_56 TMP_71 H6)))))))))))))))))))))))) in (land_ind TMP_22 TMP_25 TMP_37 
TMP_72 H3))))))))))))))))))))))))) in (let TMP_133 \def (\lambda (n1: 
nat).(\lambda (_: (((sc3 g (match n1 with [O \Rightarrow (ASort O (next g 
n0)) | (S h) \Rightarrow (ASort h n0)]) c (THeads (Flat Appl) vs u)) \to 
((land (arity g c (THeads (Flat Appl) vs t) (ASort n1 n0)) (sn3 c (THeads 
(Flat Appl) vs t))) \to (land (arity g c (THeads (Flat Appl) vs (THead (Flat 
Cast) u t)) (ASort n1 n0)) (sn3 c (THeads (Flat Appl) vs (THead (Flat Cast) u 
t)))))))).(\lambda (H1: (sc3 g (ASort n1 n0) c (THeads (Flat Appl) vs 
u))).(\lambda (H2: (land (arity g c (THeads (Flat Appl) vs t) (ASort (S n1) 
n0)) (sn3 c (THeads (Flat Appl) vs t)))).(let H3 \def H1 in (let TMP_74 \def 
(Flat Appl) in (let TMP_75 \def (THeads TMP_74 vs u) in (let TMP_76 \def 
(ASort n1 n0) in (let TMP_77 \def (arity g c TMP_75 TMP_76) in (let TMP_78 
\def (Flat Appl) in (let TMP_79 \def (THeads TMP_78 vs u) in (let TMP_80 \def 
(sn3 c TMP_79) in (let TMP_81 \def (Flat Appl) in (let TMP_82 \def (Flat 
Cast) in (let TMP_83 \def (THead TMP_82 u t) in (let TMP_84 \def (THeads 
TMP_81 vs TMP_83) in (let TMP_85 \def (S n1) in (let TMP_86 \def (ASort 
TMP_85 n0) in (let TMP_87 \def (arity g c TMP_84 TMP_86) in (let TMP_88 \def 
(Flat Appl) in (let TMP_89 \def (Flat Cast) in (let TMP_90 \def (THead TMP_89 
u t) in (let TMP_91 \def (THeads TMP_88 vs TMP_90) in (let TMP_92 \def (sn3 c 
TMP_91) in (let TMP_93 \def (land TMP_87 TMP_92) in (let TMP_132 \def 
(\lambda (H4: (arity g c (THeads (Flat Appl) vs u) (ASort n1 n0))).(\lambda 
(H5: (sn3 c (THeads (Flat Appl) vs u))).(let H6 \def H2 in (let TMP_94 \def 
(Flat Appl) in (let TMP_95 \def (THeads TMP_94 vs t) in (let TMP_96 \def (S 
n1) in (let TMP_97 \def (ASort TMP_96 n0) in (let TMP_98 \def (arity g c 
TMP_95 TMP_97) in (let TMP_99 \def (Flat Appl) in (let TMP_100 \def (THeads 
TMP_99 vs t) in (let TMP_101 \def (sn3 c TMP_100) in (let TMP_102 \def (Flat 
Appl) in (let TMP_103 \def (Flat Cast) in (let TMP_104 \def (THead TMP_103 u 
t) in (let TMP_105 \def (THeads TMP_102 vs TMP_104) in (let TMP_106 \def (S 
n1) in (let TMP_107 \def (ASort TMP_106 n0) in (let TMP_108 \def (arity g c 
TMP_105 TMP_107) in (let TMP_109 \def (Flat Appl) in (let TMP_110 \def (Flat 
Cast) in (let TMP_111 \def (THead TMP_110 u t) in (let TMP_112 \def (THeads 
TMP_109 vs TMP_111) in (let TMP_113 \def (sn3 c TMP_112) in (let TMP_114 \def 
(land TMP_108 TMP_113) in (let TMP_131 \def (\lambda (H7: (arity g c (THeads 
(Flat Appl) vs t) (ASort (S n1) n0))).(\lambda (H8: (sn3 c (THeads (Flat 
Appl) vs t))).(let TMP_115 \def (Flat Appl) in (let TMP_116 \def (Flat Cast) 
in (let TMP_117 \def (THead TMP_116 u t) in (let TMP_118 \def (THeads TMP_115 
vs TMP_117) in (let TMP_119 \def (S n1) in (let TMP_120 \def (ASort TMP_119 
n0) in (let TMP_121 \def (arity g c TMP_118 TMP_120) in (let TMP_122 \def 
(Flat Appl) in (let TMP_123 \def (Flat Cast) in (let TMP_124 \def (THead 
TMP_123 u t) in (let TMP_125 \def (THeads TMP_122 vs TMP_124) in (let TMP_126 
\def (sn3 c TMP_125) in (let TMP_127 \def (S n1) in (let TMP_128 \def (ASort 
TMP_127 n0) in (let TMP_129 \def (arity_appls_cast g c u t vs TMP_128 H4 H7) 
in (let TMP_130 \def (sn3_appls_cast c vs u H5 t H8) in (conj TMP_121 TMP_126 
TMP_129 TMP_130))))))))))))))))))) in (land_ind TMP_98 TMP_101 TMP_114 
TMP_131 H6)))))))))))))))))))))))))) in (land_ind TMP_77 TMP_80 TMP_93 
TMP_132 H3))))))))))))))))))))))))))) in (nat_ind TMP_17 TMP_73 TMP_133 n H 
H0)))))))))))) in (let TMP_270 \def (\lambda (a0: A).(\lambda (_: ((\forall 
(vs: TList).(\forall (c: C).(\forall (u: T).((sc3 g (asucc g a0) c (THeads 
(Flat Appl) vs u)) \to (\forall (t: T).((sc3 g a0 c (THeads (Flat Appl) vs 
t)) \to (sc3 g a0 c (THeads (Flat Appl) vs (THead (Flat Cast) u 
t))))))))))).(\lambda (a1: A).(\lambda (H0: ((\forall (vs: TList).(\forall 
(c: C).(\forall (u: T).((sc3 g (asucc g a1) c (THeads (Flat Appl) vs u)) \to 
(\forall (t: T).((sc3 g a1 c (THeads (Flat Appl) vs t)) \to (sc3 g a1 c 
(THeads (Flat Appl) vs (THead (Flat Cast) u t))))))))))).(\lambda (vs: 
TList).(\lambda (c: C).(\lambda (u: T).(\lambda (H1: (land (arity g c (THeads 
(Flat Appl) vs u) (AHead a0 (asucc g a1))) (\forall (d: C).(\forall (w: 
T).((sc3 g a0 d w) \to (\forall (is: PList).((drop1 is d c) \to (sc3 g (asucc 
g a1) d (THead (Flat Appl) w (lift1 is (THeads (Flat Appl) vs 
u))))))))))).(\lambda (t: T).(\lambda (H2: (land (arity g c (THeads (Flat 
Appl) vs t) (AHead a0 a1)) (\forall (d: C).(\forall (w: T).((sc3 g a0 d w) 
\to (\forall (is: PList).((drop1 is d c) \to (sc3 g a1 d (THead (Flat Appl) w 
(lift1 is (THeads (Flat Appl) vs t))))))))))).(let H3 \def H1 in (let TMP_135 
\def (Flat Appl) in (let TMP_136 \def (THeads TMP_135 vs u) in (let TMP_137 
\def (asucc g a1) in (let TMP_138 \def (AHead a0 TMP_137) in (let TMP_139 
\def (arity g c TMP_136 TMP_138) in (let TMP_146 \def (\forall (d: 
C).(\forall (w: T).((sc3 g a0 d w) \to (\forall (is: PList).((drop1 is d c) 
\to (let TMP_140 \def (asucc g a1) in (let TMP_141 \def (Flat Appl) in (let 
TMP_142 \def (Flat Appl) in (let TMP_143 \def (THeads TMP_142 vs u) in (let 
TMP_144 \def (lift1 is TMP_143) in (let TMP_145 \def (THead TMP_141 w 
TMP_144) in (sc3 g TMP_140 d TMP_145)))))))))))) in (let TMP_147 \def (Flat 
Appl) in (let TMP_148 \def (Flat Cast) in (let TMP_149 \def (THead TMP_148 u 
t) in (let TMP_150 \def (THeads TMP_147 vs TMP_149) in (let TMP_151 \def 
(AHead a0 a1) in (let TMP_152 \def (arity g c TMP_150 TMP_151) in (let 
TMP_160 \def (\forall (d: C).(\forall (w: T).((sc3 g a0 d w) \to (\forall 
(is: PList).((drop1 is d c) \to (let TMP_153 \def (Flat Appl) in (let TMP_154 
\def (Flat Appl) in (let TMP_155 \def (Flat Cast) in (let TMP_156 \def (THead 
TMP_155 u t) in (let TMP_157 \def (THeads TMP_154 vs TMP_156) in (let TMP_158 
\def (lift1 is TMP_157) in (let TMP_159 \def (THead TMP_153 w TMP_158) in 
(sc3 g a1 d TMP_159))))))))))))) in (let TMP_161 \def (land TMP_152 TMP_160) 
in (let TMP_269 \def (\lambda (H4: (arity g c (THeads (Flat Appl) vs u) 
(AHead a0 (asucc g a1)))).(\lambda (H5: ((\forall (d: C).(\forall (w: 
T).((sc3 g a0 d w) \to (\forall (is: PList).((drop1 is d c) \to (sc3 g (asucc 
g a1) d (THead (Flat Appl) w (lift1 is (THeads (Flat Appl) vs 
u))))))))))).(let H6 \def H2 in (let TMP_162 \def (Flat Appl) in (let TMP_163 
\def (THeads TMP_162 vs t) in (let TMP_164 \def (AHead a0 a1) in (let TMP_165 
\def (arity g c TMP_163 TMP_164) in (let TMP_171 \def (\forall (d: 
C).(\forall (w: T).((sc3 g a0 d w) \to (\forall (is: PList).((drop1 is d c) 
\to (let TMP_166 \def (Flat Appl) in (let TMP_167 \def (Flat Appl) in (let 
TMP_168 \def (THeads TMP_167 vs t) in (let TMP_169 \def (lift1 is TMP_168) in 
(let TMP_170 \def (THead TMP_166 w TMP_169) in (sc3 g a1 d TMP_170))))))))))) 
in (let TMP_172 \def (Flat Appl) in (let TMP_173 \def (Flat Cast) in (let 
TMP_174 \def (THead TMP_173 u t) in (let TMP_175 \def (THeads TMP_172 vs 
TMP_174) in (let TMP_176 \def (AHead a0 a1) in (let TMP_177 \def (arity g c 
TMP_175 TMP_176) in (let TMP_185 \def (\forall (d: C).(\forall (w: T).((sc3 g 
a0 d w) \to (\forall (is: PList).((drop1 is d c) \to (let TMP_178 \def (Flat 
Appl) in (let TMP_179 \def (Flat Appl) in (let TMP_180 \def (Flat Cast) in 
(let TMP_181 \def (THead TMP_180 u t) in (let TMP_182 \def (THeads TMP_179 vs 
TMP_181) in (let TMP_183 \def (lift1 is TMP_182) in (let TMP_184 \def (THead 
TMP_178 w TMP_183) in (sc3 g a1 d TMP_184))))))))))))) in (let TMP_186 \def 
(land TMP_177 TMP_185) in (let TMP_268 \def (\lambda (H7: (arity g c (THeads 
(Flat Appl) vs t) (AHead a0 a1))).(\lambda (H8: ((\forall (d: C).(\forall (w: 
T).((sc3 g a0 d w) \to (\forall (is: PList).((drop1 is d c) \to (sc3 g a1 d 
(THead (Flat Appl) w (lift1 is (THeads (Flat Appl) vs t))))))))))).(let 
TMP_187 \def (Flat Appl) in (let TMP_188 \def (Flat Cast) in (let TMP_189 
\def (THead TMP_188 u t) in (let TMP_190 \def (THeads TMP_187 vs TMP_189) in 
(let TMP_191 \def (AHead a0 a1) in (let TMP_192 \def (arity g c TMP_190 
TMP_191) in (let TMP_200 \def (\forall (d: C).(\forall (w: T).((sc3 g a0 d w) 
\to (\forall (is: PList).((drop1 is d c) \to (let TMP_193 \def (Flat Appl) in 
(let TMP_194 \def (Flat Appl) in (let TMP_195 \def (Flat Cast) in (let 
TMP_196 \def (THead TMP_195 u t) in (let TMP_197 \def (THeads TMP_194 vs 
TMP_196) in (let TMP_198 \def (lift1 is TMP_197) in (let TMP_199 \def (THead 
TMP_193 w TMP_198) in (sc3 g a1 d TMP_199))))))))))))) in (let TMP_201 \def 
(AHead a0 a1) in (let TMP_202 \def (arity_appls_cast g c u t vs TMP_201 H4 
H7) in (let TMP_267 \def (\lambda (d: C).(\lambda (w: T).(\lambda (H9: (sc3 g 
a0 d w)).(\lambda (is: PList).(\lambda (H10: (drop1 is d c)).(let TMP_203 
\def (lifts1 is vs) in (let TMP_204 \def (TCons w TMP_203) in (let H_y \def 
(H0 TMP_204) in (let TMP_205 \def (Flat Appl) in (let TMP_206 \def (lifts1 is 
vs) in (let TMP_207 \def (Flat Cast) in (let TMP_208 \def (THead TMP_207 u t) 
in (let TMP_209 \def (lift1 is TMP_208) in (let TMP_210 \def (THeads TMP_205 
TMP_206 TMP_209) in (let TMP_213 \def (\lambda (t0: T).(let TMP_211 \def 
(Flat Appl) in (let TMP_212 \def (THead TMP_211 w t0) in (sc3 g a1 d 
TMP_212)))) in (let TMP_214 \def (Flat Cast) in (let TMP_215 \def (lift1 is 
u) in (let TMP_216 \def (lift1 is t) in (let TMP_217 \def (THead TMP_214 
TMP_215 TMP_216) in (let TMP_223 \def (\lambda (t0: T).(let TMP_218 \def 
(Flat Appl) in (let TMP_219 \def (Flat Appl) in (let TMP_220 \def (lifts1 is 
vs) in (let TMP_221 \def (THeads TMP_219 TMP_220 t0) in (let TMP_222 \def 
(THead TMP_218 w TMP_221) in (sc3 g a1 d TMP_222))))))) in (let TMP_224 \def 
(lift1 is u) in (let TMP_225 \def (Flat Appl) in (let TMP_226 \def (THeads 
TMP_225 vs u) in (let TMP_227 \def (lift1 is TMP_226) in (let TMP_231 \def 
(\lambda (t0: T).(let TMP_228 \def (asucc g a1) in (let TMP_229 \def (Flat 
Appl) in (let TMP_230 \def (THead TMP_229 w t0) in (sc3 g TMP_228 d 
TMP_230))))) in (let TMP_232 \def (H5 d w H9 is H10) in (let TMP_233 \def 
(Flat Appl) in (let TMP_234 \def (lifts1 is vs) in (let TMP_235 \def (lift1 
is u) in (let TMP_236 \def (THeads TMP_233 TMP_234 TMP_235) in (let TMP_237 
\def (lifts1_flat Appl is u vs) in (let TMP_238 \def (eq_ind T TMP_227 
TMP_231 TMP_232 TMP_236 TMP_237) in (let TMP_239 \def (lift1 is t) in (let 
TMP_240 \def (Flat Appl) in (let TMP_241 \def (THeads TMP_240 vs t) in (let 
TMP_242 \def (lift1 is TMP_241) in (let TMP_245 \def (\lambda (t0: T).(let 
TMP_243 \def (Flat Appl) in (let TMP_244 \def (THead TMP_243 w t0) in (sc3 g 
a1 d TMP_244)))) in (let TMP_246 \def (H8 d w H9 is H10) in (let TMP_247 \def 
(Flat Appl) in (let TMP_248 \def (lifts1 is vs) in (let TMP_249 \def (lift1 
is t) in (let TMP_250 \def (THeads TMP_247 TMP_248 TMP_249) in (let TMP_251 
\def (lifts1_flat Appl is t vs) in (let TMP_252 \def (eq_ind T TMP_242 
TMP_245 TMP_246 TMP_250 TMP_251) in (let TMP_253 \def (H_y d TMP_224 TMP_238 
TMP_239 TMP_252) in (let TMP_254 \def (Flat Cast) in (let TMP_255 \def (THead 
TMP_254 u t) in (let TMP_256 \def (lift1 is TMP_255) in (let TMP_257 \def 
(lift1_flat Cast is u t) in (let TMP_258 \def (eq_ind_r T TMP_217 TMP_223 
TMP_253 TMP_256 TMP_257) in (let TMP_259 \def (Flat Appl) in (let TMP_260 
\def (Flat Cast) in (let TMP_261 \def (THead TMP_260 u t) in (let TMP_262 
\def (THeads TMP_259 vs TMP_261) in (let TMP_263 \def (lift1 is TMP_262) in 
(let TMP_264 \def (Flat Cast) in (let TMP_265 \def (THead TMP_264 u t) in 
(let TMP_266 \def (lifts1_flat Appl is TMP_265 vs) in (eq_ind_r T TMP_210 
TMP_213 TMP_258 TMP_263 
TMP_266))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) in (conj 
TMP_192 TMP_200 TMP_202 TMP_267))))))))))))) in (land_ind TMP_165 TMP_171 
TMP_186 TMP_268 H6)))))))))))))))))) in (land_ind TMP_139 TMP_146 TMP_161 
TMP_269 H3))))))))))))))))))))))))))) in (A_ind TMP_5 TMP_134 TMP_270 a))))).

theorem sc3_props__sc3_sn3_abst:
 \forall (g: G).(\forall (a: A).(land (\forall (c: C).(\forall (t: T).((sc3 g 
a c t) \to (sn3 c t)))) (\forall (vs: TList).(\forall (i: nat).(let t \def 
(THeads (Flat Appl) vs (TLRef i)) in (\forall (c: C).((arity g c t a) \to 
((nf2 c (TLRef i)) \to ((sns3 c vs) \to (sc3 g a c t))))))))))
\def
 \lambda (g: G).(\lambda (a: A).(let TMP_5 \def (\lambda (a0: A).(let TMP_1 
\def (\forall (c: C).(\forall (t: T).((sc3 g a0 c t) \to (sn3 c t)))) in (let 
TMP_4 \def (\forall (vs: TList).(\forall (i: nat).(let TMP_2 \def (Flat Appl) 
in (let TMP_3 \def (TLRef i) in (let t \def (THeads TMP_2 vs TMP_3) in 
(\forall (c: C).((arity g c t a0) \to ((nf2 c (TLRef i)) \to ((sns3 c vs) \to 
(sc3 g a0 c t)))))))))) in (land TMP_1 TMP_4)))) in (let TMP_34 \def (\lambda 
(n: nat).(\lambda (n0: nat).(let TMP_6 \def (\forall (c: C).(\forall (t: 
T).((land (arity g c t (ASort n n0)) (sn3 c t)) \to (sn3 c t)))) in (let 
TMP_16 \def (\forall (vs: TList).(\forall (i: nat).(\forall (c: C).((arity g 
c (THeads (Flat Appl) vs (TLRef i)) (ASort n n0)) \to ((nf2 c (TLRef i)) \to 
((sns3 c vs) \to (let TMP_7 \def (Flat Appl) in (let TMP_8 \def (TLRef i) in 
(let TMP_9 \def (THeads TMP_7 vs TMP_8) in (let TMP_10 \def (ASort n n0) in 
(let TMP_11 \def (arity g c TMP_9 TMP_10) in (let TMP_12 \def (Flat Appl) in 
(let TMP_13 \def (TLRef i) in (let TMP_14 \def (THeads TMP_12 vs TMP_13) in 
(let TMP_15 \def (sn3 c TMP_14) in (land TMP_11 TMP_15)))))))))))))))) in 
(let TMP_22 \def (\lambda (c: C).(\lambda (t: T).(\lambda (H: (land (arity g 
c t (ASort n n0)) (sn3 c t))).(let H0 \def H in (let TMP_17 \def (ASort n n0) 
in (let TMP_18 \def (arity g c t TMP_17) in (let TMP_19 \def (sn3 c t) in 
(let TMP_20 \def (sn3 c t) in (let TMP_21 \def (\lambda (_: (arity g c t 
(ASort n n0))).(\lambda (H2: (sn3 c t)).H2)) in (land_ind TMP_18 TMP_19 
TMP_20 TMP_21 H0)))))))))) in (let TMP_33 \def (\lambda (vs: TList).(\lambda 
(i: nat).(\lambda (c: C).(\lambda (H: (arity g c (THeads (Flat Appl) vs 
(TLRef i)) (ASort n n0))).(\lambda (H0: (nf2 c (TLRef i))).(\lambda (H1: 
(sns3 c vs)).(let TMP_23 \def (Flat Appl) in (let TMP_24 \def (TLRef i) in 
(let TMP_25 \def (THeads TMP_23 vs TMP_24) in (let TMP_26 \def (ASort n n0) 
in (let TMP_27 \def (arity g c TMP_25 TMP_26) in (let TMP_28 \def (Flat Appl) 
in (let TMP_29 \def (TLRef i) in (let TMP_30 \def (THeads TMP_28 vs TMP_29) 
in (let TMP_31 \def (sn3 c TMP_30) in (let TMP_32 \def (sn3_appls_lref c i H0 
vs H1) in (conj TMP_27 TMP_31 H TMP_32))))))))))))))))) in (conj TMP_6 TMP_16 
TMP_22 TMP_33))))))) in (let TMP_254 \def (\lambda (a0: A).(\lambda (H: (land 
(\forall (c: C).(\forall (t: T).((sc3 g a0 c t) \to (sn3 c t)))) (\forall 
(vs: TList).(\forall (i: nat).(\forall (c: C).((arity g c (THeads (Flat Appl) 
vs (TLRef i)) a0) \to ((nf2 c (TLRef i)) \to ((sns3 c vs) \to (sc3 g a0 c 
(THeads (Flat Appl) vs (TLRef i))))))))))).(\lambda (a1: A).(\lambda (H0: 
(land (\forall (c: C).(\forall (t: T).((sc3 g a1 c t) \to (sn3 c t)))) 
(\forall (vs: TList).(\forall (i: nat).(\forall (c: C).((arity g c (THeads 
(Flat Appl) vs (TLRef i)) a1) \to ((nf2 c (TLRef i)) \to ((sns3 c vs) \to 
(sc3 g a1 c (THeads (Flat Appl) vs (TLRef i))))))))))).(let TMP_35 \def 
(\forall (c: C).(\forall (t: T).((land (arity g c t (AHead a0 a1)) (\forall 
(d: C).(\forall (w: T).((sc3 g a0 d w) \to (\forall (is: PList).((drop1 is d 
c) \to (sc3 g a1 d (THead (Flat Appl) w (lift1 is t))))))))) \to (sn3 c t)))) 
in (let TMP_48 \def (\forall (vs: TList).(\forall (i: nat).(\forall (c: 
C).((arity g c (THeads (Flat Appl) vs (TLRef i)) (AHead a0 a1)) \to ((nf2 c 
(TLRef i)) \to ((sns3 c vs) \to (let TMP_36 \def (Flat Appl) in (let TMP_37 
\def (TLRef i) in (let TMP_38 \def (THeads TMP_36 vs TMP_37) in (let TMP_39 
\def (AHead a0 a1) in (let TMP_40 \def (arity g c TMP_38 TMP_39) in (let 
TMP_47 \def (\forall (d: C).(\forall (w: T).((sc3 g a0 d w) \to (\forall (is: 
PList).((drop1 is d c) \to (let TMP_41 \def (Flat Appl) in (let TMP_42 \def 
(Flat Appl) in (let TMP_43 \def (TLRef i) in (let TMP_44 \def (THeads TMP_42 
vs TMP_43) in (let TMP_45 \def (lift1 is TMP_44) in (let TMP_46 \def (THead 
TMP_41 w TMP_45) in (sc3 g a1 d TMP_46)))))))))))) in (land TMP_40 
TMP_47))))))))))))) in (let TMP_130 \def (\lambda (c: C).(\lambda (t: 
T).(\lambda (H1: (land (arity g c t (AHead a0 a1)) (\forall (d: C).(\forall 
(w: T).((sc3 g a0 d w) \to (\forall (is: PList).((drop1 is d c) \to (sc3 g a1 
d (THead (Flat Appl) w (lift1 is t)))))))))).(let H2 \def H in (let TMP_49 
\def (\forall (c0: C).(\forall (t0: T).((sc3 g a0 c0 t0) \to (sn3 c0 t0)))) 
in (let TMP_53 \def (\forall (vs: TList).(\forall (i: nat).(\forall (c0: 
C).((arity g c0 (THeads (Flat Appl) vs (TLRef i)) a0) \to ((nf2 c0 (TLRef i)) 
\to ((sns3 c0 vs) \to (let TMP_50 \def (Flat Appl) in (let TMP_51 \def (TLRef 
i) in (let TMP_52 \def (THeads TMP_50 vs TMP_51) in (sc3 g a0 c0 
TMP_52)))))))))) in (let TMP_54 \def (sn3 c t) in (let TMP_129 \def (\lambda 
(_: ((\forall (c0: C).(\forall (t0: T).((sc3 g a0 c0 t0) \to (sn3 c0 
t0)))))).(\lambda (H4: ((\forall (vs: TList).(\forall (i: nat).(\forall (c0: 
C).((arity g c0 (THeads (Flat Appl) vs (TLRef i)) a0) \to ((nf2 c0 (TLRef i)) 
\to ((sns3 c0 vs) \to (sc3 g a0 c0 (THeads (Flat Appl) vs (TLRef 
i))))))))))).(let H5 \def H0 in (let TMP_55 \def (\forall (c0: C).(\forall 
(t0: T).((sc3 g a1 c0 t0) \to (sn3 c0 t0)))) in (let TMP_59 \def (\forall 
(vs: TList).(\forall (i: nat).(\forall (c0: C).((arity g c0 (THeads (Flat 
Appl) vs (TLRef i)) a1) \to ((nf2 c0 (TLRef i)) \to ((sns3 c0 vs) \to (let 
TMP_56 \def (Flat Appl) in (let TMP_57 \def (TLRef i) in (let TMP_58 \def 
(THeads TMP_56 vs TMP_57) in (sc3 g a1 c0 TMP_58)))))))))) in (let TMP_60 
\def (sn3 c t) in (let TMP_128 \def (\lambda (H6: ((\forall (c0: C).(\forall 
(t0: T).((sc3 g a1 c0 t0) \to (sn3 c0 t0)))))).(\lambda (_: ((\forall (vs: 
TList).(\forall (i: nat).(\forall (c0: C).((arity g c0 (THeads (Flat Appl) vs 
(TLRef i)) a1) \to ((nf2 c0 (TLRef i)) \to ((sns3 c0 vs) \to (sc3 g a1 c0 
(THeads (Flat Appl) vs (TLRef i))))))))))).(let H8 \def H1 in (let TMP_61 
\def (AHead a0 a1) in (let TMP_62 \def (arity g c t TMP_61) in (let TMP_66 
\def (\forall (d: C).(\forall (w: T).((sc3 g a0 d w) \to (\forall (is: 
PList).((drop1 is d c) \to (let TMP_63 \def (Flat Appl) in (let TMP_64 \def 
(lift1 is t) in (let TMP_65 \def (THead TMP_63 w TMP_64) in (sc3 g a1 d 
TMP_65))))))))) in (let TMP_67 \def (sn3 c t) in (let TMP_127 \def (\lambda 
(H9: (arity g c t (AHead a0 a1))).(\lambda (H10: ((\forall (d: C).(\forall 
(w: T).((sc3 g a0 d w) \to (\forall (is: PList).((drop1 is d c) \to (sc3 g a1 
d (THead (Flat Appl) w (lift1 is t)))))))))).(let TMP_68 \def (AHead a0 a1) 
in (let H_y \def (arity_aprem g c t TMP_68 H9 O a0) in (let TMP_69 \def 
(aprem_zero a0 a1) in (let H11 \def (H_y TMP_69) in (let TMP_70 \def (\lambda 
(d: C).(\lambda (_: T).(\lambda (j: nat).(drop j O d c)))) in (let TMP_72 
\def (\lambda (d: C).(\lambda (u: T).(\lambda (_: nat).(let TMP_71 \def 
(asucc g a0) in (arity g d u TMP_71))))) in (let TMP_73 \def (sn3 c t) in 
(let TMP_126 \def (\lambda (x0: C).(\lambda (x1: T).(\lambda (x2: 
nat).(\lambda (H12: (drop x2 O x0 c)).(\lambda (H13: (arity g x0 x1 (asucc g 
a0))).(let TMP_74 \def (Bind Abst) in (let TMP_75 \def (CHead x0 TMP_74 x1) 
in (let TMP_76 \def (TLRef O) in (let TMP_77 \def (Bind Abst) in (let TMP_78 
\def (CHead x0 TMP_77 x1) in (let TMP_79 \def (Bind Abst) in (let TMP_80 \def 
(CHead x0 TMP_79 x1) in (let TMP_81 \def (getl_refl Abst x0 x1) in (let 
TMP_82 \def (arity_abst g TMP_80 x0 x1 O TMP_81 a0 H13) in (let TMP_83 \def 
(Bind Abst) in (let TMP_84 \def (CHead x0 TMP_83 x1) in (let TMP_85 \def 
(getl_refl Abst x0 x1) in (let TMP_86 \def (nf2_lref_abst TMP_84 x0 x1 O 
TMP_85) in (let TMP_87 \def (H4 TNil O TMP_78 TMP_82 TMP_86 I) in (let TMP_88 
\def (S x2) in (let TMP_89 \def (PCons TMP_88 O PNil) in (let H_y0 \def (H10 
TMP_75 TMP_76 TMP_87 TMP_89) in (let TMP_90 \def (Bind Abst) in (let TMP_91 
\def (CHead x0 TMP_90 x1) in (let TMP_92 \def (Flat Appl) in (let TMP_93 \def 
(TLRef O) in (let TMP_94 \def (S x2) in (let TMP_95 \def (lift TMP_94 O t) in 
(let TMP_96 \def (THead TMP_92 TMP_93 TMP_95) in (let TMP_97 \def (Bind Abst) 
in (let TMP_98 \def (CHead x0 TMP_97 x1) in (let TMP_99 \def (S x2) in (let 
TMP_100 \def (Bind Abst) in (let TMP_101 \def (drop_drop TMP_100 x2 x0 c H12 
x1) in (let TMP_102 \def (drop1_nil c) in (let TMP_103 \def (drop1_cons 
TMP_98 c TMP_99 O TMP_101 c PNil TMP_102) in (let TMP_104 \def (H_y0 TMP_103) 
in (let H_y1 \def (H6 TMP_91 TMP_96 TMP_104) in (let TMP_105 \def (Bind Abst) 
in (let TMP_106 \def (CHead x0 TMP_105 x1) in (let TMP_107 \def (TLRef O) in 
(let TMP_108 \def (S x2) in (let TMP_109 \def (lift TMP_108 O t) in (let H_x 
\def (sn3_gen_flat Appl TMP_106 TMP_107 TMP_109 H_y1) in (let H14 \def H_x in 
(let TMP_110 \def (Bind Abst) in (let TMP_111 \def (CHead x0 TMP_110 x1) in 
(let TMP_112 \def (TLRef O) in (let TMP_113 \def (sn3 TMP_111 TMP_112) in 
(let TMP_114 \def (Bind Abst) in (let TMP_115 \def (CHead x0 TMP_114 x1) in 
(let TMP_116 \def (S x2) in (let TMP_117 \def (lift TMP_116 O t) in (let 
TMP_118 \def (sn3 TMP_115 TMP_117) in (let TMP_119 \def (sn3 c t) in (let 
TMP_125 \def (\lambda (_: (sn3 (CHead x0 (Bind Abst) x1) (TLRef O))).(\lambda 
(H16: (sn3 (CHead x0 (Bind Abst) x1) (lift (S x2) O t))).(let TMP_120 \def 
(Bind Abst) in (let TMP_121 \def (CHead x0 TMP_120 x1) in (let TMP_122 \def 
(S x2) in (let TMP_123 \def (Bind Abst) in (let TMP_124 \def (drop_drop 
TMP_123 x2 x0 c H12 x1) in (sn3_gen_lift TMP_121 t TMP_122 O H16 c 
TMP_124)))))))) in (land_ind TMP_113 TMP_118 TMP_119 TMP_125 
H14))))))))))))))))))))))))))))))))))))))))))))))))))))))))) in (ex2_3_ind C 
T nat TMP_70 TMP_72 TMP_73 TMP_126 H11))))))))))) in (land_ind TMP_62 TMP_66 
TMP_67 TMP_127 H8))))))))) in (land_ind TMP_55 TMP_59 TMP_60 TMP_128 
H5)))))))) in (land_ind TMP_49 TMP_53 TMP_54 TMP_129 H2))))))))) in (let 
TMP_253 \def (\lambda (vs: TList).(\lambda (i: nat).(\lambda (c: C).(\lambda 
(H1: (arity g c (THeads (Flat Appl) vs (TLRef i)) (AHead a0 a1))).(\lambda 
(H2: (nf2 c (TLRef i))).(\lambda (H3: (sns3 c vs)).(let TMP_131 \def (Flat 
Appl) in (let TMP_132 \def (TLRef i) in (let TMP_133 \def (THeads TMP_131 vs 
TMP_132) in (let TMP_134 \def (AHead a0 a1) in (let TMP_135 \def (arity g c 
TMP_133 TMP_134) in (let TMP_142 \def (\forall (d: C).(\forall (w: T).((sc3 g 
a0 d w) \to (\forall (is: PList).((drop1 is d c) \to (let TMP_136 \def (Flat 
Appl) in (let TMP_137 \def (Flat Appl) in (let TMP_138 \def (TLRef i) in (let 
TMP_139 \def (THeads TMP_137 vs TMP_138) in (let TMP_140 \def (lift1 is 
TMP_139) in (let TMP_141 \def (THead TMP_136 w TMP_140) in (sc3 g a1 d 
TMP_141)))))))))))) in (let TMP_252 \def (\lambda (d: C).(\lambda (w: 
T).(\lambda (H4: (sc3 g a0 d w)).(\lambda (is: PList).(\lambda (H5: (drop1 is 
d c)).(let H6 \def H in (let TMP_143 \def (\forall (c0: C).(\forall (t: 
T).((sc3 g a0 c0 t) \to (sn3 c0 t)))) in (let TMP_147 \def (\forall (vs0: 
TList).(\forall (i0: nat).(\forall (c0: C).((arity g c0 (THeads (Flat Appl) 
vs0 (TLRef i0)) a0) \to ((nf2 c0 (TLRef i0)) \to ((sns3 c0 vs0) \to (let 
TMP_144 \def (Flat Appl) in (let TMP_145 \def (TLRef i0) in (let TMP_146 \def 
(THeads TMP_144 vs0 TMP_145) in (sc3 g a0 c0 TMP_146)))))))))) in (let 
TMP_148 \def (Flat Appl) in (let TMP_149 \def (Flat Appl) in (let TMP_150 
\def (TLRef i) in (let TMP_151 \def (THeads TMP_149 vs TMP_150) in (let 
TMP_152 \def (lift1 is TMP_151) in (let TMP_153 \def (THead TMP_148 w 
TMP_152) in (let TMP_154 \def (sc3 g a1 d TMP_153) in (let TMP_251 \def 
(\lambda (H7: ((\forall (c0: C).(\forall (t: T).((sc3 g a0 c0 t) \to (sn3 c0 
t)))))).(\lambda (_: ((\forall (vs0: TList).(\forall (i0: nat).(\forall (c0: 
C).((arity g c0 (THeads (Flat Appl) vs0 (TLRef i0)) a0) \to ((nf2 c0 (TLRef 
i0)) \to ((sns3 c0 vs0) \to (sc3 g a0 c0 (THeads (Flat Appl) vs0 (TLRef 
i0))))))))))).(let H9 \def H0 in (let TMP_155 \def (\forall (c0: C).(\forall 
(t: T).((sc3 g a1 c0 t) \to (sn3 c0 t)))) in (let TMP_159 \def (\forall (vs0: 
TList).(\forall (i0: nat).(\forall (c0: C).((arity g c0 (THeads (Flat Appl) 
vs0 (TLRef i0)) a1) \to ((nf2 c0 (TLRef i0)) \to ((sns3 c0 vs0) \to (let 
TMP_156 \def (Flat Appl) in (let TMP_157 \def (TLRef i0) in (let TMP_158 \def 
(THeads TMP_156 vs0 TMP_157) in (sc3 g a1 c0 TMP_158)))))))))) in (let 
TMP_160 \def (Flat Appl) in (let TMP_161 \def (Flat Appl) in (let TMP_162 
\def (TLRef i) in (let TMP_163 \def (THeads TMP_161 vs TMP_162) in (let 
TMP_164 \def (lift1 is TMP_163) in (let TMP_165 \def (THead TMP_160 w 
TMP_164) in (let TMP_166 \def (sc3 g a1 d TMP_165) in (let TMP_250 \def 
(\lambda (_: ((\forall (c0: C).(\forall (t: T).((sc3 g a1 c0 t) \to (sn3 c0 
t)))))).(\lambda (H11: ((\forall (vs0: TList).(\forall (i0: nat).(\forall 
(c0: C).((arity g c0 (THeads (Flat Appl) vs0 (TLRef i0)) a1) \to ((nf2 c0 
(TLRef i0)) \to ((sns3 c0 vs0) \to (sc3 g a1 c0 (THeads (Flat Appl) vs0 
(TLRef i0))))))))))).(let TMP_167 \def (lifts1 is vs) in (let TMP_168 \def 
(TCons w TMP_167) in (let H_y \def (H11 TMP_168) in (let TMP_169 \def (Flat 
Appl) in (let TMP_170 \def (lifts1 is vs) in (let TMP_171 \def (TLRef i) in 
(let TMP_172 \def (lift1 is TMP_171) in (let TMP_173 \def (THeads TMP_169 
TMP_170 TMP_172) in (let TMP_176 \def (\lambda (t: T).(let TMP_174 \def (Flat 
Appl) in (let TMP_175 \def (THead TMP_174 w t) in (sc3 g a1 d TMP_175)))) in 
(let TMP_177 \def (trans is i) in (let TMP_178 \def (TLRef TMP_177) in (let 
TMP_184 \def (\lambda (t: T).(let TMP_179 \def (Flat Appl) in (let TMP_180 
\def (Flat Appl) in (let TMP_181 \def (lifts1 is vs) in (let TMP_182 \def 
(THeads TMP_180 TMP_181 t) in (let TMP_183 \def (THead TMP_179 w TMP_182) in 
(sc3 g a1 d TMP_183))))))) in (let TMP_185 \def (trans is i) in (let TMP_186 
\def (TLRef i) in (let TMP_187 \def (lift1 is TMP_186) in (let TMP_193 \def 
(\lambda (t: T).(let TMP_188 \def (Flat Appl) in (let TMP_189 \def (Flat 
Appl) in (let TMP_190 \def (lifts1 is vs) in (let TMP_191 \def (THeads 
TMP_189 TMP_190 t) in (let TMP_192 \def (THead TMP_188 w TMP_191) in (arity g 
d TMP_192 a1))))))) in (let TMP_194 \def (Flat Appl) in (let TMP_195 \def 
(TLRef i) in (let TMP_196 \def (THeads TMP_194 vs TMP_195) in (let TMP_197 
\def (lift1 is TMP_196) in (let TMP_200 \def (\lambda (t: T).(let TMP_198 
\def (Flat Appl) in (let TMP_199 \def (THead TMP_198 w t) in (arity g d 
TMP_199 a1)))) in (let TMP_201 \def (sc3_arity_gen g d w a0 H4) in (let 
TMP_202 \def (Flat Appl) in (let TMP_203 \def (TLRef i) in (let TMP_204 \def 
(THeads TMP_202 vs TMP_203) in (let TMP_205 \def (lift1 is TMP_204) in (let 
TMP_206 \def (AHead a0 a1) in (let TMP_207 \def (Flat Appl) in (let TMP_208 
\def (TLRef i) in (let TMP_209 \def (THeads TMP_207 vs TMP_208) in (let 
TMP_210 \def (arity_lift1 g TMP_206 c is d TMP_209 H5 H1) in (let TMP_211 
\def (arity_appl g d w a0 TMP_201 TMP_205 a1 TMP_210) in (let TMP_212 \def 
(Flat Appl) in (let TMP_213 \def (lifts1 is vs) in (let TMP_214 \def (TLRef 
i) in (let TMP_215 \def (lift1 is TMP_214) in (let TMP_216 \def (THeads 
TMP_212 TMP_213 TMP_215) in (let TMP_217 \def (TLRef i) in (let TMP_218 \def 
(lifts1_flat Appl is TMP_217 vs) in (let TMP_219 \def (eq_ind T TMP_197 
TMP_200 TMP_211 TMP_216 TMP_218) in (let TMP_220 \def (trans is i) in (let 
TMP_221 \def (TLRef TMP_220) in (let TMP_222 \def (lift1_lref is i) in (let 
TMP_223 \def (eq_ind T TMP_187 TMP_193 TMP_219 TMP_221 TMP_222) in (let 
TMP_224 \def (TLRef i) in (let TMP_225 \def (lift1 is TMP_224) in (let 
TMP_226 \def (\lambda (t: T).(nf2 d t)) in (let TMP_227 \def (TLRef i) in 
(let TMP_228 \def (nf2_lift1 c is d TMP_227 H5 H2) in (let TMP_229 \def 
(trans is i) in (let TMP_230 \def (TLRef TMP_229) in (let TMP_231 \def 
(lift1_lref is i) in (let TMP_232 \def (eq_ind T TMP_225 TMP_226 TMP_228 
TMP_230 TMP_231) in (let TMP_233 \def (sn3 d w) in (let TMP_234 \def (lifts1 
is vs) in (let TMP_235 \def (sns3 d TMP_234) in (let TMP_236 \def (H7 d w H4) 
in (let TMP_237 \def (sns3_lifts1 c is d H5 vs H3) in (let TMP_238 \def (conj 
TMP_233 TMP_235 TMP_236 TMP_237) in (let TMP_239 \def (H_y TMP_185 d TMP_223 
TMP_232 TMP_238) in (let TMP_240 \def (TLRef i) in (let TMP_241 \def (lift1 
is TMP_240) in (let TMP_242 \def (lift1_lref is i) in (let TMP_243 \def 
(eq_ind_r T TMP_178 TMP_184 TMP_239 TMP_241 TMP_242) in (let TMP_244 \def 
(Flat Appl) in (let TMP_245 \def (TLRef i) in (let TMP_246 \def (THeads 
TMP_244 vs TMP_245) in (let TMP_247 \def (lift1 is TMP_246) in (let TMP_248 
\def (TLRef i) in (let TMP_249 \def (lifts1_flat Appl is TMP_248 vs) in 
(eq_ind_r T TMP_173 TMP_176 TMP_243 TMP_247 
TMP_249)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
)) in (land_ind TMP_155 TMP_159 TMP_166 TMP_250 H9)))))))))))))) in (land_ind 
TMP_143 TMP_147 TMP_154 TMP_251 H6))))))))))))))))) in (conj TMP_135 TMP_142 
H1 TMP_252)))))))))))))) in (conj TMP_35 TMP_48 TMP_130 TMP_253))))))))) in 
(A_ind TMP_5 TMP_34 TMP_254 a))))).

theorem sc3_sn3:
 \forall (g: G).(\forall (a: A).(\forall (c: C).(\forall (t: T).((sc3 g a c 
t) \to (sn3 c t)))))
\def
 \lambda (g: G).(\lambda (a: A).(\lambda (c: C).(\lambda (t: T).(\lambda (H: 
(sc3 g a c t)).(let H_x \def (sc3_props__sc3_sn3_abst g a) in (let H0 \def 
H_x in (let TMP_1 \def (\forall (c0: C).(\forall (t0: T).((sc3 g a c0 t0) \to 
(sn3 c0 t0)))) in (let TMP_5 \def (\forall (vs: TList).(\forall (i: 
nat).(\forall (c0: C).((arity g c0 (THeads (Flat Appl) vs (TLRef i)) a) \to 
((nf2 c0 (TLRef i)) \to ((sns3 c0 vs) \to (let TMP_2 \def (Flat Appl) in (let 
TMP_3 \def (TLRef i) in (let TMP_4 \def (THeads TMP_2 vs TMP_3) in (sc3 g a 
c0 TMP_4)))))))))) in (let TMP_6 \def (sn3 c t) in (let TMP_7 \def (\lambda 
(H1: ((\forall (c0: C).(\forall (t0: T).((sc3 g a c0 t0) \to (sn3 c0 
t0)))))).(\lambda (_: ((\forall (vs: TList).(\forall (i: nat).(\forall (c0: 
C).((arity g c0 (THeads (Flat Appl) vs (TLRef i)) a) \to ((nf2 c0 (TLRef i)) 
\to ((sns3 c0 vs) \to (sc3 g a c0 (THeads (Flat Appl) vs (TLRef 
i))))))))))).(H1 c t H))) in (land_ind TMP_1 TMP_5 TMP_6 TMP_7 H0))))))))))).

theorem sc3_abst:
 \forall (g: G).(\forall (a: A).(\forall (vs: TList).(\forall (c: C).(\forall 
(i: nat).((arity g c (THeads (Flat Appl) vs (TLRef i)) a) \to ((nf2 c (TLRef 
i)) \to ((sns3 c vs) \to (sc3 g a c (THeads (Flat Appl) vs (TLRef i))))))))))
\def
 \lambda (g: G).(\lambda (a: A).(\lambda (vs: TList).(\lambda (c: C).(\lambda 
(i: nat).(\lambda (H: (arity g c (THeads (Flat Appl) vs (TLRef i)) 
a)).(\lambda (H0: (nf2 c (TLRef i))).(\lambda (H1: (sns3 c vs)).(let H_x \def 
(sc3_props__sc3_sn3_abst g a) in (let H2 \def H_x in (let TMP_1 \def (\forall 
(c0: C).(\forall (t: T).((sc3 g a c0 t) \to (sn3 c0 t)))) in (let TMP_5 \def 
(\forall (vs0: TList).(\forall (i0: nat).(\forall (c0: C).((arity g c0 
(THeads (Flat Appl) vs0 (TLRef i0)) a) \to ((nf2 c0 (TLRef i0)) \to ((sns3 c0 
vs0) \to (let TMP_2 \def (Flat Appl) in (let TMP_3 \def (TLRef i0) in (let 
TMP_4 \def (THeads TMP_2 vs0 TMP_3) in (sc3 g a c0 TMP_4)))))))))) in (let 
TMP_6 \def (Flat Appl) in (let TMP_7 \def (TLRef i) in (let TMP_8 \def 
(THeads TMP_6 vs TMP_7) in (let TMP_9 \def (sc3 g a c TMP_8) in (let TMP_10 
\def (\lambda (_: ((\forall (c0: C).(\forall (t: T).((sc3 g a c0 t) \to (sn3 
c0 t)))))).(\lambda (H4: ((\forall (vs0: TList).(\forall (i0: nat).(\forall 
(c0: C).((arity g c0 (THeads (Flat Appl) vs0 (TLRef i0)) a) \to ((nf2 c0 
(TLRef i0)) \to ((sns3 c0 vs0) \to (sc3 g a c0 (THeads (Flat Appl) vs0 (TLRef 
i0))))))))))).(H4 vs i c H H0 H1))) in (land_ind TMP_1 TMP_5 TMP_9 TMP_10 
H2))))))))))))))))).

theorem sc3_bind:
 \forall (g: G).(\forall (b: B).((not (eq B b Abst)) \to (\forall (a1: 
A).(\forall (a2: A).(\forall (vs: TList).(\forall (c: C).(\forall (v: 
T).(\forall (t: T).((sc3 g a2 (CHead c (Bind b) v) (THeads (Flat Appl) (lifts 
(S O) O vs) t)) \to ((sc3 g a1 c v) \to (sc3 g a2 c (THeads (Flat Appl) vs 
(THead (Bind b) v t)))))))))))))
\def
 \lambda (g: G).(\lambda (b: B).(\lambda (H: (not (eq B b Abst))).(\lambda 
(a1: A).(\lambda (a2: A).(let TMP_5 \def (\lambda (a: A).(\forall (vs: 
TList).(\forall (c: C).(\forall (v: T).(\forall (t: T).((sc3 g a (CHead c 
(Bind b) v) (THeads (Flat Appl) (lifts (S O) O vs) t)) \to ((sc3 g a1 c v) 
\to (let TMP_1 \def (Flat Appl) in (let TMP_2 \def (Bind b) in (let TMP_3 
\def (THead TMP_2 v t) in (let TMP_4 \def (THeads TMP_1 vs TMP_3) in (sc3 g a 
c TMP_4)))))))))))) in (let TMP_50 \def (\lambda (n: nat).(\lambda (n0: 
nat).(\lambda (vs: TList).(\lambda (c: C).(\lambda (v: T).(\lambda (t: 
T).(\lambda (H0: (land (arity g (CHead c (Bind b) v) (THeads (Flat Appl) 
(lifts (S O) O vs) t) (ASort n n0)) (sn3 (CHead c (Bind b) v) (THeads (Flat 
Appl) (lifts (S O) O vs) t)))).(\lambda (H1: (sc3 g a1 c v)).(let H2 \def H0 
in (let TMP_6 \def (Bind b) in (let TMP_7 \def (CHead c TMP_6 v) in (let 
TMP_8 \def (Flat Appl) in (let TMP_9 \def (S O) in (let TMP_10 \def (lifts 
TMP_9 O vs) in (let TMP_11 \def (THeads TMP_8 TMP_10 t) in (let TMP_12 \def 
(ASort n n0) in (let TMP_13 \def (arity g TMP_7 TMP_11 TMP_12) in (let TMP_14 
\def (Bind b) in (let TMP_15 \def (CHead c TMP_14 v) in (let TMP_16 \def 
(Flat Appl) in (let TMP_17 \def (S O) in (let TMP_18 \def (lifts TMP_17 O vs) 
in (let TMP_19 \def (THeads TMP_16 TMP_18 t) in (let TMP_20 \def (sn3 TMP_15 
TMP_19) in (let TMP_21 \def (Flat Appl) in (let TMP_22 \def (Bind b) in (let 
TMP_23 \def (THead TMP_22 v t) in (let TMP_24 \def (THeads TMP_21 vs TMP_23) 
in (let TMP_25 \def (ASort n n0) in (let TMP_26 \def (arity g c TMP_24 
TMP_25) in (let TMP_27 \def (Flat Appl) in (let TMP_28 \def (Bind b) in (let 
TMP_29 \def (THead TMP_28 v t) in (let TMP_30 \def (THeads TMP_27 vs TMP_29) 
in (let TMP_31 \def (sn3 c TMP_30) in (let TMP_32 \def (land TMP_26 TMP_31) 
in (let TMP_49 \def (\lambda (H3: (arity g (CHead c (Bind b) v) (THeads (Flat 
Appl) (lifts (S O) O vs) t) (ASort n n0))).(\lambda (H4: (sn3 (CHead c (Bind 
b) v) (THeads (Flat Appl) (lifts (S O) O vs) t))).(let TMP_33 \def (Flat 
Appl) in (let TMP_34 \def (Bind b) in (let TMP_35 \def (THead TMP_34 v t) in 
(let TMP_36 \def (THeads TMP_33 vs TMP_35) in (let TMP_37 \def (ASort n n0) 
in (let TMP_38 \def (arity g c TMP_36 TMP_37) in (let TMP_39 \def (Flat Appl) 
in (let TMP_40 \def (Bind b) in (let TMP_41 \def (THead TMP_40 v t) in (let 
TMP_42 \def (THeads TMP_39 vs TMP_41) in (let TMP_43 \def (sn3 c TMP_42) in 
(let TMP_44 \def (sc3_arity_gen g c v a1 H1) in (let TMP_45 \def (ASort n n0) 
in (let TMP_46 \def (arity_appls_bind g b H c v a1 TMP_44 t vs TMP_45 H3) in 
(let TMP_47 \def (sc3_sn3 g a1 c v H1) in (let TMP_48 \def (sn3_appls_bind b 
H c v TMP_47 vs t H4) in (conj TMP_38 TMP_43 TMP_46 TMP_48))))))))))))))))))) 
in (land_ind TMP_13 TMP_20 TMP_32 TMP_49 
H2)))))))))))))))))))))))))))))))))))))) in (let TMP_206 \def (\lambda (a: 
A).(\lambda (_: ((\forall (vs: TList).(\forall (c: C).(\forall (v: 
T).(\forall (t: T).((sc3 g a (CHead c (Bind b) v) (THeads (Flat Appl) (lifts 
(S O) O vs) t)) \to ((sc3 g a1 c v) \to (sc3 g a c (THeads (Flat Appl) vs 
(THead (Bind b) v t))))))))))).(\lambda (a0: A).(\lambda (H1: ((\forall (vs: 
TList).(\forall (c: C).(\forall (v: T).(\forall (t: T).((sc3 g a0 (CHead c 
(Bind b) v) (THeads (Flat Appl) (lifts (S O) O vs) t)) \to ((sc3 g a1 c v) 
\to (sc3 g a0 c (THeads (Flat Appl) vs (THead (Bind b) v 
t))))))))))).(\lambda (vs: TList).(\lambda (c: C).(\lambda (v: T).(\lambda 
(t: T).(\lambda (H2: (land (arity g (CHead c (Bind b) v) (THeads (Flat Appl) 
(lifts (S O) O vs) t) (AHead a a0)) (\forall (d: C).(\forall (w: T).((sc3 g a 
d w) \to (\forall (is: PList).((drop1 is d (CHead c (Bind b) v)) \to (sc3 g 
a0 d (THead (Flat Appl) w (lift1 is (THeads (Flat Appl) (lifts (S O) O vs) 
t))))))))))).(\lambda (H3: (sc3 g a1 c v)).(let H4 \def H2 in (let TMP_51 
\def (Bind b) in (let TMP_52 \def (CHead c TMP_51 v) in (let TMP_53 \def 
(Flat Appl) in (let TMP_54 \def (S O) in (let TMP_55 \def (lifts TMP_54 O vs) 
in (let TMP_56 \def (THeads TMP_53 TMP_55 t) in (let TMP_57 \def (AHead a a0) 
in (let TMP_58 \def (arity g TMP_52 TMP_56 TMP_57) in (let TMP_66 \def 
(\forall (d: C).(\forall (w: T).((sc3 g a d w) \to (\forall (is: 
PList).((drop1 is d (CHead c (Bind b) v)) \to (let TMP_59 \def (Flat Appl) in 
(let TMP_60 \def (Flat Appl) in (let TMP_61 \def (S O) in (let TMP_62 \def 
(lifts TMP_61 O vs) in (let TMP_63 \def (THeads TMP_60 TMP_62 t) in (let 
TMP_64 \def (lift1 is TMP_63) in (let TMP_65 \def (THead TMP_59 w TMP_64) in 
(sc3 g a0 d TMP_65))))))))))))) in (let TMP_67 \def (Flat Appl) in (let 
TMP_68 \def (Bind b) in (let TMP_69 \def (THead TMP_68 v t) in (let TMP_70 
\def (THeads TMP_67 vs TMP_69) in (let TMP_71 \def (AHead a a0) in (let 
TMP_72 \def (arity g c TMP_70 TMP_71) in (let TMP_80 \def (\forall (d: 
C).(\forall (w: T).((sc3 g a d w) \to (\forall (is: PList).((drop1 is d c) 
\to (let TMP_73 \def (Flat Appl) in (let TMP_74 \def (Flat Appl) in (let 
TMP_75 \def (Bind b) in (let TMP_76 \def (THead TMP_75 v t) in (let TMP_77 
\def (THeads TMP_74 vs TMP_76) in (let TMP_78 \def (lift1 is TMP_77) in (let 
TMP_79 \def (THead TMP_73 w TMP_78) in (sc3 g a0 d TMP_79))))))))))))) in 
(let TMP_81 \def (land TMP_72 TMP_80) in (let TMP_205 \def (\lambda (H5: 
(arity g (CHead c (Bind b) v) (THeads (Flat Appl) (lifts (S O) O vs) t) 
(AHead a a0))).(\lambda (H6: ((\forall (d: C).(\forall (w: T).((sc3 g a d w) 
\to (\forall (is: PList).((drop1 is d (CHead c (Bind b) v)) \to (sc3 g a0 d 
(THead (Flat Appl) w (lift1 is (THeads (Flat Appl) (lifts (S O) O vs) 
t))))))))))).(let TMP_82 \def (Flat Appl) in (let TMP_83 \def (Bind b) in 
(let TMP_84 \def (THead TMP_83 v t) in (let TMP_85 \def (THeads TMP_82 vs 
TMP_84) in (let TMP_86 \def (AHead a a0) in (let TMP_87 \def (arity g c 
TMP_85 TMP_86) in (let TMP_95 \def (\forall (d: C).(\forall (w: T).((sc3 g a 
d w) \to (\forall (is: PList).((drop1 is d c) \to (let TMP_88 \def (Flat 
Appl) in (let TMP_89 \def (Flat Appl) in (let TMP_90 \def (Bind b) in (let 
TMP_91 \def (THead TMP_90 v t) in (let TMP_92 \def (THeads TMP_89 vs TMP_91) 
in (let TMP_93 \def (lift1 is TMP_92) in (let TMP_94 \def (THead TMP_88 w 
TMP_93) in (sc3 g a0 d TMP_94))))))))))))) in (let TMP_96 \def (sc3_arity_gen 
g c v a1 H3) in (let TMP_97 \def (AHead a a0) in (let TMP_98 \def 
(arity_appls_bind g b H c v a1 TMP_96 t vs TMP_97 H5) in (let TMP_204 \def 
(\lambda (d: C).(\lambda (w: T).(\lambda (H7: (sc3 g a d w)).(\lambda (is: 
PList).(\lambda (H8: (drop1 is d c)).(let TMP_99 \def (lifts1 is vs) in (let 
TMP_100 \def (TCons w TMP_99) in (let H_y \def (H1 TMP_100) in (let TMP_101 
\def (Flat Appl) in (let TMP_102 \def (lifts1 is vs) in (let TMP_103 \def 
(Bind b) in (let TMP_104 \def (THead TMP_103 v t) in (let TMP_105 \def (lift1 
is TMP_104) in (let TMP_106 \def (THeads TMP_101 TMP_102 TMP_105) in (let 
TMP_109 \def (\lambda (t0: T).(let TMP_107 \def (Flat Appl) in (let TMP_108 
\def (THead TMP_107 w t0) in (sc3 g a0 d TMP_108)))) in (let TMP_110 \def 
(Bind b) in (let TMP_111 \def (lift1 is v) in (let TMP_112 \def (Ss is) in 
(let TMP_113 \def (lift1 TMP_112 t) in (let TMP_114 \def (THead TMP_110 
TMP_111 TMP_113) in (let TMP_120 \def (\lambda (t0: T).(let TMP_115 \def 
(Flat Appl) in (let TMP_116 \def (Flat Appl) in (let TMP_117 \def (lifts1 is 
vs) in (let TMP_118 \def (THeads TMP_116 TMP_117 t0) in (let TMP_119 \def 
(THead TMP_115 w TMP_118) in (sc3 g a0 d TMP_119))))))) in (let TMP_121 \def 
(lift1 is v) in (let TMP_122 \def (Ss is) in (let TMP_123 \def (lift1 TMP_122 
t) in (let TMP_124 \def (Ss is) in (let TMP_125 \def (S O) in (let TMP_126 
\def (lifts TMP_125 O vs) in (let TMP_127 \def (lifts1 TMP_124 TMP_126) in 
(let TMP_139 \def (\lambda (t0: TList).(let TMP_128 \def (Bind b) in (let 
TMP_129 \def (lift1 is v) in (let TMP_130 \def (CHead d TMP_128 TMP_129) in 
(let TMP_131 \def (Flat Appl) in (let TMP_132 \def (S O) in (let TMP_133 \def 
(lift TMP_132 O w) in (let TMP_134 \def (Flat Appl) in (let TMP_135 \def (Ss 
is) in (let TMP_136 \def (lift1 TMP_135 t) in (let TMP_137 \def (THeads 
TMP_134 t0 TMP_136) in (let TMP_138 \def (THead TMP_131 TMP_133 TMP_137) in 
(sc3 g a0 TMP_130 TMP_138))))))))))))) in (let TMP_140 \def (Ss is) in (let 
TMP_141 \def (Flat Appl) in (let TMP_142 \def (S O) in (let TMP_143 \def 
(lifts TMP_142 O vs) in (let TMP_144 \def (THeads TMP_141 TMP_143 t) in (let 
TMP_145 \def (lift1 TMP_140 TMP_144) in (let TMP_153 \def (\lambda (t0: 
T).(let TMP_146 \def (Bind b) in (let TMP_147 \def (lift1 is v) in (let 
TMP_148 \def (CHead d TMP_146 TMP_147) in (let TMP_149 \def (Flat Appl) in 
(let TMP_150 \def (S O) in (let TMP_151 \def (lift TMP_150 O w) in (let 
TMP_152 \def (THead TMP_149 TMP_151 t0) in (sc3 g a0 TMP_148 TMP_152))))))))) 
in (let TMP_154 \def (Bind b) in (let TMP_155 \def (lift1 is v) in (let 
TMP_156 \def (CHead d TMP_154 TMP_155) in (let TMP_157 \def (S O) in (let 
TMP_158 \def (lift TMP_157 O w) in (let TMP_159 \def (Bind b) in (let TMP_160 
\def (lift1 is v) in (let TMP_161 \def (CHead d TMP_159 TMP_160) in (let 
TMP_162 \def (S O) in (let TMP_163 \def (Bind b) in (let TMP_164 \def 
(drop_refl d) in (let TMP_165 \def (lift1 is v) in (let TMP_166 \def 
(drop_drop TMP_163 O d d TMP_164 TMP_165) in (let TMP_167 \def (sc3_lift g a 
d w H7 TMP_161 TMP_162 O TMP_166) in (let TMP_168 \def (Ss is) in (let 
TMP_169 \def (drop1_skip_bind b c is d v H8) in (let TMP_170 \def (H6 TMP_156 
TMP_158 TMP_167 TMP_168 TMP_169) in (let TMP_171 \def (Flat Appl) in (let 
TMP_172 \def (Ss is) in (let TMP_173 \def (S O) in (let TMP_174 \def (lifts 
TMP_173 O vs) in (let TMP_175 \def (lifts1 TMP_172 TMP_174) in (let TMP_176 
\def (Ss is) in (let TMP_177 \def (lift1 TMP_176 t) in (let TMP_178 \def 
(THeads TMP_171 TMP_175 TMP_177) in (let TMP_179 \def (Ss is) in (let TMP_180 
\def (S O) in (let TMP_181 \def (lifts TMP_180 O vs) in (let TMP_182 \def 
(lifts1_flat Appl TMP_179 t TMP_181) in (let TMP_183 \def (eq_ind T TMP_145 
TMP_153 TMP_170 TMP_178 TMP_182) in (let TMP_184 \def (S O) in (let TMP_185 
\def (lifts1 is vs) in (let TMP_186 \def (lifts TMP_184 O TMP_185) in (let 
TMP_187 \def (lifts1_xhg is vs) in (let TMP_188 \def (eq_ind TList TMP_127 
TMP_139 TMP_183 TMP_186 TMP_187) in (let TMP_189 \def (sc3_lift1 g c a1 is d 
v H3 H8) in (let TMP_190 \def (H_y d TMP_121 TMP_123 TMP_188 TMP_189) in (let 
TMP_191 \def (Bind b) in (let TMP_192 \def (THead TMP_191 v t) in (let 
TMP_193 \def (lift1 is TMP_192) in (let TMP_194 \def (lift1_bind b is v t) in 
(let TMP_195 \def (eq_ind_r T TMP_114 TMP_120 TMP_190 TMP_193 TMP_194) in 
(let TMP_196 \def (Flat Appl) in (let TMP_197 \def (Bind b) in (let TMP_198 
\def (THead TMP_197 v t) in (let TMP_199 \def (THeads TMP_196 vs TMP_198) in 
(let TMP_200 \def (lift1 is TMP_199) in (let TMP_201 \def (Bind b) in (let 
TMP_202 \def (THead TMP_201 v t) in (let TMP_203 \def (lifts1_flat Appl is 
TMP_202 vs) in (eq_ind_r T TMP_106 TMP_109 TMP_195 TMP_200 
TMP_203)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
)))))))))))))))) in (conj TMP_87 TMP_95 TMP_98 TMP_204)))))))))))))) in 
(land_ind TMP_58 TMP_66 TMP_81 TMP_205 H4)))))))))))))))))))))))))))))) in 
(A_ind TMP_5 TMP_50 TMP_206 a2)))))))).

theorem sc3_appl:
 \forall (g: G).(\forall (a1: A).(\forall (a2: A).(\forall (vs: 
TList).(\forall (c: C).(\forall (v: T).(\forall (t: T).((sc3 g a2 c (THeads 
(Flat Appl) vs (THead (Bind Abbr) v t))) \to ((sc3 g a1 c v) \to (\forall (w: 
T).((sc3 g (asucc g a1) c w) \to (sc3 g a2 c (THeads (Flat Appl) vs (THead 
(Flat Appl) v (THead (Bind Abst) w t))))))))))))))
\def
 \lambda (g: G).(\lambda (a1: A).(\lambda (a2: A).(let TMP_7 \def (\lambda 
(a: A).(\forall (vs: TList).(\forall (c: C).(\forall (v: T).(\forall (t: 
T).((sc3 g a c (THeads (Flat Appl) vs (THead (Bind Abbr) v t))) \to ((sc3 g 
a1 c v) \to (\forall (w: T).((sc3 g (asucc g a1) c w) \to (let TMP_1 \def 
(Flat Appl) in (let TMP_2 \def (Flat Appl) in (let TMP_3 \def (Bind Abst) in 
(let TMP_4 \def (THead TMP_3 w t) in (let TMP_5 \def (THead TMP_2 v TMP_4) in 
(let TMP_6 \def (THeads TMP_1 vs TMP_5) in (sc3 g a c TMP_6)))))))))))))))) 
in (let TMP_59 \def (\lambda (n: nat).(\lambda (n0: nat).(\lambda (vs: 
TList).(\lambda (c: C).(\lambda (v: T).(\lambda (t: T).(\lambda (H: (land 
(arity g c (THeads (Flat Appl) vs (THead (Bind Abbr) v t)) (ASort n n0)) (sn3 
c (THeads (Flat Appl) vs (THead (Bind Abbr) v t))))).(\lambda (H0: (sc3 g a1 
c v)).(\lambda (w: T).(\lambda (H1: (sc3 g (asucc g a1) c w)).(let H2 \def H 
in (let TMP_8 \def (Flat Appl) in (let TMP_9 \def (Bind Abbr) in (let TMP_10 
\def (THead TMP_9 v t) in (let TMP_11 \def (THeads TMP_8 vs TMP_10) in (let 
TMP_12 \def (ASort n n0) in (let TMP_13 \def (arity g c TMP_11 TMP_12) in 
(let TMP_14 \def (Flat Appl) in (let TMP_15 \def (Bind Abbr) in (let TMP_16 
\def (THead TMP_15 v t) in (let TMP_17 \def (THeads TMP_14 vs TMP_16) in (let 
TMP_18 \def (sn3 c TMP_17) in (let TMP_19 \def (Flat Appl) in (let TMP_20 
\def (Flat Appl) in (let TMP_21 \def (Bind Abst) in (let TMP_22 \def (THead 
TMP_21 w t) in (let TMP_23 \def (THead TMP_20 v TMP_22) in (let TMP_24 \def 
(THeads TMP_19 vs TMP_23) in (let TMP_25 \def (ASort n n0) in (let TMP_26 
\def (arity g c TMP_24 TMP_25) in (let TMP_27 \def (Flat Appl) in (let TMP_28 
\def (Flat Appl) in (let TMP_29 \def (Bind Abst) in (let TMP_30 \def (THead 
TMP_29 w t) in (let TMP_31 \def (THead TMP_28 v TMP_30) in (let TMP_32 \def 
(THeads TMP_27 vs TMP_31) in (let TMP_33 \def (sn3 c TMP_32) in (let TMP_34 
\def (land TMP_26 TMP_33) in (let TMP_58 \def (\lambda (H3: (arity g c 
(THeads (Flat Appl) vs (THead (Bind Abbr) v t)) (ASort n n0))).(\lambda (H4: 
(sn3 c (THeads (Flat Appl) vs (THead (Bind Abbr) v t)))).(let TMP_35 \def 
(Flat Appl) in (let TMP_36 \def (Flat Appl) in (let TMP_37 \def (Bind Abst) 
in (let TMP_38 \def (THead TMP_37 w t) in (let TMP_39 \def (THead TMP_36 v 
TMP_38) in (let TMP_40 \def (THeads TMP_35 vs TMP_39) in (let TMP_41 \def 
(ASort n n0) in (let TMP_42 \def (arity g c TMP_40 TMP_41) in (let TMP_43 
\def (Flat Appl) in (let TMP_44 \def (Flat Appl) in (let TMP_45 \def (Bind 
Abst) in (let TMP_46 \def (THead TMP_45 w t) in (let TMP_47 \def (THead 
TMP_44 v TMP_46) in (let TMP_48 \def (THeads TMP_43 vs TMP_47) in (let TMP_49 
\def (sn3 c TMP_48) in (let TMP_50 \def (sc3_arity_gen g c v a1 H0) in (let 
TMP_51 \def (asucc g a1) in (let TMP_52 \def (sc3_arity_gen g c w TMP_51 H1) 
in (let TMP_53 \def (ASort n n0) in (let TMP_54 \def (arity_appls_appl g c v 
a1 TMP_50 w TMP_52 t vs TMP_53 H3) in (let TMP_55 \def (asucc g a1) in (let 
TMP_56 \def (sc3_sn3 g TMP_55 c w H1) in (let TMP_57 \def (sn3_appls_beta c v 
t vs H4 w TMP_56) in (conj TMP_42 TMP_49 TMP_54 
TMP_57)))))))))))))))))))))))))) in (land_ind TMP_13 TMP_18 TMP_34 TMP_58 
H2)))))))))))))))))))))))))))))))))))))))) in (let TMP_226 \def (\lambda (a: 
A).(\lambda (_: ((\forall (vs: TList).(\forall (c: C).(\forall (v: 
T).(\forall (t: T).((sc3 g a c (THeads (Flat Appl) vs (THead (Bind Abbr) v 
t))) \to ((sc3 g a1 c v) \to (\forall (w: T).((sc3 g (asucc g a1) c w) \to 
(sc3 g a c (THeads (Flat Appl) vs (THead (Flat Appl) v (THead (Bind Abst) w 
t)))))))))))))).(\lambda (a0: A).(\lambda (H0: ((\forall (vs: TList).(\forall 
(c: C).(\forall (v: T).(\forall (t: T).((sc3 g a0 c (THeads (Flat Appl) vs 
(THead (Bind Abbr) v t))) \to ((sc3 g a1 c v) \to (\forall (w: T).((sc3 g 
(asucc g a1) c w) \to (sc3 g a0 c (THeads (Flat Appl) vs (THead (Flat Appl) v 
(THead (Bind Abst) w t)))))))))))))).(\lambda (vs: TList).(\lambda (c: 
C).(\lambda (v: T).(\lambda (t: T).(\lambda (H1: (land (arity g c (THeads 
(Flat Appl) vs (THead (Bind Abbr) v t)) (AHead a a0)) (\forall (d: 
C).(\forall (w: T).((sc3 g a d w) \to (\forall (is: PList).((drop1 is d c) 
\to (sc3 g a0 d (THead (Flat Appl) w (lift1 is (THeads (Flat Appl) vs (THead 
(Bind Abbr) v t)))))))))))).(\lambda (H2: (sc3 g a1 c v)).(\lambda (w: 
T).(\lambda (H3: (sc3 g (asucc g a1) c w)).(let H4 \def H1 in (let TMP_60 
\def (Flat Appl) in (let TMP_61 \def (Bind Abbr) in (let TMP_62 \def (THead 
TMP_61 v t) in (let TMP_63 \def (THeads TMP_60 vs TMP_62) in (let TMP_64 \def 
(AHead a a0) in (let TMP_65 \def (arity g c TMP_63 TMP_64) in (let TMP_73 
\def (\forall (d: C).(\forall (w0: T).((sc3 g a d w0) \to (\forall (is: 
PList).((drop1 is d c) \to (let TMP_66 \def (Flat Appl) in (let TMP_67 \def 
(Flat Appl) in (let TMP_68 \def (Bind Abbr) in (let TMP_69 \def (THead TMP_68 
v t) in (let TMP_70 \def (THeads TMP_67 vs TMP_69) in (let TMP_71 \def (lift1 
is TMP_70) in (let TMP_72 \def (THead TMP_66 w0 TMP_71) in (sc3 g a0 d 
TMP_72))))))))))))) in (let TMP_74 \def (Flat Appl) in (let TMP_75 \def (Flat 
Appl) in (let TMP_76 \def (Bind Abst) in (let TMP_77 \def (THead TMP_76 w t) 
in (let TMP_78 \def (THead TMP_75 v TMP_77) in (let TMP_79 \def (THeads 
TMP_74 vs TMP_78) in (let TMP_80 \def (AHead a a0) in (let TMP_81 \def (arity 
g c TMP_79 TMP_80) in (let TMP_91 \def (\forall (d: C).(\forall (w0: T).((sc3 
g a d w0) \to (\forall (is: PList).((drop1 is d c) \to (let TMP_82 \def (Flat 
Appl) in (let TMP_83 \def (Flat Appl) in (let TMP_84 \def (Flat Appl) in (let 
TMP_85 \def (Bind Abst) in (let TMP_86 \def (THead TMP_85 w t) in (let TMP_87 
\def (THead TMP_84 v TMP_86) in (let TMP_88 \def (THeads TMP_83 vs TMP_87) in 
(let TMP_89 \def (lift1 is TMP_88) in (let TMP_90 \def (THead TMP_82 w0 
TMP_89) in (sc3 g a0 d TMP_90))))))))))))))) in (let TMP_92 \def (land TMP_81 
TMP_91) in (let TMP_225 \def (\lambda (H5: (arity g c (THeads (Flat Appl) vs 
(THead (Bind Abbr) v t)) (AHead a a0))).(\lambda (H6: ((\forall (d: 
C).(\forall (w0: T).((sc3 g a d w0) \to (\forall (is: PList).((drop1 is d c) 
\to (sc3 g a0 d (THead (Flat Appl) w0 (lift1 is (THeads (Flat Appl) vs (THead 
(Bind Abbr) v t)))))))))))).(let TMP_93 \def (Flat Appl) in (let TMP_94 \def 
(Flat Appl) in (let TMP_95 \def (Bind Abst) in (let TMP_96 \def (THead TMP_95 
w t) in (let TMP_97 \def (THead TMP_94 v TMP_96) in (let TMP_98 \def (THeads 
TMP_93 vs TMP_97) in (let TMP_99 \def (AHead a a0) in (let TMP_100 \def 
(arity g c TMP_98 TMP_99) in (let TMP_110 \def (\forall (d: C).(\forall (w0: 
T).((sc3 g a d w0) \to (\forall (is: PList).((drop1 is d c) \to (let TMP_101 
\def (Flat Appl) in (let TMP_102 \def (Flat Appl) in (let TMP_103 \def (Flat 
Appl) in (let TMP_104 \def (Bind Abst) in (let TMP_105 \def (THead TMP_104 w 
t) in (let TMP_106 \def (THead TMP_103 v TMP_105) in (let TMP_107 \def 
(THeads TMP_102 vs TMP_106) in (let TMP_108 \def (lift1 is TMP_107) in (let 
TMP_109 \def (THead TMP_101 w0 TMP_108) in (sc3 g a0 d TMP_109))))))))))))))) 
in (let TMP_111 \def (sc3_arity_gen g c v a1 H2) in (let TMP_112 \def (asucc 
g a1) in (let TMP_113 \def (sc3_arity_gen g c w TMP_112 H3) in (let TMP_114 
\def (AHead a a0) in (let TMP_115 \def (arity_appls_appl g c v a1 TMP_111 w 
TMP_113 t vs TMP_114 H5) in (let TMP_224 \def (\lambda (d: C).(\lambda (w0: 
T).(\lambda (H7: (sc3 g a d w0)).(\lambda (is: PList).(\lambda (H8: (drop1 is 
d c)).(let TMP_116 \def (Flat Appl) in (let TMP_117 \def (lifts1 is vs) in 
(let TMP_118 \def (Flat Appl) in (let TMP_119 \def (Bind Abst) in (let 
TMP_120 \def (THead TMP_119 w t) in (let TMP_121 \def (THead TMP_118 v 
TMP_120) in (let TMP_122 \def (lift1 is TMP_121) in (let TMP_123 \def (THeads 
TMP_116 TMP_117 TMP_122) in (let TMP_126 \def (\lambda (t0: T).(let TMP_124 
\def (Flat Appl) in (let TMP_125 \def (THead TMP_124 w0 t0) in (sc3 g a0 d 
TMP_125)))) in (let TMP_127 \def (Flat Appl) in (let TMP_128 \def (lift1 is 
v) in (let TMP_129 \def (Bind Abst) in (let TMP_130 \def (THead TMP_129 w t) 
in (let TMP_131 \def (lift1 is TMP_130) in (let TMP_132 \def (THead TMP_127 
TMP_128 TMP_131) in (let TMP_138 \def (\lambda (t0: T).(let TMP_133 \def 
(Flat Appl) in (let TMP_134 \def (Flat Appl) in (let TMP_135 \def (lifts1 is 
vs) in (let TMP_136 \def (THeads TMP_134 TMP_135 t0) in (let TMP_137 \def 
(THead TMP_133 w0 TMP_136) in (sc3 g a0 d TMP_137))))))) in (let TMP_139 \def 
(Bind Abst) in (let TMP_140 \def (lift1 is w) in (let TMP_141 \def (Ss is) in 
(let TMP_142 \def (lift1 TMP_141 t) in (let TMP_143 \def (THead TMP_139 
TMP_140 TMP_142) in (let TMP_152 \def (\lambda (t0: T).(let TMP_144 \def 
(Flat Appl) in (let TMP_145 \def (Flat Appl) in (let TMP_146 \def (lifts1 is 
vs) in (let TMP_147 \def (Flat Appl) in (let TMP_148 \def (lift1 is v) in 
(let TMP_149 \def (THead TMP_147 TMP_148 t0) in (let TMP_150 \def (THeads 
TMP_145 TMP_146 TMP_149) in (let TMP_151 \def (THead TMP_144 w0 TMP_150) in 
(sc3 g a0 d TMP_151)))))))))) in (let TMP_153 \def (lifts1 is vs) in (let 
TMP_154 \def (TCons w0 TMP_153) in (let H_y \def (H0 TMP_154) in (let TMP_155 
\def (lift1 is v) in (let TMP_156 \def (Ss is) in (let TMP_157 \def (lift1 
TMP_156 t) in (let TMP_158 \def (Bind Abbr) in (let TMP_159 \def (THead 
TMP_158 v t) in (let TMP_160 \def (lift1 is TMP_159) in (let TMP_166 \def 
(\lambda (t0: T).(let TMP_161 \def (Flat Appl) in (let TMP_162 \def (Flat 
Appl) in (let TMP_163 \def (lifts1 is vs) in (let TMP_164 \def (THeads 
TMP_162 TMP_163 t0) in (let TMP_165 \def (THead TMP_161 w0 TMP_164) in (sc3 g 
a0 d TMP_165))))))) in (let TMP_167 \def (Flat Appl) in (let TMP_168 \def 
(Bind Abbr) in (let TMP_169 \def (THead TMP_168 v t) in (let TMP_170 \def 
(THeads TMP_167 vs TMP_169) in (let TMP_171 \def (lift1 is TMP_170) in (let 
TMP_174 \def (\lambda (t0: T).(let TMP_172 \def (Flat Appl) in (let TMP_173 
\def (THead TMP_172 w0 t0) in (sc3 g a0 d TMP_173)))) in (let TMP_175 \def 
(H6 d w0 H7 is H8) in (let TMP_176 \def (Flat Appl) in (let TMP_177 \def 
(lifts1 is vs) in (let TMP_178 \def (Bind Abbr) in (let TMP_179 \def (THead 
TMP_178 v t) in (let TMP_180 \def (lift1 is TMP_179) in (let TMP_181 \def 
(THeads TMP_176 TMP_177 TMP_180) in (let TMP_182 \def (Bind Abbr) in (let 
TMP_183 \def (THead TMP_182 v t) in (let TMP_184 \def (lifts1_flat Appl is 
TMP_183 vs) in (let TMP_185 \def (eq_ind T TMP_171 TMP_174 TMP_175 TMP_181 
TMP_184) in (let TMP_186 \def (Bind Abbr) in (let TMP_187 \def (lift1 is v) 
in (let TMP_188 \def (Ss is) in (let TMP_189 \def (lift1 TMP_188 t) in (let 
TMP_190 \def (THead TMP_186 TMP_187 TMP_189) in (let TMP_191 \def (lift1_bind 
Abbr is v t) in (let TMP_192 \def (eq_ind T TMP_160 TMP_166 TMP_185 TMP_190 
TMP_191) in (let TMP_193 \def (sc3_lift1 g c a1 is d v H2 H8) in (let TMP_194 
\def (lift1 is w) in (let TMP_195 \def (asucc g a1) in (let TMP_196 \def 
(sc3_lift1 g c TMP_195 is d w H3 H8) in (let TMP_197 \def (H_y d TMP_155 
TMP_157 TMP_192 TMP_193 TMP_194 TMP_196) in (let TMP_198 \def (Bind Abst) in 
(let TMP_199 \def (THead TMP_198 w t) in (let TMP_200 \def (lift1 is TMP_199) 
in (let TMP_201 \def (lift1_bind Abst is w t) in (let TMP_202 \def (eq_ind_r 
T TMP_143 TMP_152 TMP_197 TMP_200 TMP_201) in (let TMP_203 \def (Flat Appl) 
in (let TMP_204 \def (Bind Abst) in (let TMP_205 \def (THead TMP_204 w t) in 
(let TMP_206 \def (THead TMP_203 v TMP_205) in (let TMP_207 \def (lift1 is 
TMP_206) in (let TMP_208 \def (Bind Abst) in (let TMP_209 \def (THead TMP_208 
w t) in (let TMP_210 \def (lift1_flat Appl is v TMP_209) in (let TMP_211 \def 
(eq_ind_r T TMP_132 TMP_138 TMP_202 TMP_207 TMP_210) in (let TMP_212 \def 
(Flat Appl) in (let TMP_213 \def (Flat Appl) in (let TMP_214 \def (Bind Abst) 
in (let TMP_215 \def (THead TMP_214 w t) in (let TMP_216 \def (THead TMP_213 
v TMP_215) in (let TMP_217 \def (THeads TMP_212 vs TMP_216) in (let TMP_218 
\def (lift1 is TMP_217) in (let TMP_219 \def (Flat Appl) in (let TMP_220 \def 
(Bind Abst) in (let TMP_221 \def (THead TMP_220 w t) in (let TMP_222 \def 
(THead TMP_219 v TMP_221) in (let TMP_223 \def (lifts1_flat Appl is TMP_222 
vs) in (eq_ind_r T TMP_123 TMP_126 TMP_211 TMP_218 
TMP_223)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
)))))))))))))))))))))) in (conj TMP_100 TMP_110 TMP_115 
TMP_224)))))))))))))))))) in (land_ind TMP_65 TMP_73 TMP_92 TMP_225 
H4)))))))))))))))))))))))))))))))) in (A_ind TMP_7 TMP_59 TMP_226 a2)))))).

