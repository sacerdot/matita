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

set "baseuri" "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/pr2/subst1".

include "pr2/defs.ma".

include "pr0/subst1.ma".

include "csubst1/defs.ma".

include "subst1/subst1.ma".

include "getl/props.ma".

theorem pr2_delta1:
 \forall (c: C).(\forall (d: C).(\forall (u: T).(\forall (i: nat).((getl i c 
(CHead d (Bind Abbr) u)) \to (\forall (t1: T).(\forall (t2: T).((pr0 t1 t2) 
\to (\forall (t: T).((subst1 i u t2 t) \to (pr2 c t1 t))))))))))
\def
 \lambda (c: C).(\lambda (d: C).(\lambda (u: T).(\lambda (i: nat).(\lambda 
(H: (getl i c (CHead d (Bind Abbr) u))).(\lambda (t1: T).(\lambda (t2: 
T).(\lambda (H0: (pr0 t1 t2)).(\lambda (t: T).(\lambda (H1: (subst1 i u t2 
t)).(subst1_ind i u t2 (\lambda (t0: T).(pr2 c t1 t0)) (pr2_free c t1 t2 H0) 
(\lambda (t0: T).(\lambda (H2: (subst0 i u t2 t0)).(pr2_delta c d u i H t1 t2 
H0 t0 H2))) t H1)))))))))).

theorem pr2_subst1:
 \forall (c: C).(\forall (e: C).(\forall (v: T).(\forall (i: nat).((getl i c 
(CHead e (Bind Abbr) v)) \to (\forall (t1: T).(\forall (t2: T).((pr2 c t1 t2) 
\to (\forall (w1: T).((subst1 i v t1 w1) \to (ex2 T (\lambda (w2: T).(pr2 c 
w1 w2)) (\lambda (w2: T).(subst1 i v t2 w2))))))))))))
\def
 \lambda (c: C).(\lambda (e: C).(\lambda (v: T).(\lambda (i: nat).(\lambda 
(H: (getl i c (CHead e (Bind Abbr) v))).(\lambda (t1: T).(\lambda (t2: 
T).(\lambda (H0: (pr2 c t1 t2)).(let H1 \def (match H0 in pr2 return (\lambda 
(c0: C).(\lambda (t: T).(\lambda (t0: T).(\lambda (_: (pr2 c0 t t0)).((eq C 
c0 c) \to ((eq T t t1) \to ((eq T t0 t2) \to (\forall (w1: T).((subst1 i v t1 
w1) \to (ex2 T (\lambda (w2: T).(pr2 c w1 w2)) (\lambda (w2: T).(subst1 i v 
t2 w2)))))))))))) with [(pr2_free c0 t0 t3 H1) \Rightarrow (\lambda (H2: (eq 
C c0 c)).(\lambda (H3: (eq T t0 t1)).(\lambda (H4: (eq T t3 t2)).(eq_ind C c 
(\lambda (_: C).((eq T t0 t1) \to ((eq T t3 t2) \to ((pr0 t0 t3) \to (\forall 
(w1: T).((subst1 i v t1 w1) \to (ex2 T (\lambda (w2: T).(pr2 c w1 w2)) 
(\lambda (w2: T).(subst1 i v t2 w2))))))))) (\lambda (H5: (eq T t0 
t1)).(eq_ind T t1 (\lambda (t: T).((eq T t3 t2) \to ((pr0 t t3) \to (\forall 
(w1: T).((subst1 i v t1 w1) \to (ex2 T (\lambda (w2: T).(pr2 c w1 w2)) 
(\lambda (w2: T).(subst1 i v t2 w2)))))))) (\lambda (H6: (eq T t3 
t2)).(eq_ind T t2 (\lambda (t: T).((pr0 t1 t) \to (\forall (w1: T).((subst1 i 
v t1 w1) \to (ex2 T (\lambda (w2: T).(pr2 c w1 w2)) (\lambda (w2: T).(subst1 
i v t2 w2))))))) (\lambda (H7: (pr0 t1 t2)).(\lambda (w1: T).(\lambda (H8: 
(subst1 i v t1 w1)).(ex2_ind T (\lambda (w2: T).(pr0 w1 w2)) (\lambda (w2: 
T).(subst1 i v t2 w2)) (ex2 T (\lambda (w2: T).(pr2 c w1 w2)) (\lambda (w2: 
T).(subst1 i v t2 w2))) (\lambda (x: T).(\lambda (H9: (pr0 w1 x)).(\lambda 
(H10: (subst1 i v t2 x)).(ex_intro2 T (\lambda (w2: T).(pr2 c w1 w2)) 
(\lambda (w2: T).(subst1 i v t2 w2)) x (pr2_free c w1 x H9) H10)))) 
(pr0_subst1 t1 t2 H7 v w1 i H8 v (pr0_refl v)))))) t3 (sym_eq T t3 t2 H6))) 
t0 (sym_eq T t0 t1 H5))) c0 (sym_eq C c0 c H2) H3 H4 H1)))) | (pr2_delta c0 d 
u i0 H1 t0 t3 H2 t H3) \Rightarrow (\lambda (H4: (eq C c0 c)).(\lambda (H5: 
(eq T t0 t1)).(\lambda (H6: (eq T t t2)).(eq_ind C c (\lambda (c1: C).((eq T 
t0 t1) \to ((eq T t t2) \to ((getl i0 c1 (CHead d (Bind Abbr) u)) \to ((pr0 
t0 t3) \to ((subst0 i0 u t3 t) \to (\forall (w1: T).((subst1 i v t1 w1) \to 
(ex2 T (\lambda (w2: T).(pr2 c w1 w2)) (\lambda (w2: T).(subst1 i v t2 
w2))))))))))) (\lambda (H7: (eq T t0 t1)).(eq_ind T t1 (\lambda (t4: T).((eq 
T t t2) \to ((getl i0 c (CHead d (Bind Abbr) u)) \to ((pr0 t4 t3) \to 
((subst0 i0 u t3 t) \to (\forall (w1: T).((subst1 i v t1 w1) \to (ex2 T 
(\lambda (w2: T).(pr2 c w1 w2)) (\lambda (w2: T).(subst1 i v t2 w2)))))))))) 
(\lambda (H8: (eq T t t2)).(eq_ind T t2 (\lambda (t4: T).((getl i0 c (CHead d 
(Bind Abbr) u)) \to ((pr0 t1 t3) \to ((subst0 i0 u t3 t4) \to (\forall (w1: 
T).((subst1 i v t1 w1) \to (ex2 T (\lambda (w2: T).(pr2 c w1 w2)) (\lambda 
(w2: T).(subst1 i v t2 w2))))))))) (\lambda (H9: (getl i0 c (CHead d (Bind 
Abbr) u))).(\lambda (H10: (pr0 t1 t3)).(\lambda (H11: (subst0 i0 u t3 
t2)).(\lambda (w1: T).(\lambda (H12: (subst1 i v t1 w1)).(ex2_ind T (\lambda 
(w2: T).(pr0 w1 w2)) (\lambda (w2: T).(subst1 i v t3 w2)) (ex2 T (\lambda 
(w2: T).(pr2 c w1 w2)) (\lambda (w2: T).(subst1 i v t2 w2))) (\lambda (x: 
T).(\lambda (H13: (pr0 w1 x)).(\lambda (H14: (subst1 i v t3 x)).(neq_eq_e i 
i0 (ex2 T (\lambda (w2: T).(pr2 c w1 w2)) (\lambda (w2: T).(subst1 i v t2 
w2))) (\lambda (H15: (not (eq nat i i0))).(ex2_ind T (\lambda (t4: T).(subst1 
i v t2 t4)) (\lambda (t4: T).(subst1 i0 u x t4)) (ex2 T (\lambda (w2: T).(pr2 
c w1 w2)) (\lambda (w2: T).(subst1 i v t2 w2))) (\lambda (x0: T).(\lambda 
(H16: (subst1 i v t2 x0)).(\lambda (H17: (subst1 i0 u x x0)).(ex_intro2 T 
(\lambda (w2: T).(pr2 c w1 w2)) (\lambda (w2: T).(subst1 i v t2 w2)) x0 
(pr2_delta1 c d u i0 H9 w1 x H13 x0 H17) H16)))) (subst1_confluence_neq t3 t2 
u i0 (subst1_single i0 u t3 t2 H11) x v i H14 (sym_not_eq nat i i0 H15)))) 
(\lambda (H15: (eq nat i i0)).(let H16 \def (eq_ind_r nat i0 (\lambda (n: 
nat).(subst0 n u t3 t2)) H11 i H15) in (let H17 \def (eq_ind_r nat i0 
(\lambda (n: nat).(getl n c (CHead d (Bind Abbr) u))) H9 i H15) in (let H18 
\def (eq_ind C (CHead e (Bind Abbr) v) (\lambda (c1: C).(getl i c c1)) H 
(CHead d (Bind Abbr) u) (getl_mono c (CHead e (Bind Abbr) v) i H (CHead d 
(Bind Abbr) u) H17)) in (let H19 \def (f_equal C C (\lambda (e0: C).(match e0 
in C return (\lambda (_: C).C) with [(CSort _) \Rightarrow e | (CHead c1 _ _) 
\Rightarrow c1])) (CHead e (Bind Abbr) v) (CHead d (Bind Abbr) u) (getl_mono 
c (CHead e (Bind Abbr) v) i H (CHead d (Bind Abbr) u) H17)) in ((let H20 \def 
(f_equal C T (\lambda (e0: C).(match e0 in C return (\lambda (_: C).T) with 
[(CSort _) \Rightarrow v | (CHead _ _ t4) \Rightarrow t4])) (CHead e (Bind 
Abbr) v) (CHead d (Bind Abbr) u) (getl_mono c (CHead e (Bind Abbr) v) i H 
(CHead d (Bind Abbr) u) H17)) in (\lambda (H21: (eq C e d)).(let H22 \def 
(eq_ind_r T u (\lambda (t4: T).(getl i c (CHead d (Bind Abbr) t4))) H18 v 
H20) in (let H23 \def (eq_ind_r T u (\lambda (t4: T).(subst0 i t4 t3 t2)) H16 
v H20) in (let H24 \def (eq_ind_r C d (\lambda (c1: C).(getl i c (CHead c1 
(Bind Abbr) v))) H22 e H21) in (ex2_ind T (\lambda (t4: T).(subst1 i v t2 
t4)) (\lambda (t4: T).(subst1 i v x t4)) (ex2 T (\lambda (w2: T).(pr2 c w1 
w2)) (\lambda (w2: T).(subst1 i v t2 w2))) (\lambda (x0: T).(\lambda (H25: 
(subst1 i v t2 x0)).(\lambda (H26: (subst1 i v x x0)).(ex_intro2 T (\lambda 
(w2: T).(pr2 c w1 w2)) (\lambda (w2: T).(subst1 i v t2 w2)) x0 (pr2_delta1 c 
e v i H24 w1 x H13 x0 H26) H25)))) (subst1_confluence_eq t3 t2 v i 
(subst1_single i v t3 t2 H23) x H14))))))) H19)))))))))) (pr0_subst1 t1 t3 
H10 v w1 i H12 v (pr0_refl v)))))))) t (sym_eq T t t2 H8))) t0 (sym_eq T t0 
t1 H7))) c0 (sym_eq C c0 c H4) H5 H6 H1 H2 H3))))]) in (H1 (refl_equal C c) 
(refl_equal T t1) (refl_equal T t2)))))))))).

axiom pr2_gen_cabbr:
 \forall (c: C).(\forall (t1: T).(\forall (t2: T).((pr2 c t1 t2) \to (\forall 
(e: C).(\forall (u: T).(\forall (d: nat).((getl d c (CHead e (Bind Abbr) u)) 
\to (\forall (a0: C).((csubst1 d u c a0) \to (\forall (a: C).((drop (S O) d 
a0 a) \to (\forall (x1: T).((subst1 d u t1 (lift (S O) d x1)) \to (ex2 T 
(\lambda (x2: T).(subst1 d u t2 (lift (S O) d x2))) (\lambda (x2: T).(pr2 a 
x1 x2))))))))))))))))
.

