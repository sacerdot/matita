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

include "Basic-1/pr3/defs.ma".

include "Basic-1/pr2/subst1.ma".

theorem pr3_subst1:
 \forall (c: C).(\forall (e: C).(\forall (v: T).(\forall (i: nat).((getl i c 
(CHead e (Bind Abbr) v)) \to (\forall (t1: T).(\forall (t2: T).((pr3 c t1 t2) 
\to (\forall (w1: T).((subst1 i v t1 w1) \to (ex2 T (\lambda (w2: T).(pr3 c 
w1 w2)) (\lambda (w2: T).(subst1 i v t2 w2))))))))))))
\def
 \lambda (c: C).(\lambda (e: C).(\lambda (v: T).(\lambda (i: nat).(\lambda 
(H: (getl i c (CHead e (Bind Abbr) v))).(\lambda (t1: T).(\lambda (t2: 
T).(\lambda (H0: (pr3 c t1 t2)).(pr3_ind c (\lambda (t: T).(\lambda (t0: 
T).(\forall (w1: T).((subst1 i v t w1) \to (ex2 T (\lambda (w2: T).(pr3 c w1 
w2)) (\lambda (w2: T).(subst1 i v t0 w2))))))) (\lambda (t: T).(\lambda (w1: 
T).(\lambda (H1: (subst1 i v t w1)).(ex_intro2 T (\lambda (w2: T).(pr3 c w1 
w2)) (\lambda (w2: T).(subst1 i v t w2)) w1 (pr3_refl c w1) H1)))) (\lambda 
(t3: T).(\lambda (t4: T).(\lambda (H1: (pr2 c t4 t3)).(\lambda (t5: 
T).(\lambda (_: (pr3 c t3 t5)).(\lambda (H3: ((\forall (w1: T).((subst1 i v 
t3 w1) \to (ex2 T (\lambda (w2: T).(pr3 c w1 w2)) (\lambda (w2: T).(subst1 i 
v t5 w2))))))).(\lambda (w1: T).(\lambda (H4: (subst1 i v t4 w1)).(ex2_ind T 
(\lambda (w2: T).(pr2 c w1 w2)) (\lambda (w2: T).(subst1 i v t3 w2)) (ex2 T 
(\lambda (w2: T).(pr3 c w1 w2)) (\lambda (w2: T).(subst1 i v t5 w2))) 
(\lambda (x: T).(\lambda (H5: (pr2 c w1 x)).(\lambda (H6: (subst1 i v t3 
x)).(ex2_ind T (\lambda (w2: T).(pr3 c x w2)) (\lambda (w2: T).(subst1 i v t5 
w2)) (ex2 T (\lambda (w2: T).(pr3 c w1 w2)) (\lambda (w2: T).(subst1 i v t5 
w2))) (\lambda (x0: T).(\lambda (H7: (pr3 c x x0)).(\lambda (H8: (subst1 i v 
t5 x0)).(ex_intro2 T (\lambda (w2: T).(pr3 c w1 w2)) (\lambda (w2: T).(subst1 
i v t5 w2)) x0 (pr3_sing c x w1 H5 x0 H7) H8)))) (H3 x H6))))) (pr2_subst1 c 
e v i H t4 t3 H1 w1 H4)))))))))) t1 t2 H0)))))))).
(* COMMENTS
Initial nodes: 425
END *)

theorem pr3_gen_cabbr:
 \forall (c: C).(\forall (t1: T).(\forall (t2: T).((pr3 c t1 t2) \to (\forall 
(e: C).(\forall (u: T).(\forall (d: nat).((getl d c (CHead e (Bind Abbr) u)) 
\to (\forall (a0: C).((csubst1 d u c a0) \to (\forall (a: C).((drop (S O) d 
a0 a) \to (\forall (x1: T).((subst1 d u t1 (lift (S O) d x1)) \to (ex2 T 
(\lambda (x2: T).(subst1 d u t2 (lift (S O) d x2))) (\lambda (x2: T).(pr3 a 
x1 x2))))))))))))))))
\def
 \lambda (c: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H: (pr3 c t1 
t2)).(pr3_ind c (\lambda (t: T).(\lambda (t0: T).(\forall (e: C).(\forall (u: 
T).(\forall (d: nat).((getl d c (CHead e (Bind Abbr) u)) \to (\forall (a0: 
C).((csubst1 d u c a0) \to (\forall (a: C).((drop (S O) d a0 a) \to (\forall 
(x1: T).((subst1 d u t (lift (S O) d x1)) \to (ex2 T (\lambda (x2: T).(subst1 
d u t0 (lift (S O) d x2))) (\lambda (x2: T).(pr3 a x1 x2))))))))))))))) 
(\lambda (t: T).(\lambda (e: C).(\lambda (u: T).(\lambda (d: nat).(\lambda 
(_: (getl d c (CHead e (Bind Abbr) u))).(\lambda (a0: C).(\lambda (_: 
(csubst1 d u c a0)).(\lambda (a: C).(\lambda (_: (drop (S O) d a0 
a)).(\lambda (x1: T).(\lambda (H3: (subst1 d u t (lift (S O) d 
x1))).(ex_intro2 T (\lambda (x2: T).(subst1 d u t (lift (S O) d x2))) 
(\lambda (x2: T).(pr3 a x1 x2)) x1 H3 (pr3_refl a x1))))))))))))) (\lambda 
(t0: T).(\lambda (t3: T).(\lambda (H0: (pr2 c t3 t0)).(\lambda (t4: 
T).(\lambda (_: (pr3 c t0 t4)).(\lambda (H2: ((\forall (e: C).(\forall (u: 
T).(\forall (d: nat).((getl d c (CHead e (Bind Abbr) u)) \to (\forall (a0: 
C).((csubst1 d u c a0) \to (\forall (a: C).((drop (S O) d a0 a) \to (\forall 
(x1: T).((subst1 d u t0 (lift (S O) d x1)) \to (ex2 T (\lambda (x2: 
T).(subst1 d u t4 (lift (S O) d x2))) (\lambda (x2: T).(pr3 a x1 
x2))))))))))))))).(\lambda (e: C).(\lambda (u: T).(\lambda (d: nat).(\lambda 
(H3: (getl d c (CHead e (Bind Abbr) u))).(\lambda (a0: C).(\lambda (H4: 
(csubst1 d u c a0)).(\lambda (a: C).(\lambda (H5: (drop (S O) d a0 
a)).(\lambda (x1: T).(\lambda (H6: (subst1 d u t3 (lift (S O) d 
x1))).(ex2_ind T (\lambda (x2: T).(subst1 d u t0 (lift (S O) d x2))) (\lambda 
(x2: T).(pr2 a x1 x2)) (ex2 T (\lambda (x2: T).(subst1 d u t4 (lift (S O) d 
x2))) (\lambda (x2: T).(pr3 a x1 x2))) (\lambda (x: T).(\lambda (H7: (subst1 
d u t0 (lift (S O) d x))).(\lambda (H8: (pr2 a x1 x)).(ex2_ind T (\lambda 
(x2: T).(subst1 d u t4 (lift (S O) d x2))) (\lambda (x2: T).(pr3 a x x2)) 
(ex2 T (\lambda (x2: T).(subst1 d u t4 (lift (S O) d x2))) (\lambda (x2: 
T).(pr3 a x1 x2))) (\lambda (x0: T).(\lambda (H9: (subst1 d u t4 (lift (S O) 
d x0))).(\lambda (H10: (pr3 a x x0)).(ex_intro2 T (\lambda (x2: T).(subst1 d 
u t4 (lift (S O) d x2))) (\lambda (x2: T).(pr3 a x1 x2)) x0 H9 (pr3_sing a x 
x1 H8 x0 H10))))) (H2 e u d H3 a0 H4 a H5 x H7))))) (pr2_gen_cabbr c t3 t0 H0 
e u d H3 a0 H4 a H5 x1 H6)))))))))))))))))) t1 t2 H)))).
(* COMMENTS
Initial nodes: 731
END *)

