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

include "Basic-1/csubc/arity.ma".

include "Basic-1/csubc/getl.ma".

include "Basic-1/csubc/drop1.ma".

include "Basic-1/csubc/props.ma".

theorem sc3_arity_csubc:
 \forall (g: G).(\forall (c1: C).(\forall (t: T).(\forall (a: A).((arity g c1 
t a) \to (\forall (d1: C).(\forall (is: PList).((drop1 is d1 c1) \to (\forall 
(c2: C).((csubc g d1 c2) \to (sc3 g a c2 (lift1 is t)))))))))))
\def
 \lambda (g: G).(\lambda (c1: C).(\lambda (t: T).(\lambda (a: A).(\lambda (H: 
(arity g c1 t a)).(arity_ind g (\lambda (c: C).(\lambda (t0: T).(\lambda (a0: 
A).(\forall (d1: C).(\forall (is: PList).((drop1 is d1 c) \to (\forall (c2: 
C).((csubc g d1 c2) \to (sc3 g a0 c2 (lift1 is t0)))))))))) (\lambda (c: 
C).(\lambda (n: nat).(\lambda (d1: C).(\lambda (is: PList).(\lambda (_: 
(drop1 is d1 c)).(\lambda (c2: C).(\lambda (_: (csubc g d1 c2)).(eq_ind_r T 
(TSort n) (\lambda (t0: T).(land (arity g c2 t0 (ASort O n)) (sn3 c2 t0))) 
(conj (arity g c2 (TSort n) (ASort O n)) (sn3 c2 (TSort n)) (arity_sort g c2 
n) (sn3_nf2 c2 (TSort n) (nf2_sort c2 n))) (lift1 is (TSort n)) (lift1_sort n 
is))))))))) (\lambda (c: C).(\lambda (d: C).(\lambda (u: T).(\lambda (i: 
nat).(\lambda (H0: (getl i c (CHead d (Bind Abbr) u))).(\lambda (a0: 
A).(\lambda (_: (arity g d u a0)).(\lambda (H2: ((\forall (d1: C).(\forall 
(is: PList).((drop1 is d1 d) \to (\forall (c2: C).((csubc g d1 c2) \to (sc3 g 
a0 c2 (lift1 is u))))))))).(\lambda (d1: C).(\lambda (is: PList).(\lambda 
(H3: (drop1 is d1 c)).(\lambda (c2: C).(\lambda (H4: (csubc g d1 c2)).(let 
H_x \def (drop1_getl_trans is c d1 H3 Abbr d u i H0) in (let H5 \def H_x in 
(ex2_ind C (\lambda (e2: C).(drop1 (ptrans is i) e2 d)) (\lambda (e2: 
C).(getl (trans is i) d1 (CHead e2 (Bind Abbr) (lift1 (ptrans is i) u)))) 
(sc3 g a0 c2 (lift1 is (TLRef i))) (\lambda (x: C).(\lambda (_: (drop1 
(ptrans is i) x d)).(\lambda (H7: (getl (trans is i) d1 (CHead x (Bind Abbr) 
(lift1 (ptrans is i) u)))).(let H_x0 \def (csubc_getl_conf g d1 (CHead x 
(Bind Abbr) (lift1 (ptrans is i) u)) (trans is i) H7 c2 H4) in (let H8 \def 
H_x0 in (ex2_ind C (\lambda (e2: C).(getl (trans is i) c2 e2)) (\lambda (e2: 
C).(csubc g (CHead x (Bind Abbr) (lift1 (ptrans is i) u)) e2)) (sc3 g a0 c2 
(lift1 is (TLRef i))) (\lambda (x0: C).(\lambda (H9: (getl (trans is i) c2 
x0)).(\lambda (H10: (csubc g (CHead x (Bind Abbr) (lift1 (ptrans is i) u)) 
x0)).(let H_x1 \def (csubc_gen_head_l g x x0 (lift1 (ptrans is i) u) (Bind 
Abbr) H10) in (let H11 \def H_x1 in (or3_ind (ex2 C (\lambda (c3: C).(eq C x0 
(CHead c3 (Bind Abbr) (lift1 (ptrans is i) u)))) (\lambda (c3: C).(csubc g x 
c3))) (ex5_3 C T A (\lambda (_: C).(\lambda (_: T).(\lambda (_: A).(eq K 
(Bind Abbr) (Bind Abst))))) (\lambda (c3: C).(\lambda (w: T).(\lambda (_: 
A).(eq C x0 (CHead c3 (Bind Abbr) w))))) (\lambda (c3: C).(\lambda (_: 
T).(\lambda (_: A).(csubc g x c3)))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a1: A).(sc3 g (asucc g a1) x (lift1 (ptrans is i) u))))) (\lambda (c3: 
C).(\lambda (w: T).(\lambda (a1: A).(sc3 g a1 c3 w))))) (ex4_3 B C T (\lambda 
(b: B).(\lambda (c3: C).(\lambda (v2: T).(eq C x0 (CHead c3 (Bind b) v2))))) 
(\lambda (_: B).(\lambda (_: C).(\lambda (_: T).(eq K (Bind Abbr) (Bind 
Void))))) (\lambda (b: B).(\lambda (_: C).(\lambda (_: T).(not (eq B b 
Void))))) (\lambda (_: B).(\lambda (c3: C).(\lambda (_: T).(csubc g x c3))))) 
(sc3 g a0 c2 (lift1 is (TLRef i))) (\lambda (H12: (ex2 C (\lambda (c3: C).(eq 
C x0 (CHead c3 (Bind Abbr) (lift1 (ptrans is i) u)))) (\lambda (c3: C).(csubc 
g x c3)))).(ex2_ind C (\lambda (c3: C).(eq C x0 (CHead c3 (Bind Abbr) (lift1 
(ptrans is i) u)))) (\lambda (c3: C).(csubc g x c3)) (sc3 g a0 c2 (lift1 is 
(TLRef i))) (\lambda (x1: C).(\lambda (H13: (eq C x0 (CHead x1 (Bind Abbr) 
(lift1 (ptrans is i) u)))).(\lambda (_: (csubc g x x1)).(let H15 \def (eq_ind 
C x0 (\lambda (c0: C).(getl (trans is i) c2 c0)) H9 (CHead x1 (Bind Abbr) 
(lift1 (ptrans is i) u)) H13) in (let H_y \def (sc3_abbr g a0 TNil) in 
(eq_ind_r T (TLRef (trans is i)) (\lambda (t0: T).(sc3 g a0 c2 t0)) (H_y 
(trans is i) x1 (lift1 (ptrans is i) u) c2 (eq_ind T (lift1 is (lift (S i) O 
u)) (\lambda (t0: T).(sc3 g a0 c2 t0)) (eq_ind T (lift1 (PConsTail is (S i) 
O) u) (\lambda (t0: T).(sc3 g a0 c2 t0)) (H2 d1 (PConsTail is (S i) O) 
(drop1_cons_tail c d (S i) O (getl_drop Abbr c d u i H0) is d1 H3) c2 H4) 
(lift1 is (lift (S i) O u)) (lift1_cons_tail u (S i) O is)) (lift (S (trans 
is i)) O (lift1 (ptrans is i) u)) (lift1_free is i u)) H15) (lift1 is (TLRef 
i)) (lift1_lref is i))))))) H12)) (\lambda (H12: (ex5_3 C T A (\lambda (_: 
C).(\lambda (_: T).(\lambda (_: A).(eq K (Bind Abbr) (Bind Abst))))) (\lambda 
(c3: C).(\lambda (w: T).(\lambda (_: A).(eq C x0 (CHead c3 (Bind Abbr) w))))) 
(\lambda (c3: C).(\lambda (_: T).(\lambda (_: A).(csubc g x c3)))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a1: A).(sc3 g (asucc g a1) x (lift1 (ptrans 
is i) u))))) (\lambda (c3: C).(\lambda (w: T).(\lambda (a1: A).(sc3 g a1 c3 
w)))))).(ex5_3_ind C T A (\lambda (_: C).(\lambda (_: T).(\lambda (_: A).(eq 
K (Bind Abbr) (Bind Abst))))) (\lambda (c3: C).(\lambda (w: T).(\lambda (_: 
A).(eq C x0 (CHead c3 (Bind Abbr) w))))) (\lambda (c3: C).(\lambda (_: 
T).(\lambda (_: A).(csubc g x c3)))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a1: A).(sc3 g (asucc g a1) x (lift1 (ptrans is i) u))))) (\lambda (c3: 
C).(\lambda (w: T).(\lambda (a1: A).(sc3 g a1 c3 w)))) (sc3 g a0 c2 (lift1 is 
(TLRef i))) (\lambda (x1: C).(\lambda (x2: T).(\lambda (x3: A).(\lambda (H13: 
(eq K (Bind Abbr) (Bind Abst))).(\lambda (H14: (eq C x0 (CHead x1 (Bind Abbr) 
x2))).(\lambda (_: (csubc g x x1)).(\lambda (_: (sc3 g (asucc g x3) x (lift1 
(ptrans is i) u))).(\lambda (_: (sc3 g x3 x1 x2)).(let H18 \def (eq_ind C x0 
(\lambda (c0: C).(getl (trans is i) c2 c0)) H9 (CHead x1 (Bind Abbr) x2) H14) 
in (let H19 \def (eq_ind K (Bind Abbr) (\lambda (ee: K).(match ee in K return 
(\lambda (_: K).Prop) with [(Bind b) \Rightarrow (match b in B return 
(\lambda (_: B).Prop) with [Abbr \Rightarrow True | Abst \Rightarrow False | 
Void \Rightarrow False]) | (Flat _) \Rightarrow False])) I (Bind Abst) H13) 
in (False_ind (sc3 g a0 c2 (lift1 is (TLRef i))) H19))))))))))) H12)) 
(\lambda (H12: (ex4_3 B C T (\lambda (b: B).(\lambda (c3: C).(\lambda (v2: 
T).(eq C x0 (CHead c3 (Bind b) v2))))) (\lambda (_: B).(\lambda (_: 
C).(\lambda (_: T).(eq K (Bind Abbr) (Bind Void))))) (\lambda (b: B).(\lambda 
(_: C).(\lambda (_: T).(not (eq B b Void))))) (\lambda (_: B).(\lambda (c3: 
C).(\lambda (_: T).(csubc g x c3)))))).(ex4_3_ind B C T (\lambda (b: 
B).(\lambda (c3: C).(\lambda (v2: T).(eq C x0 (CHead c3 (Bind b) v2))))) 
(\lambda (_: B).(\lambda (_: C).(\lambda (_: T).(eq K (Bind Abbr) (Bind 
Void))))) (\lambda (b: B).(\lambda (_: C).(\lambda (_: T).(not (eq B b 
Void))))) (\lambda (_: B).(\lambda (c3: C).(\lambda (_: T).(csubc g x c3)))) 
(sc3 g a0 c2 (lift1 is (TLRef i))) (\lambda (x1: B).(\lambda (x2: C).(\lambda 
(x3: T).(\lambda (H13: (eq C x0 (CHead x2 (Bind x1) x3))).(\lambda (H14: (eq 
K (Bind Abbr) (Bind Void))).(\lambda (_: (not (eq B x1 Void))).(\lambda (_: 
(csubc g x x2)).(let H17 \def (eq_ind C x0 (\lambda (c0: C).(getl (trans is 
i) c2 c0)) H9 (CHead x2 (Bind x1) x3) H13) in (let H18 \def (eq_ind K (Bind 
Abbr) (\lambda (ee: K).(match ee in K return (\lambda (_: K).Prop) with 
[(Bind b) \Rightarrow (match b in B return (\lambda (_: B).Prop) with [Abbr 
\Rightarrow True | Abst \Rightarrow False | Void \Rightarrow False]) | (Flat 
_) \Rightarrow False])) I (Bind Void) H14) in (False_ind (sc3 g a0 c2 (lift1 
is (TLRef i))) H18)))))))))) H12)) H11)))))) H8)))))) H5)))))))))))))))) 
(\lambda (c: C).(\lambda (d: C).(\lambda (u: T).(\lambda (i: nat).(\lambda 
(H0: (getl i c (CHead d (Bind Abst) u))).(\lambda (a0: A).(\lambda (H1: 
(arity g d u (asucc g a0))).(\lambda (_: ((\forall (d1: C).(\forall (is: 
PList).((drop1 is d1 d) \to (\forall (c2: C).((csubc g d1 c2) \to (sc3 g 
(asucc g a0) c2 (lift1 is u))))))))).(\lambda (d1: C).(\lambda (is: 
PList).(\lambda (H3: (drop1 is d1 c)).(\lambda (c2: C).(\lambda (H4: (csubc g 
d1 c2)).(let H5 \def H0 in (let H_x \def (drop1_getl_trans is c d1 H3 Abst d 
u i H5) in (let H6 \def H_x in (ex2_ind C (\lambda (e2: C).(drop1 (ptrans is 
i) e2 d)) (\lambda (e2: C).(getl (trans is i) d1 (CHead e2 (Bind Abst) (lift1 
(ptrans is i) u)))) (sc3 g a0 c2 (lift1 is (TLRef i))) (\lambda (x: 
C).(\lambda (H7: (drop1 (ptrans is i) x d)).(\lambda (H8: (getl (trans is i) 
d1 (CHead x (Bind Abst) (lift1 (ptrans is i) u)))).(let H_x0 \def 
(csubc_getl_conf g d1 (CHead x (Bind Abst) (lift1 (ptrans is i) u)) (trans is 
i) H8 c2 H4) in (let H9 \def H_x0 in (ex2_ind C (\lambda (e2: C).(getl (trans 
is i) c2 e2)) (\lambda (e2: C).(csubc g (CHead x (Bind Abst) (lift1 (ptrans 
is i) u)) e2)) (sc3 g a0 c2 (lift1 is (TLRef i))) (\lambda (x0: C).(\lambda 
(H10: (getl (trans is i) c2 x0)).(\lambda (H11: (csubc g (CHead x (Bind Abst) 
(lift1 (ptrans is i) u)) x0)).(let H_x1 \def (csubc_gen_head_l g x x0 (lift1 
(ptrans is i) u) (Bind Abst) H11) in (let H12 \def H_x1 in (or3_ind (ex2 C 
(\lambda (c3: C).(eq C x0 (CHead c3 (Bind Abst) (lift1 (ptrans is i) u)))) 
(\lambda (c3: C).(csubc g x c3))) (ex5_3 C T A (\lambda (_: C).(\lambda (_: 
T).(\lambda (_: A).(eq K (Bind Abst) (Bind Abst))))) (\lambda (c3: 
C).(\lambda (w: T).(\lambda (_: A).(eq C x0 (CHead c3 (Bind Abbr) w))))) 
(\lambda (c3: C).(\lambda (_: T).(\lambda (_: A).(csubc g x c3)))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a1: A).(sc3 g (asucc g a1) x (lift1 (ptrans 
is i) u))))) (\lambda (c3: C).(\lambda (w: T).(\lambda (a1: A).(sc3 g a1 c3 
w))))) (ex4_3 B C T (\lambda (b: B).(\lambda (c3: C).(\lambda (v2: T).(eq C 
x0 (CHead c3 (Bind b) v2))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: 
T).(eq K (Bind Abst) (Bind Void))))) (\lambda (b: B).(\lambda (_: C).(\lambda 
(_: T).(not (eq B b Void))))) (\lambda (_: B).(\lambda (c3: C).(\lambda (_: 
T).(csubc g x c3))))) (sc3 g a0 c2 (lift1 is (TLRef i))) (\lambda (H13: (ex2 
C (\lambda (c3: C).(eq C x0 (CHead c3 (Bind Abst) (lift1 (ptrans is i) u)))) 
(\lambda (c3: C).(csubc g x c3)))).(ex2_ind C (\lambda (c3: C).(eq C x0 
(CHead c3 (Bind Abst) (lift1 (ptrans is i) u)))) (\lambda (c3: C).(csubc g x 
c3)) (sc3 g a0 c2 (lift1 is (TLRef i))) (\lambda (x1: C).(\lambda (H14: (eq C 
x0 (CHead x1 (Bind Abst) (lift1 (ptrans is i) u)))).(\lambda (_: (csubc g x 
x1)).(let H16 \def (eq_ind C x0 (\lambda (c0: C).(getl (trans is i) c2 c0)) 
H10 (CHead x1 (Bind Abst) (lift1 (ptrans is i) u)) H14) in (let H_y \def 
(sc3_abst g a0 TNil) in (eq_ind_r T (TLRef (trans is i)) (\lambda (t0: 
T).(sc3 g a0 c2 t0)) (H_y c2 (trans is i) (csubc_arity_conf g d1 c2 H4 (TLRef 
(trans is i)) a0 (eq_ind T (lift1 is (TLRef i)) (\lambda (t0: T).(arity g d1 
t0 a0)) (arity_lift1 g a0 c is d1 (TLRef i) H3 (arity_abst g c d u i H0 a0 
H1)) (TLRef (trans is i)) (lift1_lref is i))) (nf2_lref_abst c2 x1 (lift1 
(ptrans is i) u) (trans is i) H16) I) (lift1 is (TLRef i)) (lift1_lref is 
i))))))) H13)) (\lambda (H13: (ex5_3 C T A (\lambda (_: C).(\lambda (_: 
T).(\lambda (_: A).(eq K (Bind Abst) (Bind Abst))))) (\lambda (c3: 
C).(\lambda (w: T).(\lambda (_: A).(eq C x0 (CHead c3 (Bind Abbr) w))))) 
(\lambda (c3: C).(\lambda (_: T).(\lambda (_: A).(csubc g x c3)))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a1: A).(sc3 g (asucc g a1) x (lift1 (ptrans 
is i) u))))) (\lambda (c3: C).(\lambda (w: T).(\lambda (a1: A).(sc3 g a1 c3 
w)))))).(ex5_3_ind C T A (\lambda (_: C).(\lambda (_: T).(\lambda (_: A).(eq 
K (Bind Abst) (Bind Abst))))) (\lambda (c3: C).(\lambda (w: T).(\lambda (_: 
A).(eq C x0 (CHead c3 (Bind Abbr) w))))) (\lambda (c3: C).(\lambda (_: 
T).(\lambda (_: A).(csubc g x c3)))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a1: A).(sc3 g (asucc g a1) x (lift1 (ptrans is i) u))))) (\lambda (c3: 
C).(\lambda (w: T).(\lambda (a1: A).(sc3 g a1 c3 w)))) (sc3 g a0 c2 (lift1 is 
(TLRef i))) (\lambda (x1: C).(\lambda (x2: T).(\lambda (x3: A).(\lambda (_: 
(eq K (Bind Abst) (Bind Abst))).(\lambda (H15: (eq C x0 (CHead x1 (Bind Abbr) 
x2))).(\lambda (_: (csubc g x x1)).(\lambda (H17: (sc3 g (asucc g x3) x 
(lift1 (ptrans is i) u))).(\lambda (H18: (sc3 g x3 x1 x2)).(let H19 \def 
(eq_ind C x0 (\lambda (c0: C).(getl (trans is i) c2 c0)) H10 (CHead x1 (Bind 
Abbr) x2) H15) in (let H_y \def (sc3_abbr g a0 TNil) in (eq_ind_r T (TLRef 
(trans is i)) (\lambda (t0: T).(sc3 g a0 c2 t0)) (H_y (trans is i) x1 x2 c2 
(let H_y0 \def (arity_lift1 g (asucc g a0) d (ptrans is i) x u H7 H1) in (let 
H_y1 \def (sc3_arity_gen g x (lift1 (ptrans is i) u) (asucc g x3) H17) in 
(sc3_repl g x3 c2 (lift (S (trans is i)) O x2) (sc3_lift g x3 x1 x2 H18 c2 (S 
(trans is i)) O (getl_drop Abbr c2 x1 x2 (trans is i) H19)) a0 (asucc_inj g 
x3 a0 (arity_mono g x (lift1 (ptrans is i) u) (asucc g x3) H_y1 (asucc g a0) 
H_y0))))) H19) (lift1 is (TLRef i)) (lift1_lref is i)))))))))))) H13)) 
(\lambda (H13: (ex4_3 B C T (\lambda (b: B).(\lambda (c3: C).(\lambda (v2: 
T).(eq C x0 (CHead c3 (Bind b) v2))))) (\lambda (_: B).(\lambda (_: 
C).(\lambda (_: T).(eq K (Bind Abst) (Bind Void))))) (\lambda (b: B).(\lambda 
(_: C).(\lambda (_: T).(not (eq B b Void))))) (\lambda (_: B).(\lambda (c3: 
C).(\lambda (_: T).(csubc g x c3)))))).(ex4_3_ind B C T (\lambda (b: 
B).(\lambda (c3: C).(\lambda (v2: T).(eq C x0 (CHead c3 (Bind b) v2))))) 
(\lambda (_: B).(\lambda (_: C).(\lambda (_: T).(eq K (Bind Abst) (Bind 
Void))))) (\lambda (b: B).(\lambda (_: C).(\lambda (_: T).(not (eq B b 
Void))))) (\lambda (_: B).(\lambda (c3: C).(\lambda (_: T).(csubc g x c3)))) 
(sc3 g a0 c2 (lift1 is (TLRef i))) (\lambda (x1: B).(\lambda (x2: C).(\lambda 
(x3: T).(\lambda (H14: (eq C x0 (CHead x2 (Bind x1) x3))).(\lambda (H15: (eq 
K (Bind Abst) (Bind Void))).(\lambda (_: (not (eq B x1 Void))).(\lambda (_: 
(csubc g x x2)).(let H18 \def (eq_ind C x0 (\lambda (c0: C).(getl (trans is 
i) c2 c0)) H10 (CHead x2 (Bind x1) x3) H14) in (let H19 \def (eq_ind K (Bind 
Abst) (\lambda (ee: K).(match ee in K return (\lambda (_: K).Prop) with 
[(Bind b) \Rightarrow (match b in B return (\lambda (_: B).Prop) with [Abbr 
\Rightarrow False | Abst \Rightarrow True | Void \Rightarrow False]) | (Flat 
_) \Rightarrow False])) I (Bind Void) H15) in (False_ind (sc3 g a0 c2 (lift1 
is (TLRef i))) H19)))))))))) H13)) H12)))))) H9)))))) H6))))))))))))))))) 
(\lambda (b: B).(\lambda (H0: (not (eq B b Abst))).(\lambda (c: C).(\lambda 
(u: T).(\lambda (a1: A).(\lambda (_: (arity g c u a1)).(\lambda (H2: 
((\forall (d1: C).(\forall (is: PList).((drop1 is d1 c) \to (\forall (c2: 
C).((csubc g d1 c2) \to (sc3 g a1 c2 (lift1 is u))))))))).(\lambda (t0: 
T).(\lambda (a2: A).(\lambda (_: (arity g (CHead c (Bind b) u) t0 
a2)).(\lambda (H4: ((\forall (d1: C).(\forall (is: PList).((drop1 is d1 
(CHead c (Bind b) u)) \to (\forall (c2: C).((csubc g d1 c2) \to (sc3 g a2 c2 
(lift1 is t0))))))))).(\lambda (d1: C).(\lambda (is: PList).(\lambda (H5: 
(drop1 is d1 c)).(\lambda (c2: C).(\lambda (H6: (csubc g d1 c2)).(let H_y 
\def (sc3_bind g b H0 a1 a2 TNil) in (eq_ind_r T (THead (Bind b) (lift1 is u) 
(lift1 (Ss is) t0)) (\lambda (t1: T).(sc3 g a2 c2 t1)) (H_y c2 (lift1 is u) 
(lift1 (Ss is) t0) (H4 (CHead d1 (Bind b) (lift1 is u)) (Ss is) 
(drop1_skip_bind b c is d1 u H5) (CHead c2 (Bind b) (lift1 is u)) (csubc_head 
g d1 c2 H6 (Bind b) (lift1 is u))) (H2 d1 is H5 c2 H6)) (lift1 is (THead 
(Bind b) u t0)) (lift1_bind b is u t0))))))))))))))))))) (\lambda (c: 
C).(\lambda (u: T).(\lambda (a1: A).(\lambda (H0: (arity g c u (asucc g 
a1))).(\lambda (H1: ((\forall (d1: C).(\forall (is: PList).((drop1 is d1 c) 
\to (\forall (c2: C).((csubc g d1 c2) \to (sc3 g (asucc g a1) c2 (lift1 is 
u))))))))).(\lambda (t0: T).(\lambda (a2: A).(\lambda (H2: (arity g (CHead c 
(Bind Abst) u) t0 a2)).(\lambda (H3: ((\forall (d1: C).(\forall (is: 
PList).((drop1 is d1 (CHead c (Bind Abst) u)) \to (\forall (c2: C).((csubc g 
d1 c2) \to (sc3 g a2 c2 (lift1 is t0))))))))).(\lambda (d1: C).(\lambda (is: 
PList).(\lambda (H4: (drop1 is d1 c)).(\lambda (c2: C).(\lambda (H5: (csubc g 
d1 c2)).(eq_ind_r T (THead (Bind Abst) (lift1 is u) (lift1 (Ss is) t0)) 
(\lambda (t1: T).(land (arity g c2 t1 (AHead a1 a2)) (\forall (d: C).(\forall 
(w: T).((sc3 g a1 d w) \to (\forall (is0: PList).((drop1 is0 d c2) \to (sc3 g 
a2 d (THead (Flat Appl) w (lift1 is0 t1)))))))))) (conj (arity g c2 (THead 
(Bind Abst) (lift1 is u) (lift1 (Ss is) t0)) (AHead a1 a2)) (\forall (d: 
C).(\forall (w: T).((sc3 g a1 d w) \to (\forall (is0: PList).((drop1 is0 d 
c2) \to (sc3 g a2 d (THead (Flat Appl) w (lift1 is0 (THead (Bind Abst) (lift1 
is u) (lift1 (Ss is) t0)))))))))) (csubc_arity_conf g d1 c2 H5 (THead (Bind 
Abst) (lift1 is u) (lift1 (Ss is) t0)) (AHead a1 a2) (arity_head g d1 (lift1 
is u) a1 (arity_lift1 g (asucc g a1) c is d1 u H4 H0) (lift1 (Ss is) t0) a2 
(arity_lift1 g a2 (CHead c (Bind Abst) u) (Ss is) (CHead d1 (Bind Abst) 
(lift1 is u)) t0 (drop1_skip_bind Abst c is d1 u H4) H2))) (\lambda (d: 
C).(\lambda (w: T).(\lambda (H6: (sc3 g a1 d w)).(\lambda (is0: 
PList).(\lambda (H7: (drop1 is0 d c2)).(eq_ind_r T (THead (Bind Abst) (lift1 
is0 (lift1 is u)) (lift1 (Ss is0) (lift1 (Ss is) t0))) (\lambda (t1: T).(sc3 
g a2 d (THead (Flat Appl) w t1))) (let H8 \def (sc3_appl g a1 a2 TNil) in (H8 
d w (lift1 (Ss is0) (lift1 (Ss is) t0)) (let H_y \def (sc3_bind g Abbr 
(\lambda (H9: (eq B Abbr Abst)).(not_abbr_abst H9)) a1 a2 TNil) in (H_y d w 
(lift1 (Ss is0) (lift1 (Ss is) t0)) (let H_x \def (csubc_drop1_conf_rev g is0 
d c2 H7 d1 H5) in (let H9 \def H_x in (ex2_ind C (\lambda (c3: C).(drop1 is0 
c3 d1)) (\lambda (c3: C).(csubc g c3 d)) (sc3 g a2 (CHead d (Bind Abbr) w) 
(lift1 (Ss is0) (lift1 (Ss is) t0))) (\lambda (x: C).(\lambda (H10: (drop1 
is0 x d1)).(\lambda (H11: (csubc g x d)).(eq_ind_r T (lift1 (papp (Ss is0) 
(Ss is)) t0) (\lambda (t1: T).(sc3 g a2 (CHead d (Bind Abbr) w) t1)) 
(eq_ind_r PList (Ss (papp is0 is)) (\lambda (p: PList).(sc3 g a2 (CHead d 
(Bind Abbr) w) (lift1 p t0))) (H3 (CHead x (Bind Abst) (lift1 (papp is0 is) 
u)) (Ss (papp is0 is)) (drop1_skip_bind Abst c (papp is0 is) x u (drop1_trans 
is0 x d1 H10 is c H4)) (CHead d (Bind Abbr) w) (csubc_abst g x d H11 (lift1 
(papp is0 is) u) a1 (H1 x (papp is0 is) (drop1_trans is0 x d1 H10 is c H4) x 
(csubc_refl g x)) w H6)) (papp (Ss is0) (Ss is)) (papp_ss is0 is)) (lift1 (Ss 
is0) (lift1 (Ss is) t0)) (lift1_lift1 (Ss is0) (Ss is) t0))))) H9))) H6)) H6 
(lift1 is0 (lift1 is u)) (sc3_lift1 g c2 (asucc g a1) is0 d (lift1 is u) (H1 
d1 is H4 c2 H5) H7))) (lift1 is0 (THead (Bind Abst) (lift1 is u) (lift1 (Ss 
is) t0))) (lift1_bind Abst is0 (lift1 is u) (lift1 (Ss is) t0))))))))) (lift1 
is (THead (Bind Abst) u t0)) (lift1_bind Abst is u t0)))))))))))))))) 
(\lambda (c: C).(\lambda (u: T).(\lambda (a1: A).(\lambda (_: (arity g c u 
a1)).(\lambda (H1: ((\forall (d1: C).(\forall (is: PList).((drop1 is d1 c) 
\to (\forall (c2: C).((csubc g d1 c2) \to (sc3 g a1 c2 (lift1 is 
u))))))))).(\lambda (t0: T).(\lambda (a2: A).(\lambda (_: (arity g c t0 
(AHead a1 a2))).(\lambda (H3: ((\forall (d1: C).(\forall (is: PList).((drop1 
is d1 c) \to (\forall (c2: C).((csubc g d1 c2) \to (sc3 g (AHead a1 a2) c2 
(lift1 is t0))))))))).(\lambda (d1: C).(\lambda (is: PList).(\lambda (H4: 
(drop1 is d1 c)).(\lambda (c2: C).(\lambda (H5: (csubc g d1 c2)).(let H_y 
\def (H1 d1 is H4 c2 H5) in (let H_y0 \def (H3 d1 is H4 c2 H5) in (let H6 
\def H_y0 in (land_ind (arity g c2 (lift1 is t0) (AHead a1 a2)) (\forall (d: 
C).(\forall (w: T).((sc3 g a1 d w) \to (\forall (is0: PList).((drop1 is0 d 
c2) \to (sc3 g a2 d (THead (Flat Appl) w (lift1 is0 (lift1 is t0))))))))) 
(sc3 g a2 c2 (lift1 is (THead (Flat Appl) u t0))) (\lambda (_: (arity g c2 
(lift1 is t0) (AHead a1 a2))).(\lambda (H8: ((\forall (d: C).(\forall (w: 
T).((sc3 g a1 d w) \to (\forall (is0: PList).((drop1 is0 d c2) \to (sc3 g a2 
d (THead (Flat Appl) w (lift1 is0 (lift1 is t0))))))))))).(let H_y1 \def (H8 
c2 (lift1 is u) H_y PNil) in (eq_ind_r T (THead (Flat Appl) (lift1 is u) 
(lift1 is t0)) (\lambda (t1: T).(sc3 g a2 c2 t1)) (H_y1 (drop1_nil c2)) 
(lift1 is (THead (Flat Appl) u t0)) (lift1_flat Appl is u t0))))) 
H6)))))))))))))))))) (\lambda (c: C).(\lambda (u: T).(\lambda (a0: 
A).(\lambda (_: (arity g c u (asucc g a0))).(\lambda (H1: ((\forall (d1: 
C).(\forall (is: PList).((drop1 is d1 c) \to (\forall (c2: C).((csubc g d1 
c2) \to (sc3 g (asucc g a0) c2 (lift1 is u))))))))).(\lambda (t0: T).(\lambda 
(_: (arity g c t0 a0)).(\lambda (H3: ((\forall (d1: C).(\forall (is: 
PList).((drop1 is d1 c) \to (\forall (c2: C).((csubc g d1 c2) \to (sc3 g a0 
c2 (lift1 is t0))))))))).(\lambda (d1: C).(\lambda (is: PList).(\lambda (H4: 
(drop1 is d1 c)).(\lambda (c2: C).(\lambda (H5: (csubc g d1 c2)).(let H_y 
\def (sc3_cast g a0 TNil) in (eq_ind_r T (THead (Flat Cast) (lift1 is u) 
(lift1 is t0)) (\lambda (t1: T).(sc3 g a0 c2 t1)) (H_y c2 (lift1 is u) (H1 d1 
is H4 c2 H5) (lift1 is t0) (H3 d1 is H4 c2 H5)) (lift1 is (THead (Flat Cast) 
u t0)) (lift1_flat Cast is u t0)))))))))))))))) (\lambda (c: C).(\lambda (t0: 
T).(\lambda (a1: A).(\lambda (_: (arity g c t0 a1)).(\lambda (H1: ((\forall 
(d1: C).(\forall (is: PList).((drop1 is d1 c) \to (\forall (c2: C).((csubc g 
d1 c2) \to (sc3 g a1 c2 (lift1 is t0))))))))).(\lambda (a2: A).(\lambda (H2: 
(leq g a1 a2)).(\lambda (d1: C).(\lambda (is: PList).(\lambda (H3: (drop1 is 
d1 c)).(\lambda (c2: C).(\lambda (H4: (csubc g d1 c2)).(sc3_repl g a1 c2 
(lift1 is t0) (H1 d1 is H3 c2 H4) a2 H2))))))))))))) c1 t a H))))).
(* COMMENTS
Initial nodes: 5940
END *)

theorem sc3_arity:
 \forall (g: G).(\forall (c: C).(\forall (t: T).(\forall (a: A).((arity g c t 
a) \to (sc3 g a c t)))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (t: T).(\lambda (a: A).(\lambda (H: 
(arity g c t a)).(let H_y \def (sc3_arity_csubc g c t a H c PNil) in (H_y 
(drop1_nil c) c (csubc_refl g c))))))).
(* COMMENTS
Initial nodes: 47
END *)

