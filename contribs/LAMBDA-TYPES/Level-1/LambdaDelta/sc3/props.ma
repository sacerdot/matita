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

set "baseuri" "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/sc3/props".

include "sc3/defs.ma".

include "sn3/lift1.ma".

include "nf2/lift1.ma".

include "arity/lift1.ma".

include "arity/aprem.ma".

include "llt/props.ma".

include "drop1/props.ma".

theorem sc3_arity_gen:
 \forall (g: G).(\forall (c: C).(\forall (t: T).(\forall (a: A).((sc3 g a c 
t) \to (arity g c t a)))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (t: T).(\lambda (a: A).(A_ind 
(\lambda (a0: A).((sc3 g a0 c t) \to (arity g c t a0))) (\lambda (n: 
nat).(\lambda (n0: nat).(\lambda (H: (land (arity g c t (ASort n n0)) (sn3 c 
t))).(let H0 \def H in (and_ind (arity g c t (ASort n n0)) (sn3 c t) (arity g 
c t (ASort n n0)) (\lambda (H1: (arity g c t (ASort n n0))).(\lambda (_: (sn3 
c t)).H1)) H0))))) (\lambda (a0: A).(\lambda (_: (((sc3 g a0 c t) \to (arity 
g c t a0)))).(\lambda (a1: A).(\lambda (_: (((sc3 g a1 c t) \to (arity g c t 
a1)))).(\lambda (H1: (land (arity g c t (AHead a0 a1)) (\forall (d: 
C).(\forall (w: T).((sc3 g a0 d w) \to (\forall (is: PList).((drop1 is d c) 
\to (sc3 g a1 d (THead (Flat Appl) w (lift1 is t)))))))))).(let H2 \def H1 in 
(and_ind (arity g c t (AHead a0 a1)) (\forall (d: C).(\forall (w: T).((sc3 g 
a0 d w) \to (\forall (is: PList).((drop1 is d c) \to (sc3 g a1 d (THead (Flat 
Appl) w (lift1 is t)))))))) (arity g c t (AHead a0 a1)) (\lambda (H3: (arity 
g c t (AHead a0 a1))).(\lambda (_: ((\forall (d: C).(\forall (w: T).((sc3 g 
a0 d w) \to (\forall (is: PList).((drop1 is d c) \to (sc3 g a1 d (THead (Flat 
Appl) w (lift1 is t)))))))))).H3)) H2))))))) a)))).

theorem sc3_repl:
 \forall (g: G).(\forall (a1: A).(\forall (c: C).(\forall (t: T).((sc3 g a1 c 
t) \to (\forall (a2: A).((leq g a1 a2) \to (sc3 g a2 c t)))))))
\def
 \lambda (g: G).(\lambda (a1: A).(llt_wf_ind (\lambda (a: A).(\forall (c: 
C).(\forall (t: T).((sc3 g a c t) \to (\forall (a2: A).((leq g a a2) \to (sc3 
g a2 c t))))))) (\lambda (a2: A).(A_ind (\lambda (a: A).(((\forall (a3: 
A).((llt a3 a) \to (\forall (c: C).(\forall (t: T).((sc3 g a3 c t) \to 
(\forall (a4: A).((leq g a3 a4) \to (sc3 g a4 c t))))))))) \to (\forall (c: 
C).(\forall (t: T).((sc3 g a c t) \to (\forall (a3: A).((leq g a a3) \to (sc3 
g a3 c t)))))))) (\lambda (n: nat).(\lambda (n0: nat).(\lambda (_: ((\forall 
(a3: A).((llt a3 (ASort n n0)) \to (\forall (c: C).(\forall (t: T).((sc3 g a3 
c t) \to (\forall (a4: A).((leq g a3 a4) \to (sc3 g a4 c t)))))))))).(\lambda 
(c: C).(\lambda (t: T).(\lambda (H0: (land (arity g c t (ASort n n0)) (sn3 c 
t))).(\lambda (a3: A).(\lambda (H1: (leq g (ASort n n0) a3)).(let H2 \def H0 
in (and_ind (arity g c t (ASort n n0)) (sn3 c t) (sc3 g a3 c t) (\lambda (H3: 
(arity g c t (ASort n n0))).(\lambda (H4: (sn3 c t)).(let H_y \def 
(arity_repl g c t (ASort n n0) H3 a3 H1) in (let H_x \def (leq_gen_sort g n 
n0 a3 H1) in (let H5 \def H_x in (ex2_3_ind nat nat nat (\lambda (n2: 
nat).(\lambda (h2: nat).(\lambda (_: nat).(eq A a3 (ASort h2 n2))))) (\lambda 
(n2: nat).(\lambda (h2: nat).(\lambda (k: nat).(eq A (aplus g (ASort n n0) k) 
(aplus g (ASort h2 n2) k))))) (sc3 g a3 c t) (\lambda (x0: nat).(\lambda (x1: 
nat).(\lambda (x2: nat).(\lambda (H6: (eq A a3 (ASort x1 x0))).(\lambda (_: 
(eq A (aplus g (ASort n n0) x2) (aplus g (ASort x1 x0) x2))).(let H8 \def 
(eq_ind A a3 (\lambda (a: A).(arity g c t a)) H_y (ASort x1 x0) H6) in 
(eq_ind_r A (ASort x1 x0) (\lambda (a: A).(sc3 g a c t)) (conj (arity g c t 
(ASort x1 x0)) (sn3 c t) H8 H4) a3 H6))))))) H5)))))) H2)))))))))) (\lambda 
(a: A).(\lambda (_: ((((\forall (a3: A).((llt a3 a) \to (\forall (c: 
C).(\forall (t: T).((sc3 g a3 c t) \to (\forall (a4: A).((leq g a3 a4) \to 
(sc3 g a4 c t))))))))) \to (\forall (c: C).(\forall (t: T).((sc3 g a c t) \to 
(\forall (a3: A).((leq g a a3) \to (sc3 g a3 c t))))))))).(\lambda (a0: 
A).(\lambda (H0: ((((\forall (a3: A).((llt a3 a0) \to (\forall (c: 
C).(\forall (t: T).((sc3 g a3 c t) \to (\forall (a4: A).((leq g a3 a4) \to 
(sc3 g a4 c t))))))))) \to (\forall (c: C).(\forall (t: T).((sc3 g a0 c t) 
\to (\forall (a3: A).((leq g a0 a3) \to (sc3 g a3 c t))))))))).(\lambda (H1: 
((\forall (a3: A).((llt a3 (AHead a a0)) \to (\forall (c: C).(\forall (t: 
T).((sc3 g a3 c t) \to (\forall (a4: A).((leq g a3 a4) \to (sc3 g a4 c 
t)))))))))).(\lambda (c: C).(\lambda (t: T).(\lambda (H2: (land (arity g c t 
(AHead a a0)) (\forall (d: C).(\forall (w: T).((sc3 g a d w) \to (\forall 
(is: PList).((drop1 is d c) \to (sc3 g a0 d (THead (Flat Appl) w (lift1 is 
t)))))))))).(\lambda (a3: A).(\lambda (H3: (leq g (AHead a a0) a3)).(let H4 
\def H2 in (and_ind (arity g c t (AHead a a0)) (\forall (d: C).(\forall (w: 
T).((sc3 g a d w) \to (\forall (is: PList).((drop1 is d c) \to (sc3 g a0 d 
(THead (Flat Appl) w (lift1 is t)))))))) (sc3 g a3 c t) (\lambda (H5: (arity 
g c t (AHead a a0))).(\lambda (H6: ((\forall (d: C).(\forall (w: T).((sc3 g a 
d w) \to (\forall (is: PList).((drop1 is d c) \to (sc3 g a0 d (THead (Flat 
Appl) w (lift1 is t)))))))))).(let H_x \def (leq_gen_head g a a0 a3 H3) in 
(let H7 \def H_x in (ex3_2_ind A A (\lambda (a4: A).(\lambda (a5: A).(eq A a3 
(AHead a4 a5)))) (\lambda (a4: A).(\lambda (_: A).(leq g a a4))) (\lambda (_: 
A).(\lambda (a5: A).(leq g a0 a5))) (sc3 g a3 c t) (\lambda (x0: A).(\lambda 
(x1: A).(\lambda (H8: (eq A a3 (AHead x0 x1))).(\lambda (H9: (leq g a 
x0)).(\lambda (H10: (leq g a0 x1)).(eq_ind_r A (AHead x0 x1) (\lambda (a4: 
A).(sc3 g a4 c t)) (conj (arity g c t (AHead x0 x1)) (\forall (d: C).(\forall 
(w: T).((sc3 g x0 d w) \to (\forall (is: PList).((drop1 is d c) \to (sc3 g x1 
d (THead (Flat Appl) w (lift1 is t)))))))) (arity_repl g c t (AHead a a0) H5 
(AHead x0 x1) (leq_head g a x0 H9 a0 x1 H10)) (\lambda (d: C).(\lambda (w: 
T).(\lambda (H11: (sc3 g x0 d w)).(\lambda (is: PList).(\lambda (H12: (drop1 
is d c)).(H0 (\lambda (a4: A).(\lambda (H13: (llt a4 a0)).(\lambda (c0: 
C).(\lambda (t0: T).(\lambda (H14: (sc3 g a4 c0 t0)).(\lambda (a5: 
A).(\lambda (H15: (leq g a4 a5)).(H1 a4 (llt_trans a4 a0 (AHead a a0) H13 
(llt_head_dx a a0)) c0 t0 H14 a5 H15)))))))) d (THead (Flat Appl) w (lift1 is 
t)) (H6 d w (H1 x0 (llt_repl g a x0 H9 (AHead a a0) (llt_head_sx a a0)) d w 
H11 a (leq_sym g a x0 H9)) is H12) x1 H10))))))) a3 H8)))))) H7))))) 
H4)))))))))))) a2)) a1)).

theorem sc3_lift:
 \forall (g: G).(\forall (a: A).(\forall (e: C).(\forall (t: T).((sc3 g a e 
t) \to (\forall (c: C).(\forall (h: nat).(\forall (d: nat).((drop h d c e) 
\to (sc3 g a c (lift h d t))))))))))
\def
 \lambda (g: G).(\lambda (a: A).(A_ind (\lambda (a0: A).(\forall (e: 
C).(\forall (t: T).((sc3 g a0 e t) \to (\forall (c: C).(\forall (h: 
nat).(\forall (d: nat).((drop h d c e) \to (sc3 g a0 c (lift h d t)))))))))) 
(\lambda (n: nat).(\lambda (n0: nat).(\lambda (e: C).(\lambda (t: T).(\lambda 
(H: (land (arity g e t (ASort n n0)) (sn3 e t))).(\lambda (c: C).(\lambda (h: 
nat).(\lambda (d: nat).(\lambda (H0: (drop h d c e)).(let H1 \def H in 
(and_ind (arity g e t (ASort n n0)) (sn3 e t) (land (arity g c (lift h d t) 
(ASort n n0)) (sn3 c (lift h d t))) (\lambda (H2: (arity g e t (ASort n 
n0))).(\lambda (H3: (sn3 e t)).(conj (arity g c (lift h d t) (ASort n n0)) 
(sn3 c (lift h d t)) (arity_lift g e t (ASort n n0) H2 c h d H0) (sn3_lift e 
t H3 c h d H0)))) H1))))))))))) (\lambda (a0: A).(\lambda (_: ((\forall (e: 
C).(\forall (t: T).((sc3 g a0 e t) \to (\forall (c: C).(\forall (h: 
nat).(\forall (d: nat).((drop h d c e) \to (sc3 g a0 c (lift h d 
t))))))))))).(\lambda (a1: A).(\lambda (_: ((\forall (e: C).(\forall (t: 
T).((sc3 g a1 e t) \to (\forall (c: C).(\forall (h: nat).(\forall (d: 
nat).((drop h d c e) \to (sc3 g a1 c (lift h d t))))))))))).(\lambda (e: 
C).(\lambda (t: T).(\lambda (H1: (land (arity g e t (AHead a0 a1)) (\forall 
(d: C).(\forall (w: T).((sc3 g a0 d w) \to (\forall (is: PList).((drop1 is d 
e) \to (sc3 g a1 d (THead (Flat Appl) w (lift1 is t)))))))))).(\lambda (c: 
C).(\lambda (h: nat).(\lambda (d: nat).(\lambda (H2: (drop h d c e)).(let H3 
\def H1 in (and_ind (arity g e t (AHead a0 a1)) (\forall (d0: C).(\forall (w: 
T).((sc3 g a0 d0 w) \to (\forall (is: PList).((drop1 is d0 e) \to (sc3 g a1 
d0 (THead (Flat Appl) w (lift1 is t)))))))) (land (arity g c (lift h d t) 
(AHead a0 a1)) (\forall (d0: C).(\forall (w: T).((sc3 g a0 d0 w) \to (\forall 
(is: PList).((drop1 is d0 c) \to (sc3 g a1 d0 (THead (Flat Appl) w (lift1 is 
(lift h d t)))))))))) (\lambda (H4: (arity g e t (AHead a0 a1))).(\lambda 
(H5: ((\forall (d0: C).(\forall (w: T).((sc3 g a0 d0 w) \to (\forall (is: 
PList).((drop1 is d0 e) \to (sc3 g a1 d0 (THead (Flat Appl) w (lift1 is 
t)))))))))).(conj (arity g c (lift h d t) (AHead a0 a1)) (\forall (d0: 
C).(\forall (w: T).((sc3 g a0 d0 w) \to (\forall (is: PList).((drop1 is d0 c) 
\to (sc3 g a1 d0 (THead (Flat Appl) w (lift1 is (lift h d t))))))))) 
(arity_lift g e t (AHead a0 a1) H4 c h d H2) (\lambda (d0: C).(\lambda (w: 
T).(\lambda (H6: (sc3 g a0 d0 w)).(\lambda (is: PList).(\lambda (H7: (drop1 
is d0 c)).(let H_y \def (H5 d0 w H6 (PConsTail is h d)) in (eq_ind T (lift1 
(PConsTail is h d) t) (\lambda (t0: T).(sc3 g a1 d0 (THead (Flat Appl) w 
t0))) (H_y (drop1_cons_tail c e h d H2 is d0 H7)) (lift1 is (lift h d t)) 
(lift1_cons_tail t h d is))))))))))) H3))))))))))))) a)).

theorem sc3_lift1:
 \forall (g: G).(\forall (e: C).(\forall (a: A).(\forall (hds: 
PList).(\forall (c: C).(\forall (t: T).((sc3 g a e t) \to ((drop1 hds c e) 
\to (sc3 g a c (lift1 hds t)))))))))
\def
 \lambda (g: G).(\lambda (e: C).(\lambda (a: A).(\lambda (hds: 
PList).(PList_ind (\lambda (p: PList).(\forall (c: C).(\forall (t: T).((sc3 g 
a e t) \to ((drop1 p c e) \to (sc3 g a c (lift1 p t))))))) (\lambda (c: 
C).(\lambda (t: T).(\lambda (H: (sc3 g a e t)).(\lambda (H0: (drop1 PNil c 
e)).(let H1 \def (match H0 in drop1 return (\lambda (p: PList).(\lambda (c0: 
C).(\lambda (c1: C).(\lambda (_: (drop1 p c0 c1)).((eq PList p PNil) \to ((eq 
C c0 c) \to ((eq C c1 e) \to (sc3 g a c t)))))))) with [(drop1_nil c0) 
\Rightarrow (\lambda (_: (eq PList PNil PNil)).(\lambda (H2: (eq C c0 
c)).(\lambda (H3: (eq C c0 e)).(eq_ind C c (\lambda (c1: C).((eq C c1 e) \to 
(sc3 g a c t))) (\lambda (H4: (eq C c e)).(eq_ind C e (\lambda (c1: C).(sc3 g 
a c1 t)) H c (sym_eq C c e H4))) c0 (sym_eq C c0 c H2) H3)))) | (drop1_cons 
c1 c2 h d H1 c3 hds0 H2) \Rightarrow (\lambda (H3: (eq PList (PCons h d hds0) 
PNil)).(\lambda (H4: (eq C c1 c)).(\lambda (H5: (eq C c3 e)).((let H6 \def 
(eq_ind PList (PCons h d hds0) (\lambda (e0: PList).(match e0 in PList return 
(\lambda (_: PList).Prop) with [PNil \Rightarrow False | (PCons _ _ _) 
\Rightarrow True])) I PNil H3) in (False_ind ((eq C c1 c) \to ((eq C c3 e) 
\to ((drop h d c1 c2) \to ((drop1 hds0 c2 c3) \to (sc3 g a c t))))) H6)) H4 
H5 H1 H2))))]) in (H1 (refl_equal PList PNil) (refl_equal C c) (refl_equal C 
e))))))) (\lambda (n: nat).(\lambda (n0: nat).(\lambda (p: PList).(\lambda 
(H: ((\forall (c: C).(\forall (t: T).((sc3 g a e t) \to ((drop1 p c e) \to 
(sc3 g a c (lift1 p t)))))))).(\lambda (c: C).(\lambda (t: T).(\lambda (H0: 
(sc3 g a e t)).(\lambda (H1: (drop1 (PCons n n0 p) c e)).(let H2 \def (match 
H1 in drop1 return (\lambda (p0: PList).(\lambda (c0: C).(\lambda (c1: 
C).(\lambda (_: (drop1 p0 c0 c1)).((eq PList p0 (PCons n n0 p)) \to ((eq C c0 
c) \to ((eq C c1 e) \to (sc3 g a c (lift n n0 (lift1 p t)))))))))) with 
[(drop1_nil c0) \Rightarrow (\lambda (H2: (eq PList PNil (PCons n n0 
p))).(\lambda (H3: (eq C c0 c)).(\lambda (H4: (eq C c0 e)).((let H5 \def 
(eq_ind PList PNil (\lambda (e0: PList).(match e0 in PList return (\lambda 
(_: PList).Prop) with [PNil \Rightarrow True | (PCons _ _ _) \Rightarrow 
False])) I (PCons n n0 p) H2) in (False_ind ((eq C c0 c) \to ((eq C c0 e) \to 
(sc3 g a c (lift n n0 (lift1 p t))))) H5)) H3 H4)))) | (drop1_cons c1 c2 h d 
H2 c3 hds0 H3) \Rightarrow (\lambda (H4: (eq PList (PCons h d hds0) (PCons n 
n0 p))).(\lambda (H5: (eq C c1 c)).(\lambda (H6: (eq C c3 e)).((let H7 \def 
(f_equal PList PList (\lambda (e0: PList).(match e0 in PList return (\lambda 
(_: PList).PList) with [PNil \Rightarrow hds0 | (PCons _ _ p0) \Rightarrow 
p0])) (PCons h d hds0) (PCons n n0 p) H4) in ((let H8 \def (f_equal PList nat 
(\lambda (e0: PList).(match e0 in PList return (\lambda (_: PList).nat) with 
[PNil \Rightarrow d | (PCons _ n1 _) \Rightarrow n1])) (PCons h d hds0) 
(PCons n n0 p) H4) in ((let H9 \def (f_equal PList nat (\lambda (e0: 
PList).(match e0 in PList return (\lambda (_: PList).nat) with [PNil 
\Rightarrow h | (PCons n1 _ _) \Rightarrow n1])) (PCons h d hds0) (PCons n n0 
p) H4) in (eq_ind nat n (\lambda (n1: nat).((eq nat d n0) \to ((eq PList hds0 
p) \to ((eq C c1 c) \to ((eq C c3 e) \to ((drop n1 d c1 c2) \to ((drop1 hds0 
c2 c3) \to (sc3 g a c (lift n n0 (lift1 p t)))))))))) (\lambda (H10: (eq nat 
d n0)).(eq_ind nat n0 (\lambda (n1: nat).((eq PList hds0 p) \to ((eq C c1 c) 
\to ((eq C c3 e) \to ((drop n n1 c1 c2) \to ((drop1 hds0 c2 c3) \to (sc3 g a 
c (lift n n0 (lift1 p t))))))))) (\lambda (H11: (eq PList hds0 p)).(eq_ind 
PList p (\lambda (p0: PList).((eq C c1 c) \to ((eq C c3 e) \to ((drop n n0 c1 
c2) \to ((drop1 p0 c2 c3) \to (sc3 g a c (lift n n0 (lift1 p t)))))))) 
(\lambda (H12: (eq C c1 c)).(eq_ind C c (\lambda (c0: C).((eq C c3 e) \to 
((drop n n0 c0 c2) \to ((drop1 p c2 c3) \to (sc3 g a c (lift n n0 (lift1 p 
t))))))) (\lambda (H13: (eq C c3 e)).(eq_ind C e (\lambda (c0: C).((drop n n0 
c c2) \to ((drop1 p c2 c0) \to (sc3 g a c (lift n n0 (lift1 p t)))))) 
(\lambda (H14: (drop n n0 c c2)).(\lambda (H15: (drop1 p c2 e)).(sc3_lift g a 
c2 (lift1 p t) (H c2 t H0 H15) c n n0 H14))) c3 (sym_eq C c3 e H13))) c1 
(sym_eq C c1 c H12))) hds0 (sym_eq PList hds0 p H11))) d (sym_eq nat d n0 
H10))) h (sym_eq nat h n H9))) H8)) H7)) H5 H6 H2 H3))))]) in (H2 (refl_equal 
PList (PCons n n0 p)) (refl_equal C c) (refl_equal C e))))))))))) hds)))).

axiom sc3_abbr:
 \forall (g: G).(\forall (a: A).(\forall (vs: TList).(\forall (i: 
nat).(\forall (d: C).(\forall (v: T).(\forall (c: C).((sc3 g a c (THeads 
(Flat Appl) vs (lift (S i) O v))) \to ((getl i c (CHead d (Bind Abbr) v)) \to 
(sc3 g a c (THeads (Flat Appl) vs (TLRef i)))))))))))
.

theorem sc3_cast:
 \forall (g: G).(\forall (a: A).(\forall (vs: TList).(\forall (c: C).(\forall 
(u: T).((sc3 g (asucc g a) c (THeads (Flat Appl) vs u)) \to (\forall (t: 
T).((sc3 g a c (THeads (Flat Appl) vs t)) \to (sc3 g a c (THeads (Flat Appl) 
vs (THead (Flat Cast) u t))))))))))
\def
 \lambda (g: G).(\lambda (a: A).(A_ind (\lambda (a0: A).(\forall (vs: 
TList).(\forall (c: C).(\forall (u: T).((sc3 g (asucc g a0) c (THeads (Flat 
Appl) vs u)) \to (\forall (t: T).((sc3 g a0 c (THeads (Flat Appl) vs t)) \to 
(sc3 g a0 c (THeads (Flat Appl) vs (THead (Flat Cast) u t)))))))))) (\lambda 
(n: nat).(\lambda (n0: nat).(\lambda (vs: TList).(\lambda (c: C).(\lambda (u: 
T).(\lambda (H: (sc3 g (match n with [O \Rightarrow (ASort O (next g n0)) | 
(S h) \Rightarrow (ASort h n0)]) c (THeads (Flat Appl) vs u))).(\lambda (t: 
T).(\lambda (H0: (land (arity g c (THeads (Flat Appl) vs t) (ASort n n0)) 
(sn3 c (THeads (Flat Appl) vs t)))).(nat_ind (\lambda (n1: nat).((sc3 g 
(match n1 with [O \Rightarrow (ASort O (next g n0)) | (S h) \Rightarrow 
(ASort h n0)]) c (THeads (Flat Appl) vs u)) \to ((land (arity g c (THeads 
(Flat Appl) vs t) (ASort n1 n0)) (sn3 c (THeads (Flat Appl) vs t))) \to (land 
(arity g c (THeads (Flat Appl) vs (THead (Flat Cast) u t)) (ASort n1 n0)) 
(sn3 c (THeads (Flat Appl) vs (THead (Flat Cast) u t))))))) (\lambda (H1: 
(sc3 g (ASort O (next g n0)) c (THeads (Flat Appl) vs u))).(\lambda (H2: 
(land (arity g c (THeads (Flat Appl) vs t) (ASort O n0)) (sn3 c (THeads (Flat 
Appl) vs t)))).(let H3 \def H1 in (and_ind (arity g c (THeads (Flat Appl) vs 
u) (ASort O (next g n0))) (sn3 c (THeads (Flat Appl) vs u)) (land (arity g c 
(THeads (Flat Appl) vs (THead (Flat Cast) u t)) (ASort O n0)) (sn3 c (THeads 
(Flat Appl) vs (THead (Flat Cast) u t)))) (\lambda (H4: (arity g c (THeads 
(Flat Appl) vs u) (ASort O (next g n0)))).(\lambda (H5: (sn3 c (THeads (Flat 
Appl) vs u))).(let H6 \def H2 in (and_ind (arity g c (THeads (Flat Appl) vs 
t) (ASort O n0)) (sn3 c (THeads (Flat Appl) vs t)) (land (arity g c (THeads 
(Flat Appl) vs (THead (Flat Cast) u t)) (ASort O n0)) (sn3 c (THeads (Flat 
Appl) vs (THead (Flat Cast) u t)))) (\lambda (H7: (arity g c (THeads (Flat 
Appl) vs t) (ASort O n0))).(\lambda (H8: (sn3 c (THeads (Flat Appl) vs 
t))).(conj (arity g c (THeads (Flat Appl) vs (THead (Flat Cast) u t)) (ASort 
O n0)) (sn3 c (THeads (Flat Appl) vs (THead (Flat Cast) u t))) 
(arity_appls_cast g c u t vs (ASort O n0) H4 H7) (sn3_appls_cast c vs u H5 t 
H8)))) H6)))) H3)))) (\lambda (n1: nat).(\lambda (_: (((sc3 g (match n1 with 
[O \Rightarrow (ASort O (next g n0)) | (S h) \Rightarrow (ASort h n0)]) c 
(THeads (Flat Appl) vs u)) \to ((land (arity g c (THeads (Flat Appl) vs t) 
(ASort n1 n0)) (sn3 c (THeads (Flat Appl) vs t))) \to (land (arity g c 
(THeads (Flat Appl) vs (THead (Flat Cast) u t)) (ASort n1 n0)) (sn3 c (THeads 
(Flat Appl) vs (THead (Flat Cast) u t)))))))).(\lambda (H1: (sc3 g (ASort n1 
n0) c (THeads (Flat Appl) vs u))).(\lambda (H2: (land (arity g c (THeads 
(Flat Appl) vs t) (ASort (S n1) n0)) (sn3 c (THeads (Flat Appl) vs t)))).(let 
H3 \def H1 in (and_ind (arity g c (THeads (Flat Appl) vs u) (ASort n1 n0)) 
(sn3 c (THeads (Flat Appl) vs u)) (land (arity g c (THeads (Flat Appl) vs 
(THead (Flat Cast) u t)) (ASort (S n1) n0)) (sn3 c (THeads (Flat Appl) vs 
(THead (Flat Cast) u t)))) (\lambda (H4: (arity g c (THeads (Flat Appl) vs u) 
(ASort n1 n0))).(\lambda (H5: (sn3 c (THeads (Flat Appl) vs u))).(let H6 \def 
H2 in (and_ind (arity g c (THeads (Flat Appl) vs t) (ASort (S n1) n0)) (sn3 c 
(THeads (Flat Appl) vs t)) (land (arity g c (THeads (Flat Appl) vs (THead 
(Flat Cast) u t)) (ASort (S n1) n0)) (sn3 c (THeads (Flat Appl) vs (THead 
(Flat Cast) u t)))) (\lambda (H7: (arity g c (THeads (Flat Appl) vs t) (ASort 
(S n1) n0))).(\lambda (H8: (sn3 c (THeads (Flat Appl) vs t))).(conj (arity g 
c (THeads (Flat Appl) vs (THead (Flat Cast) u t)) (ASort (S n1) n0)) (sn3 c 
(THeads (Flat Appl) vs (THead (Flat Cast) u t))) (arity_appls_cast g c u t vs 
(ASort (S n1) n0) H4 H7) (sn3_appls_cast c vs u H5 t H8)))) H6)))) H3)))))) n 
H H0))))))))) (\lambda (a0: A).(\lambda (_: ((\forall (vs: TList).(\forall 
(c: C).(\forall (u: T).((sc3 g (asucc g a0) c (THeads (Flat Appl) vs u)) \to 
(\forall (t: T).((sc3 g a0 c (THeads (Flat Appl) vs t)) \to (sc3 g a0 c 
(THeads (Flat Appl) vs (THead (Flat Cast) u t))))))))))).(\lambda (a1: 
A).(\lambda (H0: ((\forall (vs: TList).(\forall (c: C).(\forall (u: T).((sc3 
g (asucc g a1) c (THeads (Flat Appl) vs u)) \to (\forall (t: T).((sc3 g a1 c 
(THeads (Flat Appl) vs t)) \to (sc3 g a1 c (THeads (Flat Appl) vs (THead 
(Flat Cast) u t))))))))))).(\lambda (vs: TList).(\lambda (c: C).(\lambda (u: 
T).(\lambda (H1: (land (arity g c (THeads (Flat Appl) vs u) (AHead a0 (asucc 
g a1))) (\forall (d: C).(\forall (w: T).((sc3 g a0 d w) \to (\forall (is: 
PList).((drop1 is d c) \to (sc3 g (asucc g a1) d (THead (Flat Appl) w (lift1 
is (THeads (Flat Appl) vs u))))))))))).(\lambda (t: T).(\lambda (H2: (land 
(arity g c (THeads (Flat Appl) vs t) (AHead a0 a1)) (\forall (d: C).(\forall 
(w: T).((sc3 g a0 d w) \to (\forall (is: PList).((drop1 is d c) \to (sc3 g a1 
d (THead (Flat Appl) w (lift1 is (THeads (Flat Appl) vs t))))))))))).(let H3 
\def H1 in (and_ind (arity g c (THeads (Flat Appl) vs u) (AHead a0 (asucc g 
a1))) (\forall (d: C).(\forall (w: T).((sc3 g a0 d w) \to (\forall (is: 
PList).((drop1 is d c) \to (sc3 g (asucc g a1) d (THead (Flat Appl) w (lift1 
is (THeads (Flat Appl) vs u))))))))) (land (arity g c (THeads (Flat Appl) vs 
(THead (Flat Cast) u t)) (AHead a0 a1)) (\forall (d: C).(\forall (w: T).((sc3 
g a0 d w) \to (\forall (is: PList).((drop1 is d c) \to (sc3 g a1 d (THead 
(Flat Appl) w (lift1 is (THeads (Flat Appl) vs (THead (Flat Cast) u 
t))))))))))) (\lambda (H4: (arity g c (THeads (Flat Appl) vs u) (AHead a0 
(asucc g a1)))).(\lambda (H5: ((\forall (d: C).(\forall (w: T).((sc3 g a0 d 
w) \to (\forall (is: PList).((drop1 is d c) \to (sc3 g (asucc g a1) d (THead 
(Flat Appl) w (lift1 is (THeads (Flat Appl) vs u))))))))))).(let H6 \def H2 
in (and_ind (arity g c (THeads (Flat Appl) vs t) (AHead a0 a1)) (\forall (d: 
C).(\forall (w: T).((sc3 g a0 d w) \to (\forall (is: PList).((drop1 is d c) 
\to (sc3 g a1 d (THead (Flat Appl) w (lift1 is (THeads (Flat Appl) vs 
t))))))))) (land (arity g c (THeads (Flat Appl) vs (THead (Flat Cast) u t)) 
(AHead a0 a1)) (\forall (d: C).(\forall (w: T).((sc3 g a0 d w) \to (\forall 
(is: PList).((drop1 is d c) \to (sc3 g a1 d (THead (Flat Appl) w (lift1 is 
(THeads (Flat Appl) vs (THead (Flat Cast) u t))))))))))) (\lambda (H7: (arity 
g c (THeads (Flat Appl) vs t) (AHead a0 a1))).(\lambda (H8: ((\forall (d: 
C).(\forall (w: T).((sc3 g a0 d w) \to (\forall (is: PList).((drop1 is d c) 
\to (sc3 g a1 d (THead (Flat Appl) w (lift1 is (THeads (Flat Appl) vs 
t))))))))))).(conj (arity g c (THeads (Flat Appl) vs (THead (Flat Cast) u t)) 
(AHead a0 a1)) (\forall (d: C).(\forall (w: T).((sc3 g a0 d w) \to (\forall 
(is: PList).((drop1 is d c) \to (sc3 g a1 d (THead (Flat Appl) w (lift1 is 
(THeads (Flat Appl) vs (THead (Flat Cast) u t)))))))))) (arity_appls_cast g c 
u t vs (AHead a0 a1) H4 H7) (\lambda (d: C).(\lambda (w: T).(\lambda (H9: 
(sc3 g a0 d w)).(\lambda (is: PList).(\lambda (H10: (drop1 is d c)).(let H_y 
\def (H0 (TCons w (lifts1 is vs))) in (eq_ind_r T (THeads (Flat Appl) (lifts1 
is vs) (lift1 is (THead (Flat Cast) u t))) (\lambda (t0: T).(sc3 g a1 d 
(THead (Flat Appl) w t0))) (eq_ind_r T (THead (Flat Cast) (lift1 is u) (lift1 
is t)) (\lambda (t0: T).(sc3 g a1 d (THead (Flat Appl) w (THeads (Flat Appl) 
(lifts1 is vs) t0)))) (H_y d (lift1 is u) (eq_ind T (lift1 is (THeads (Flat 
Appl) vs u)) (\lambda (t0: T).(sc3 g (asucc g a1) d (THead (Flat Appl) w 
t0))) (H5 d w H9 is H10) (THeads (Flat Appl) (lifts1 is vs) (lift1 is u)) 
(lifts1_flat Appl is u vs)) (lift1 is t) (eq_ind T (lift1 is (THeads (Flat 
Appl) vs t)) (\lambda (t0: T).(sc3 g a1 d (THead (Flat Appl) w t0))) (H8 d w 
H9 is H10) (THeads (Flat Appl) (lifts1 is vs) (lift1 is t)) (lifts1_flat Appl 
is t vs))) (lift1 is (THead (Flat Cast) u t)) (lift1_flat Cast is u t)) 
(lift1 is (THeads (Flat Appl) vs (THead (Flat Cast) u t))) (lifts1_flat Appl 
is (THead (Flat Cast) u t) vs))))))))))) H6)))) H3)))))))))))) a)).

theorem sc3_props__sc3_sn3_abst:
 \forall (g: G).(\forall (a: A).(land (\forall (c: C).(\forall (t: T).((sc3 g 
a c t) \to (sn3 c t)))) (\forall (vs: TList).(\forall (i: nat).(let t \def 
(THeads (Flat Appl) vs (TLRef i)) in (\forall (c: C).((arity g c t a) \to 
((nf2 c (TLRef i)) \to ((sns3 c vs) \to (sc3 g a c t))))))))))
\def
 \lambda (g: G).(\lambda (a: A).(A_ind (\lambda (a0: A).(land (\forall (c: 
C).(\forall (t: T).((sc3 g a0 c t) \to (sn3 c t)))) (\forall (vs: 
TList).(\forall (i: nat).(let t \def (THeads (Flat Appl) vs (TLRef i)) in 
(\forall (c: C).((arity g c t a0) \to ((nf2 c (TLRef i)) \to ((sns3 c vs) \to 
(sc3 g a0 c t)))))))))) (\lambda (n: nat).(\lambda (n0: nat).(conj (\forall 
(c: C).(\forall (t: T).((land (arity g c t (ASort n n0)) (sn3 c t)) \to (sn3 
c t)))) (\forall (vs: TList).(\forall (i: nat).(\forall (c: C).((arity g c 
(THeads (Flat Appl) vs (TLRef i)) (ASort n n0)) \to ((nf2 c (TLRef i)) \to 
((sns3 c vs) \to (land (arity g c (THeads (Flat Appl) vs (TLRef i)) (ASort n 
n0)) (sn3 c (THeads (Flat Appl) vs (TLRef i)))))))))) (\lambda (c: 
C).(\lambda (t: T).(\lambda (H: (land (arity g c t (ASort n n0)) (sn3 c 
t))).(let H0 \def H in (and_ind (arity g c t (ASort n n0)) (sn3 c t) (sn3 c 
t) (\lambda (_: (arity g c t (ASort n n0))).(\lambda (H2: (sn3 c t)).H2)) 
H0))))) (\lambda (vs: TList).(\lambda (i: nat).(\lambda (c: C).(\lambda (H: 
(arity g c (THeads (Flat Appl) vs (TLRef i)) (ASort n n0))).(\lambda (H0: 
(nf2 c (TLRef i))).(\lambda (H1: (sns3 c vs)).(conj (arity g c (THeads (Flat 
Appl) vs (TLRef i)) (ASort n n0)) (sn3 c (THeads (Flat Appl) vs (TLRef i))) H 
(sn3_appls_lref c i H0 vs H1))))))))))) (\lambda (a0: A).(\lambda (H: (land 
(\forall (c: C).(\forall (t: T).((sc3 g a0 c t) \to (sn3 c t)))) (\forall 
(vs: TList).(\forall (i: nat).(\forall (c: C).((arity g c (THeads (Flat Appl) 
vs (TLRef i)) a0) \to ((nf2 c (TLRef i)) \to ((sns3 c vs) \to (sc3 g a0 c 
(THeads (Flat Appl) vs (TLRef i))))))))))).(\lambda (a1: A).(\lambda (H0: 
(land (\forall (c: C).(\forall (t: T).((sc3 g a1 c t) \to (sn3 c t)))) 
(\forall (vs: TList).(\forall (i: nat).(\forall (c: C).((arity g c (THeads 
(Flat Appl) vs (TLRef i)) a1) \to ((nf2 c (TLRef i)) \to ((sns3 c vs) \to 
(sc3 g a1 c (THeads (Flat Appl) vs (TLRef i))))))))))).(conj (\forall (c: 
C).(\forall (t: T).((land (arity g c t (AHead a0 a1)) (\forall (d: 
C).(\forall (w: T).((sc3 g a0 d w) \to (\forall (is: PList).((drop1 is d c) 
\to (sc3 g a1 d (THead (Flat Appl) w (lift1 is t))))))))) \to (sn3 c t)))) 
(\forall (vs: TList).(\forall (i: nat).(\forall (c: C).((arity g c (THeads 
(Flat Appl) vs (TLRef i)) (AHead a0 a1)) \to ((nf2 c (TLRef i)) \to ((sns3 c 
vs) \to (land (arity g c (THeads (Flat Appl) vs (TLRef i)) (AHead a0 a1)) 
(\forall (d: C).(\forall (w: T).((sc3 g a0 d w) \to (\forall (is: 
PList).((drop1 is d c) \to (sc3 g a1 d (THead (Flat Appl) w (lift1 is (THeads 
(Flat Appl) vs (TLRef i))))))))))))))))) (\lambda (c: C).(\lambda (t: 
T).(\lambda (H1: (land (arity g c t (AHead a0 a1)) (\forall (d: C).(\forall 
(w: T).((sc3 g a0 d w) \to (\forall (is: PList).((drop1 is d c) \to (sc3 g a1 
d (THead (Flat Appl) w (lift1 is t)))))))))).(let H2 \def H in (and_ind 
(\forall (c0: C).(\forall (t0: T).((sc3 g a0 c0 t0) \to (sn3 c0 t0)))) 
(\forall (vs: TList).(\forall (i: nat).(\forall (c0: C).((arity g c0 (THeads 
(Flat Appl) vs (TLRef i)) a0) \to ((nf2 c0 (TLRef i)) \to ((sns3 c0 vs) \to 
(sc3 g a0 c0 (THeads (Flat Appl) vs (TLRef i))))))))) (sn3 c t) (\lambda (_: 
((\forall (c0: C).(\forall (t0: T).((sc3 g a0 c0 t0) \to (sn3 c0 
t0)))))).(\lambda (H4: ((\forall (vs: TList).(\forall (i: nat).(\forall (c0: 
C).((arity g c0 (THeads (Flat Appl) vs (TLRef i)) a0) \to ((nf2 c0 (TLRef i)) 
\to ((sns3 c0 vs) \to (sc3 g a0 c0 (THeads (Flat Appl) vs (TLRef 
i))))))))))).(let H5 \def H0 in (and_ind (\forall (c0: C).(\forall (t0: 
T).((sc3 g a1 c0 t0) \to (sn3 c0 t0)))) (\forall (vs: TList).(\forall (i: 
nat).(\forall (c0: C).((arity g c0 (THeads (Flat Appl) vs (TLRef i)) a1) \to 
((nf2 c0 (TLRef i)) \to ((sns3 c0 vs) \to (sc3 g a1 c0 (THeads (Flat Appl) vs 
(TLRef i))))))))) (sn3 c t) (\lambda (H6: ((\forall (c0: C).(\forall (t0: 
T).((sc3 g a1 c0 t0) \to (sn3 c0 t0)))))).(\lambda (_: ((\forall (vs: 
TList).(\forall (i: nat).(\forall (c0: C).((arity g c0 (THeads (Flat Appl) vs 
(TLRef i)) a1) \to ((nf2 c0 (TLRef i)) \to ((sns3 c0 vs) \to (sc3 g a1 c0 
(THeads (Flat Appl) vs (TLRef i))))))))))).(let H8 \def H1 in (and_ind (arity 
g c t (AHead a0 a1)) (\forall (d: C).(\forall (w: T).((sc3 g a0 d w) \to 
(\forall (is: PList).((drop1 is d c) \to (sc3 g a1 d (THead (Flat Appl) w 
(lift1 is t)))))))) (sn3 c t) (\lambda (H9: (arity g c t (AHead a0 
a1))).(\lambda (H10: ((\forall (d: C).(\forall (w: T).((sc3 g a0 d w) \to 
(\forall (is: PList).((drop1 is d c) \to (sc3 g a1 d (THead (Flat Appl) w 
(lift1 is t)))))))))).(let H_y \def (arity_aprem g c t (AHead a0 a1) H9 O a0) 
in (let H11 \def (H_y (aprem_zero a0 a1)) in (ex2_3_ind C T nat (\lambda (d: 
C).(\lambda (_: T).(\lambda (j: nat).(drop j O d c)))) (\lambda (d: 
C).(\lambda (u: T).(\lambda (_: nat).(arity g d u (asucc g a0))))) (sn3 c t) 
(\lambda (x0: C).(\lambda (x1: T).(\lambda (x2: nat).(\lambda (H12: (drop x2 
O x0 c)).(\lambda (H13: (arity g x0 x1 (asucc g a0))).(let H_y0 \def (H10 
(CHead x0 (Bind Abst) x1) (TLRef O) (H4 TNil O (CHead x0 (Bind Abst) x1) 
(arity_abst g (CHead x0 (Bind Abst) x1) x0 x1 O (getl_refl Abst x0 x1) a0 
H13) (nf2_lref_abst (CHead x0 (Bind Abst) x1) x0 x1 O (getl_refl Abst x0 x1)) 
I) (PCons (S x2) O PNil)) in (let H_y1 \def (H6 (CHead x0 (Bind Abst) x1) 
(THead (Flat Appl) (TLRef O) (lift (S x2) O t)) (H_y0 (drop1_cons (CHead x0 
(Bind Abst) x1) c (S x2) O (drop_drop (Bind Abst) x2 x0 c H12 x1) c PNil 
(drop1_nil c)))) in (let H_x \def (sn3_gen_flat Appl (CHead x0 (Bind Abst) 
x1) (TLRef O) (lift (S x2) O t) H_y1) in (let H14 \def H_x in (and_ind (sn3 
(CHead x0 (Bind Abst) x1) (TLRef O)) (sn3 (CHead x0 (Bind Abst) x1) (lift (S 
x2) O t)) (sn3 c t) (\lambda (_: (sn3 (CHead x0 (Bind Abst) x1) (TLRef 
O))).(\lambda (H16: (sn3 (CHead x0 (Bind Abst) x1) (lift (S x2) O 
t))).(sn3_gen_lift (CHead x0 (Bind Abst) x1) t (S x2) O H16 c (drop_drop 
(Bind Abst) x2 x0 c H12 x1)))) H14)))))))))) H11))))) H8)))) H5)))) H2))))) 
(\lambda (vs: TList).(\lambda (i: nat).(\lambda (c: C).(\lambda (H1: (arity g 
c (THeads (Flat Appl) vs (TLRef i)) (AHead a0 a1))).(\lambda (H2: (nf2 c 
(TLRef i))).(\lambda (H3: (sns3 c vs)).(conj (arity g c (THeads (Flat Appl) 
vs (TLRef i)) (AHead a0 a1)) (\forall (d: C).(\forall (w: T).((sc3 g a0 d w) 
\to (\forall (is: PList).((drop1 is d c) \to (sc3 g a1 d (THead (Flat Appl) w 
(lift1 is (THeads (Flat Appl) vs (TLRef i)))))))))) H1 (\lambda (d: 
C).(\lambda (w: T).(\lambda (H4: (sc3 g a0 d w)).(\lambda (is: 
PList).(\lambda (H5: (drop1 is d c)).(let H6 \def H in (and_ind (\forall (c0: 
C).(\forall (t: T).((sc3 g a0 c0 t) \to (sn3 c0 t)))) (\forall (vs0: 
TList).(\forall (i0: nat).(\forall (c0: C).((arity g c0 (THeads (Flat Appl) 
vs0 (TLRef i0)) a0) \to ((nf2 c0 (TLRef i0)) \to ((sns3 c0 vs0) \to (sc3 g a0 
c0 (THeads (Flat Appl) vs0 (TLRef i0))))))))) (sc3 g a1 d (THead (Flat Appl) 
w (lift1 is (THeads (Flat Appl) vs (TLRef i))))) (\lambda (H7: ((\forall (c0: 
C).(\forall (t: T).((sc3 g a0 c0 t) \to (sn3 c0 t)))))).(\lambda (_: 
((\forall (vs0: TList).(\forall (i0: nat).(\forall (c0: C).((arity g c0 
(THeads (Flat Appl) vs0 (TLRef i0)) a0) \to ((nf2 c0 (TLRef i0)) \to ((sns3 
c0 vs0) \to (sc3 g a0 c0 (THeads (Flat Appl) vs0 (TLRef i0))))))))))).(let H9 
\def H0 in (and_ind (\forall (c0: C).(\forall (t: T).((sc3 g a1 c0 t) \to 
(sn3 c0 t)))) (\forall (vs0: TList).(\forall (i0: nat).(\forall (c0: 
C).((arity g c0 (THeads (Flat Appl) vs0 (TLRef i0)) a1) \to ((nf2 c0 (TLRef 
i0)) \to ((sns3 c0 vs0) \to (sc3 g a1 c0 (THeads (Flat Appl) vs0 (TLRef 
i0))))))))) (sc3 g a1 d (THead (Flat Appl) w (lift1 is (THeads (Flat Appl) vs 
(TLRef i))))) (\lambda (_: ((\forall (c0: C).(\forall (t: T).((sc3 g a1 c0 t) 
\to (sn3 c0 t)))))).(\lambda (H11: ((\forall (vs0: TList).(\forall (i0: 
nat).(\forall (c0: C).((arity g c0 (THeads (Flat Appl) vs0 (TLRef i0)) a1) 
\to ((nf2 c0 (TLRef i0)) \to ((sns3 c0 vs0) \to (sc3 g a1 c0 (THeads (Flat 
Appl) vs0 (TLRef i0))))))))))).(let H_y \def (H11 (TCons w (lifts1 is vs))) 
in (eq_ind_r T (THeads (Flat Appl) (lifts1 is vs) (lift1 is (TLRef i))) 
(\lambda (t: T).(sc3 g a1 d (THead (Flat Appl) w t))) (eq_ind_r T (TLRef 
(trans is i)) (\lambda (t: T).(sc3 g a1 d (THead (Flat Appl) w (THeads (Flat 
Appl) (lifts1 is vs) t)))) (H_y (trans is i) d (eq_ind T (lift1 is (TLRef i)) 
(\lambda (t: T).(arity g d (THead (Flat Appl) w (THeads (Flat Appl) (lifts1 
is vs) t)) a1)) (eq_ind T (lift1 is (THeads (Flat Appl) vs (TLRef i))) 
(\lambda (t: T).(arity g d (THead (Flat Appl) w t) a1)) (arity_appl g d w a0 
(sc3_arity_gen g d w a0 H4) (lift1 is (THeads (Flat Appl) vs (TLRef i))) a1 
(arity_lift1 g (AHead a0 a1) c is d (THeads (Flat Appl) vs (TLRef i)) H5 H1)) 
(THeads (Flat Appl) (lifts1 is vs) (lift1 is (TLRef i))) (lifts1_flat Appl is 
(TLRef i) vs)) (TLRef (trans is i)) (lift1_lref is i)) (eq_ind T (lift1 is 
(TLRef i)) (\lambda (t: T).(nf2 d t)) (nf2_lift1 c is d (TLRef i) H5 H2) 
(TLRef (trans is i)) (lift1_lref is i)) (conj (sn3 d w) (sns3 d (lifts1 is 
vs)) (H7 d w H4) (sns3_lifts1 c is d H5 vs H3))) (lift1 is (TLRef i)) 
(lift1_lref is i)) (lift1 is (THeads (Flat Appl) vs (TLRef i))) (lifts1_flat 
Appl is (TLRef i) vs))))) H9)))) H6))))))))))))))))))) a)).

theorem sc3_sn3:
 \forall (g: G).(\forall (a: A).(\forall (c: C).(\forall (t: T).((sc3 g a c 
t) \to (sn3 c t)))))
\def
 \lambda (g: G).(\lambda (a: A).(\lambda (c: C).(\lambda (t: T).(\lambda (H: 
(sc3 g a c t)).(let H_x \def (sc3_props__sc3_sn3_abst g a) in (let H0 \def 
H_x in (and_ind (\forall (c0: C).(\forall (t0: T).((sc3 g a c0 t0) \to (sn3 
c0 t0)))) (\forall (vs: TList).(\forall (i: nat).(let t0 \def (THeads (Flat 
Appl) vs (TLRef i)) in (\forall (c0: C).((arity g c0 t0 a) \to ((nf2 c0 
(TLRef i)) \to ((sns3 c0 vs) \to (sc3 g a c0 t0)))))))) (sn3 c t) (\lambda 
(H1: ((\forall (c0: C).(\forall (t0: T).((sc3 g a c0 t0) \to (sn3 c0 
t0)))))).(\lambda (_: ((\forall (vs: TList).(\forall (i: nat).(let t0 \def 
(THeads (Flat Appl) vs (TLRef i)) in (\forall (c0: C).((arity g c0 t0 a) \to 
((nf2 c0 (TLRef i)) \to ((sns3 c0 vs) \to (sc3 g a c0 t0)))))))))).(H1 c t 
H))) H0))))))).

theorem sc3_abst:
 \forall (g: G).(\forall (a: A).(\forall (vs: TList).(\forall (c: C).(\forall 
(i: nat).((arity g c (THeads (Flat Appl) vs (TLRef i)) a) \to ((nf2 c (TLRef 
i)) \to ((sns3 c vs) \to (sc3 g a c (THeads (Flat Appl) vs (TLRef i))))))))))
\def
 \lambda (g: G).(\lambda (a: A).(\lambda (vs: TList).(\lambda (c: C).(\lambda 
(i: nat).(\lambda (H: (arity g c (THeads (Flat Appl) vs (TLRef i)) 
a)).(\lambda (H0: (nf2 c (TLRef i))).(\lambda (H1: (sns3 c vs)).(let H_x \def 
(sc3_props__sc3_sn3_abst g a) in (let H2 \def H_x in (and_ind (\forall (c0: 
C).(\forall (t: T).((sc3 g a c0 t) \to (sn3 c0 t)))) (\forall (vs0: 
TList).(\forall (i0: nat).(let t \def (THeads (Flat Appl) vs0 (TLRef i0)) in 
(\forall (c0: C).((arity g c0 t a) \to ((nf2 c0 (TLRef i0)) \to ((sns3 c0 
vs0) \to (sc3 g a c0 t)))))))) (sc3 g a c (THeads (Flat Appl) vs (TLRef i))) 
(\lambda (_: ((\forall (c0: C).(\forall (t: T).((sc3 g a c0 t) \to (sn3 c0 
t)))))).(\lambda (H4: ((\forall (vs0: TList).(\forall (i0: nat).(let t \def 
(THeads (Flat Appl) vs0 (TLRef i0)) in (\forall (c0: C).((arity g c0 t a) \to 
((nf2 c0 (TLRef i0)) \to ((sns3 c0 vs0) \to (sc3 g a c0 t)))))))))).(H4 vs i 
c H H0 H1))) H2)))))))))).

axiom sc3_bind:
 \forall (g: G).(\forall (b: B).((not (eq B b Abst)) \to (\forall (a1: 
A).(\forall (a2: A).(\forall (vs: TList).(\forall (c: C).(\forall (v: 
T).(\forall (t: T).((sc3 g a2 (CHead c (Bind b) v) (THeads (Flat Appl) (lifts 
(S O) O vs) t)) \to ((sc3 g a1 c v) \to (sc3 g a2 c (THeads (Flat Appl) vs 
(THead (Bind b) v t)))))))))))))
.

axiom sc3_appl:
 \forall (g: G).(\forall (a1: A).(\forall (a2: A).(\forall (vs: 
TList).(\forall (c: C).(\forall (v: T).(\forall (t: T).((sc3 g a2 c (THeads 
(Flat Appl) vs (THead (Bind Abbr) v t))) \to ((sc3 g a1 c v) \to (\forall (w: 
T).((sc3 g (asucc g a1) c w) \to (sc3 g a2 c (THeads (Flat Appl) vs (THead 
(Flat Appl) v (THead (Bind Abst) w t))))))))))))))
.

