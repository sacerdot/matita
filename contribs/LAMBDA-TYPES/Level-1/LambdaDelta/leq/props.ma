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

set "baseuri" "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/leq/props".

include "leq/defs.ma".

theorem ahead_inj_snd:
 \forall (g: G).(\forall (a1: A).(\forall (a2: A).(\forall (a3: A).(\forall 
(a4: A).((leq g (AHead a1 a2) (AHead a3 a4)) \to (leq g a2 a4))))))
\def
 \lambda (g: G).(\lambda (a1: A).(\lambda (a2: A).(\lambda (a3: A).(\lambda 
(a4: A).(\lambda (H: (leq g (AHead a1 a2) (AHead a3 a4))).(let H0 \def (match 
H in leq return (\lambda (a: A).(\lambda (a0: A).(\lambda (_: (leq ? a 
a0)).((eq A a (AHead a1 a2)) \to ((eq A a0 (AHead a3 a4)) \to (leq g a2 
a4)))))) with [(leq_sort h1 h2 n1 n2 k H0) \Rightarrow (\lambda (H1: (eq A 
(ASort h1 n1) (AHead a1 a2))).(\lambda (H2: (eq A (ASort h2 n2) (AHead a3 
a4))).((let H3 \def (eq_ind A (ASort h1 n1) (\lambda (e: A).(match e in A 
return (\lambda (_: A).Prop) with [(ASort _ _) \Rightarrow True | (AHead _ _) 
\Rightarrow False])) I (AHead a1 a2) H1) in (False_ind ((eq A (ASort h2 n2) 
(AHead a3 a4)) \to ((eq A (aplus g (ASort h1 n1) k) (aplus g (ASort h2 n2) 
k)) \to (leq g a2 a4))) H3)) H2 H0))) | (leq_head a0 a5 H0 a6 a7 H1) 
\Rightarrow (\lambda (H2: (eq A (AHead a0 a6) (AHead a1 a2))).(\lambda (H3: 
(eq A (AHead a5 a7) (AHead a3 a4))).((let H4 \def (f_equal A A (\lambda (e: 
A).(match e in A return (\lambda (_: A).A) with [(ASort _ _) \Rightarrow a6 | 
(AHead _ a) \Rightarrow a])) (AHead a0 a6) (AHead a1 a2) H2) in ((let H5 \def 
(f_equal A A (\lambda (e: A).(match e in A return (\lambda (_: A).A) with 
[(ASort _ _) \Rightarrow a0 | (AHead a _) \Rightarrow a])) (AHead a0 a6) 
(AHead a1 a2) H2) in (eq_ind A a1 (\lambda (a: A).((eq A a6 a2) \to ((eq A 
(AHead a5 a7) (AHead a3 a4)) \to ((leq g a a5) \to ((leq g a6 a7) \to (leq g 
a2 a4)))))) (\lambda (H6: (eq A a6 a2)).(eq_ind A a2 (\lambda (a: A).((eq A 
(AHead a5 a7) (AHead a3 a4)) \to ((leq g a1 a5) \to ((leq g a a7) \to (leq g 
a2 a4))))) (\lambda (H7: (eq A (AHead a5 a7) (AHead a3 a4))).(let H8 \def 
(f_equal A A (\lambda (e: A).(match e in A return (\lambda (_: A).A) with 
[(ASort _ _) \Rightarrow a7 | (AHead _ a) \Rightarrow a])) (AHead a5 a7) 
(AHead a3 a4) H7) in ((let H9 \def (f_equal A A (\lambda (e: A).(match e in A 
return (\lambda (_: A).A) with [(ASort _ _) \Rightarrow a5 | (AHead a _) 
\Rightarrow a])) (AHead a5 a7) (AHead a3 a4) H7) in (eq_ind A a3 (\lambda (a: 
A).((eq A a7 a4) \to ((leq g a1 a) \to ((leq g a2 a7) \to (leq g a2 a4))))) 
(\lambda (H10: (eq A a7 a4)).(eq_ind A a4 (\lambda (a: A).((leq g a1 a3) \to 
((leq g a2 a) \to (leq g a2 a4)))) (\lambda (_: (leq g a1 a3)).(\lambda (H12: 
(leq g a2 a4)).H12)) a7 (sym_eq A a7 a4 H10))) a5 (sym_eq A a5 a3 H9))) H8))) 
a6 (sym_eq A a6 a2 H6))) a0 (sym_eq A a0 a1 H5))) H4)) H3 H0 H1)))]) in (H0 
(refl_equal A (AHead a1 a2)) (refl_equal A (AHead a3 a4))))))))).

theorem leq_refl:
 \forall (g: G).(\forall (a: A).(leq g a a))
\def
 \lambda (g: G).(\lambda (a: A).(A_ind (\lambda (a0: A).(leq g a0 a0)) 
(\lambda (n: nat).(\lambda (n0: nat).(leq_sort g n n n0 n0 O (refl_equal A 
(aplus g (ASort n n0) O))))) (\lambda (a0: A).(\lambda (H: (leq g a0 
a0)).(\lambda (a1: A).(\lambda (H0: (leq g a1 a1)).(leq_head g a0 a0 H a1 a1 
H0))))) a)).

theorem leq_eq:
 \forall (g: G).(\forall (a1: A).(\forall (a2: A).((eq A a1 a2) \to (leq g a1 
a2))))
\def
 \lambda (g: G).(\lambda (a1: A).(\lambda (a2: A).(\lambda (H: (eq A a1 
a2)).(eq_ind_r A a2 (\lambda (a: A).(leq g a a2)) (leq_refl g a2) a1 H)))).

theorem leq_sym:
 \forall (g: G).(\forall (a1: A).(\forall (a2: A).((leq g a1 a2) \to (leq g 
a2 a1))))
\def
 \lambda (g: G).(\lambda (a1: A).(\lambda (a2: A).(\lambda (H: (leq g a1 
a2)).(leq_ind g (\lambda (a: A).(\lambda (a0: A).(leq g a0 a))) (\lambda (h1: 
nat).(\lambda (h2: nat).(\lambda (n1: nat).(\lambda (n2: nat).(\lambda (k: 
nat).(\lambda (H0: (eq A (aplus g (ASort h1 n1) k) (aplus g (ASort h2 n2) 
k))).(leq_sort g h2 h1 n2 n1 k (sym_eq A (aplus g (ASort h1 n1) k) (aplus g 
(ASort h2 n2) k) H0)))))))) (\lambda (a3: A).(\lambda (a4: A).(\lambda (_: 
(leq g a3 a4)).(\lambda (H1: (leq g a4 a3)).(\lambda (a5: A).(\lambda (a6: 
A).(\lambda (_: (leq g a5 a6)).(\lambda (H3: (leq g a6 a5)).(leq_head g a4 a3 
H1 a6 a5 H3))))))))) a1 a2 H)))).

axiom leq_trans:
 \forall (g: G).(\forall (a1: A).(\forall (a2: A).((leq g a1 a2) \to (\forall 
(a3: A).((leq g a2 a3) \to (leq g a1 a3))))))
.

theorem leq_ahead_false:
 \forall (g: G).(\forall (a1: A).(\forall (a2: A).((leq g (AHead a1 a2) a1) 
\to (\forall (P: Prop).P))))
\def
 \lambda (g: G).(\lambda (a1: A).(A_ind (\lambda (a: A).(\forall (a2: 
A).((leq g (AHead a a2) a) \to (\forall (P: Prop).P)))) (\lambda (n: 
nat).(\lambda (n0: nat).(\lambda (a2: A).(\lambda (H: (leq g (AHead (ASort n 
n0) a2) (ASort n n0))).(\lambda (P: Prop).((match n in nat return (\lambda 
(n1: nat).((leq g (AHead (ASort n1 n0) a2) (ASort n1 n0)) \to P)) with [O 
\Rightarrow (\lambda (H0: (leq g (AHead (ASort O n0) a2) (ASort O n0))).(let 
H1 \def (match H0 in leq return (\lambda (a: A).(\lambda (a0: A).(\lambda (_: 
(leq ? a a0)).((eq A a (AHead (ASort O n0) a2)) \to ((eq A a0 (ASort O n0)) 
\to P))))) with [(leq_sort h1 h2 n1 n2 k H1) \Rightarrow (\lambda (H2: (eq A 
(ASort h1 n1) (AHead (ASort O n0) a2))).(\lambda (H3: (eq A (ASort h2 n2) 
(ASort O n0))).((let H4 \def (eq_ind A (ASort h1 n1) (\lambda (e: A).(match e 
in A return (\lambda (_: A).Prop) with [(ASort _ _) \Rightarrow True | (AHead 
_ _) \Rightarrow False])) I (AHead (ASort O n0) a2) H2) in (False_ind ((eq A 
(ASort h2 n2) (ASort O n0)) \to ((eq A (aplus g (ASort h1 n1) k) (aplus g 
(ASort h2 n2) k)) \to P)) H4)) H3 H1))) | (leq_head a0 a3 H1 a4 a5 H2) 
\Rightarrow (\lambda (H3: (eq A (AHead a0 a4) (AHead (ASort O n0) 
a2))).(\lambda (H4: (eq A (AHead a3 a5) (ASort O n0))).((let H5 \def (f_equal 
A A (\lambda (e: A).(match e in A return (\lambda (_: A).A) with [(ASort _ _) 
\Rightarrow a4 | (AHead _ a) \Rightarrow a])) (AHead a0 a4) (AHead (ASort O 
n0) a2) H3) in ((let H6 \def (f_equal A A (\lambda (e: A).(match e in A 
return (\lambda (_: A).A) with [(ASort _ _) \Rightarrow a0 | (AHead a _) 
\Rightarrow a])) (AHead a0 a4) (AHead (ASort O n0) a2) H3) in (eq_ind A 
(ASort O n0) (\lambda (a: A).((eq A a4 a2) \to ((eq A (AHead a3 a5) (ASort O 
n0)) \to ((leq g a a3) \to ((leq g a4 a5) \to P))))) (\lambda (H7: (eq A a4 
a2)).(eq_ind A a2 (\lambda (a: A).((eq A (AHead a3 a5) (ASort O n0)) \to 
((leq g (ASort O n0) a3) \to ((leq g a a5) \to P)))) (\lambda (H8: (eq A 
(AHead a3 a5) (ASort O n0))).(let H9 \def (eq_ind A (AHead a3 a5) (\lambda 
(e: A).(match e in A return (\lambda (_: A).Prop) with [(ASort _ _) 
\Rightarrow False | (AHead _ _) \Rightarrow True])) I (ASort O n0) H8) in 
(False_ind ((leq g (ASort O n0) a3) \to ((leq g a2 a5) \to P)) H9))) a4 
(sym_eq A a4 a2 H7))) a0 (sym_eq A a0 (ASort O n0) H6))) H5)) H4 H1 H2)))]) 
in (H1 (refl_equal A (AHead (ASort O n0) a2)) (refl_equal A (ASort O n0))))) 
| (S n1) \Rightarrow (\lambda (H0: (leq g (AHead (ASort (S n1) n0) a2) (ASort 
(S n1) n0))).(let H1 \def (match H0 in leq return (\lambda (a: A).(\lambda 
(a0: A).(\lambda (_: (leq ? a a0)).((eq A a (AHead (ASort (S n1) n0) a2)) \to 
((eq A a0 (ASort (S n1) n0)) \to P))))) with [(leq_sort h1 h2 n2 n3 k H1) 
\Rightarrow (\lambda (H2: (eq A (ASort h1 n2) (AHead (ASort (S n1) n0) 
a2))).(\lambda (H3: (eq A (ASort h2 n3) (ASort (S n1) n0))).((let H4 \def 
(eq_ind A (ASort h1 n2) (\lambda (e: A).(match e in A return (\lambda (_: 
A).Prop) with [(ASort _ _) \Rightarrow True | (AHead _ _) \Rightarrow 
False])) I (AHead (ASort (S n1) n0) a2) H2) in (False_ind ((eq A (ASort h2 
n3) (ASort (S n1) n0)) \to ((eq A (aplus g (ASort h1 n2) k) (aplus g (ASort 
h2 n3) k)) \to P)) H4)) H3 H1))) | (leq_head a0 a3 H1 a4 a5 H2) \Rightarrow 
(\lambda (H3: (eq A (AHead a0 a4) (AHead (ASort (S n1) n0) a2))).(\lambda 
(H4: (eq A (AHead a3 a5) (ASort (S n1) n0))).((let H5 \def (f_equal A A 
(\lambda (e: A).(match e in A return (\lambda (_: A).A) with [(ASort _ _) 
\Rightarrow a4 | (AHead _ a) \Rightarrow a])) (AHead a0 a4) (AHead (ASort (S 
n1) n0) a2) H3) in ((let H6 \def (f_equal A A (\lambda (e: A).(match e in A 
return (\lambda (_: A).A) with [(ASort _ _) \Rightarrow a0 | (AHead a _) 
\Rightarrow a])) (AHead a0 a4) (AHead (ASort (S n1) n0) a2) H3) in (eq_ind A 
(ASort (S n1) n0) (\lambda (a: A).((eq A a4 a2) \to ((eq A (AHead a3 a5) 
(ASort (S n1) n0)) \to ((leq g a a3) \to ((leq g a4 a5) \to P))))) (\lambda 
(H7: (eq A a4 a2)).(eq_ind A a2 (\lambda (a: A).((eq A (AHead a3 a5) (ASort 
(S n1) n0)) \to ((leq g (ASort (S n1) n0) a3) \to ((leq g a a5) \to P)))) 
(\lambda (H8: (eq A (AHead a3 a5) (ASort (S n1) n0))).(let H9 \def (eq_ind A 
(AHead a3 a5) (\lambda (e: A).(match e in A return (\lambda (_: A).Prop) with 
[(ASort _ _) \Rightarrow False | (AHead _ _) \Rightarrow True])) I (ASort (S 
n1) n0) H8) in (False_ind ((leq g (ASort (S n1) n0) a3) \to ((leq g a2 a5) 
\to P)) H9))) a4 (sym_eq A a4 a2 H7))) a0 (sym_eq A a0 (ASort (S n1) n0) 
H6))) H5)) H4 H1 H2)))]) in (H1 (refl_equal A (AHead (ASort (S n1) n0) a2)) 
(refl_equal A (ASort (S n1) n0)))))]) H)))))) (\lambda (a: A).(\lambda (H: 
((\forall (a2: A).((leq g (AHead a a2) a) \to (\forall (P: 
Prop).P))))).(\lambda (a0: A).(\lambda (_: ((\forall (a2: A).((leq g (AHead 
a0 a2) a0) \to (\forall (P: Prop).P))))).(\lambda (a2: A).(\lambda (H1: (leq 
g (AHead (AHead a a0) a2) (AHead a a0))).(\lambda (P: Prop).(let H2 \def 
(match H1 in leq return (\lambda (a3: A).(\lambda (a4: A).(\lambda (_: (leq ? 
a3 a4)).((eq A a3 (AHead (AHead a a0) a2)) \to ((eq A a4 (AHead a a0)) \to 
P))))) with [(leq_sort h1 h2 n1 n2 k H2) \Rightarrow (\lambda (H3: (eq A 
(ASort h1 n1) (AHead (AHead a a0) a2))).(\lambda (H4: (eq A (ASort h2 n2) 
(AHead a a0))).((let H5 \def (eq_ind A (ASort h1 n1) (\lambda (e: A).(match e 
in A return (\lambda (_: A).Prop) with [(ASort _ _) \Rightarrow True | (AHead 
_ _) \Rightarrow False])) I (AHead (AHead a a0) a2) H3) in (False_ind ((eq A 
(ASort h2 n2) (AHead a a0)) \to ((eq A (aplus g (ASort h1 n1) k) (aplus g 
(ASort h2 n2) k)) \to P)) H5)) H4 H2))) | (leq_head a3 a4 H2 a5 a6 H3) 
\Rightarrow (\lambda (H4: (eq A (AHead a3 a5) (AHead (AHead a a0) 
a2))).(\lambda (H5: (eq A (AHead a4 a6) (AHead a a0))).((let H6 \def (f_equal 
A A (\lambda (e: A).(match e in A return (\lambda (_: A).A) with [(ASort _ _) 
\Rightarrow a5 | (AHead _ a7) \Rightarrow a7])) (AHead a3 a5) (AHead (AHead a 
a0) a2) H4) in ((let H7 \def (f_equal A A (\lambda (e: A).(match e in A 
return (\lambda (_: A).A) with [(ASort _ _) \Rightarrow a3 | (AHead a7 _) 
\Rightarrow a7])) (AHead a3 a5) (AHead (AHead a a0) a2) H4) in (eq_ind A 
(AHead a a0) (\lambda (a7: A).((eq A a5 a2) \to ((eq A (AHead a4 a6) (AHead a 
a0)) \to ((leq g a7 a4) \to ((leq g a5 a6) \to P))))) (\lambda (H8: (eq A a5 
a2)).(eq_ind A a2 (\lambda (a7: A).((eq A (AHead a4 a6) (AHead a a0)) \to 
((leq g (AHead a a0) a4) \to ((leq g a7 a6) \to P)))) (\lambda (H9: (eq A 
(AHead a4 a6) (AHead a a0))).(let H10 \def (f_equal A A (\lambda (e: 
A).(match e in A return (\lambda (_: A).A) with [(ASort _ _) \Rightarrow a6 | 
(AHead _ a7) \Rightarrow a7])) (AHead a4 a6) (AHead a a0) H9) in ((let H11 
\def (f_equal A A (\lambda (e: A).(match e in A return (\lambda (_: A).A) 
with [(ASort _ _) \Rightarrow a4 | (AHead a7 _) \Rightarrow a7])) (AHead a4 
a6) (AHead a a0) H9) in (eq_ind A a (\lambda (a7: A).((eq A a6 a0) \to ((leq 
g (AHead a a0) a7) \to ((leq g a2 a6) \to P)))) (\lambda (H12: (eq A a6 
a0)).(eq_ind A a0 (\lambda (a7: A).((leq g (AHead a a0) a) \to ((leq g a2 a7) 
\to P))) (\lambda (H13: (leq g (AHead a a0) a)).(\lambda (_: (leq g a2 
a0)).(H a0 H13 P))) a6 (sym_eq A a6 a0 H12))) a4 (sym_eq A a4 a H11))) H10))) 
a5 (sym_eq A a5 a2 H8))) a3 (sym_eq A a3 (AHead a a0) H7))) H6)) H5 H2 
H3)))]) in (H2 (refl_equal A (AHead (AHead a a0) a2)) (refl_equal A (AHead a 
a0))))))))))) a1)).

