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

set "baseuri" "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/aprem/props".

include "aprem/defs.ma".

include "leq/defs.ma".

theorem aprem_repl:
 \forall (g: G).(\forall (a1: A).(\forall (a2: A).((leq g a1 a2) \to (\forall 
(i: nat).(\forall (b2: A).((aprem i a2 b2) \to (ex2 A (\lambda (b1: A).(leq g 
b1 b2)) (\lambda (b1: A).(aprem i a1 b1)))))))))
\def
 \lambda (g: G).(\lambda (a1: A).(\lambda (a2: A).(\lambda (H: (leq g a1 
a2)).(leq_ind g (\lambda (a: A).(\lambda (a0: A).(\forall (i: nat).(\forall 
(b2: A).((aprem i a0 b2) \to (ex2 A (\lambda (b1: A).(leq g b1 b2)) (\lambda 
(b1: A).(aprem i a b1)))))))) (\lambda (h1: nat).(\lambda (h2: nat).(\lambda 
(n1: nat).(\lambda (n2: nat).(\lambda (k: nat).(\lambda (_: (eq A (aplus g 
(ASort h1 n1) k) (aplus g (ASort h2 n2) k))).(\lambda (i: nat).(\lambda (b2: 
A).(\lambda (H1: (aprem i (ASort h2 n2) b2)).(let H2 \def (match H1 in aprem 
return (\lambda (n: nat).(\lambda (a: A).(\lambda (a0: A).(\lambda (_: (aprem 
n a a0)).((eq nat n i) \to ((eq A a (ASort h2 n2)) \to ((eq A a0 b2) \to (ex2 
A (\lambda (b1: A).(leq g b1 b2)) (\lambda (b1: A).(aprem i (ASort h1 n1) 
b1)))))))))) with [(aprem_zero a0 a3) \Rightarrow (\lambda (H2: (eq nat O 
i)).(\lambda (H3: (eq A (AHead a0 a3) (ASort h2 n2))).(\lambda (H4: (eq A a0 
b2)).(eq_ind nat O (\lambda (n: nat).((eq A (AHead a0 a3) (ASort h2 n2)) \to 
((eq A a0 b2) \to (ex2 A (\lambda (b1: A).(leq g b1 b2)) (\lambda (b1: 
A).(aprem n (ASort h1 n1) b1)))))) (\lambda (H5: (eq A (AHead a0 a3) (ASort 
h2 n2))).(let H6 \def (eq_ind A (AHead a0 a3) (\lambda (e: A).(match e in A 
return (\lambda (_: A).Prop) with [(ASort _ _) \Rightarrow False | (AHead _ 
_) \Rightarrow True])) I (ASort h2 n2) H5) in (False_ind ((eq A a0 b2) \to 
(ex2 A (\lambda (b1: A).(leq g b1 b2)) (\lambda (b1: A).(aprem O (ASort h1 
n1) b1)))) H6))) i H2 H3 H4)))) | (aprem_succ a0 a i0 H2 a3) \Rightarrow 
(\lambda (H3: (eq nat (S i0) i)).(\lambda (H4: (eq A (AHead a3 a0) (ASort h2 
n2))).(\lambda (H5: (eq A a b2)).(eq_ind nat (S i0) (\lambda (n: nat).((eq A 
(AHead a3 a0) (ASort h2 n2)) \to ((eq A a b2) \to ((aprem i0 a0 a) \to (ex2 A 
(\lambda (b1: A).(leq g b1 b2)) (\lambda (b1: A).(aprem n (ASort h1 n1) 
b1))))))) (\lambda (H6: (eq A (AHead a3 a0) (ASort h2 n2))).(let H7 \def 
(eq_ind A (AHead a3 a0) (\lambda (e: A).(match e in A return (\lambda (_: 
A).Prop) with [(ASort _ _) \Rightarrow False | (AHead _ _) \Rightarrow 
True])) I (ASort h2 n2) H6) in (False_ind ((eq A a b2) \to ((aprem i0 a0 a) 
\to (ex2 A (\lambda (b1: A).(leq g b1 b2)) (\lambda (b1: A).(aprem (S i0) 
(ASort h1 n1) b1))))) H7))) i H3 H4 H5 H2))))]) in (H2 (refl_equal nat i) 
(refl_equal A (ASort h2 n2)) (refl_equal A b2)))))))))))) (\lambda (a0: 
A).(\lambda (a3: A).(\lambda (H0: (leq g a0 a3)).(\lambda (_: ((\forall (i: 
nat).(\forall (b2: A).((aprem i a3 b2) \to (ex2 A (\lambda (b1: A).(leq g b1 
b2)) (\lambda (b1: A).(aprem i a0 b1)))))))).(\lambda (a4: A).(\lambda (a5: 
A).(\lambda (_: (leq g a4 a5)).(\lambda (H3: ((\forall (i: nat).(\forall (b2: 
A).((aprem i a5 b2) \to (ex2 A (\lambda (b1: A).(leq g b1 b2)) (\lambda (b1: 
A).(aprem i a4 b1)))))))).(\lambda (i: nat).(\lambda (b2: A).(\lambda (H4: 
(aprem i (AHead a3 a5) b2)).(nat_ind (\lambda (n: nat).((aprem n (AHead a3 
a5) b2) \to (ex2 A (\lambda (b1: A).(leq g b1 b2)) (\lambda (b1: A).(aprem n 
(AHead a0 a4) b1))))) (\lambda (H5: (aprem O (AHead a3 a5) b2)).(let H6 \def 
(match H5 in aprem return (\lambda (n: nat).(\lambda (a: A).(\lambda (a6: 
A).(\lambda (_: (aprem n a a6)).((eq nat n O) \to ((eq A a (AHead a3 a5)) \to 
((eq A a6 b2) \to (ex2 A (\lambda (b1: A).(leq g b1 b2)) (\lambda (b1: 
A).(aprem O (AHead a0 a4) b1)))))))))) with [(aprem_zero a6 a7) \Rightarrow 
(\lambda (_: (eq nat O O)).(\lambda (H7: (eq A (AHead a6 a7) (AHead a3 
a5))).(\lambda (H8: (eq A a6 b2)).((let H9 \def (f_equal A A (\lambda (e: 
A).(match e in A return (\lambda (_: A).A) with [(ASort _ _) \Rightarrow a7 | 
(AHead _ a) \Rightarrow a])) (AHead a6 a7) (AHead a3 a5) H7) in ((let H10 
\def (f_equal A A (\lambda (e: A).(match e in A return (\lambda (_: A).A) 
with [(ASort _ _) \Rightarrow a6 | (AHead a _) \Rightarrow a])) (AHead a6 a7) 
(AHead a3 a5) H7) in (eq_ind A a3 (\lambda (a: A).((eq A a7 a5) \to ((eq A a 
b2) \to (ex2 A (\lambda (b1: A).(leq g b1 b2)) (\lambda (b1: A).(aprem O 
(AHead a0 a4) b1)))))) (\lambda (H11: (eq A a7 a5)).(eq_ind A a5 (\lambda (_: 
A).((eq A a3 b2) \to (ex2 A (\lambda (b1: A).(leq g b1 b2)) (\lambda (b1: 
A).(aprem O (AHead a0 a4) b1))))) (\lambda (H12: (eq A a3 b2)).(eq_ind A b2 
(\lambda (_: A).(ex2 A (\lambda (b1: A).(leq g b1 b2)) (\lambda (b1: 
A).(aprem O (AHead a0 a4) b1)))) (eq_ind A a3 (\lambda (a: A).(ex2 A (\lambda 
(b1: A).(leq g b1 a)) (\lambda (b1: A).(aprem O (AHead a0 a4) b1)))) 
(ex_intro2 A (\lambda (b1: A).(leq g b1 a3)) (\lambda (b1: A).(aprem O (AHead 
a0 a4) b1)) a0 H0 (aprem_zero a0 a4)) b2 H12) a3 (sym_eq A a3 b2 H12))) a7 
(sym_eq A a7 a5 H11))) a6 (sym_eq A a6 a3 H10))) H9)) H8)))) | (aprem_succ a6 
a i0 H6 a7) \Rightarrow (\lambda (H7: (eq nat (S i0) O)).(\lambda (H8: (eq A 
(AHead a7 a6) (AHead a3 a5))).(\lambda (H9: (eq A a b2)).((let H10 \def 
(eq_ind nat (S i0) (\lambda (e: nat).(match e in nat return (\lambda (_: 
nat).Prop) with [O \Rightarrow False | (S _) \Rightarrow True])) I O H7) in 
(False_ind ((eq A (AHead a7 a6) (AHead a3 a5)) \to ((eq A a b2) \to ((aprem 
i0 a6 a) \to (ex2 A (\lambda (b1: A).(leq g b1 b2)) (\lambda (b1: A).(aprem O 
(AHead a0 a4) b1)))))) H10)) H8 H9 H6))))]) in (H6 (refl_equal nat O) 
(refl_equal A (AHead a3 a5)) (refl_equal A b2)))) (\lambda (i0: nat).(\lambda 
(_: (((aprem i0 (AHead a3 a5) b2) \to (ex2 A (\lambda (b1: A).(leq g b1 b2)) 
(\lambda (b1: A).(aprem i0 (AHead a0 a4) b1)))))).(\lambda (H5: (aprem (S i0) 
(AHead a3 a5) b2)).(let H6 \def (match H5 in aprem return (\lambda (n: 
nat).(\lambda (a: A).(\lambda (a6: A).(\lambda (_: (aprem n a a6)).((eq nat n 
(S i0)) \to ((eq A a (AHead a3 a5)) \to ((eq A a6 b2) \to (ex2 A (\lambda 
(b1: A).(leq g b1 b2)) (\lambda (b1: A).(aprem (S i0) (AHead a0 a4) 
b1)))))))))) with [(aprem_zero a6 a7) \Rightarrow (\lambda (H6: (eq nat O (S 
i0))).(\lambda (H7: (eq A (AHead a6 a7) (AHead a3 a5))).(\lambda (H8: (eq A 
a6 b2)).((let H9 \def (eq_ind nat O (\lambda (e: nat).(match e in nat return 
(\lambda (_: nat).Prop) with [O \Rightarrow True | (S _) \Rightarrow False])) 
I (S i0) H6) in (False_ind ((eq A (AHead a6 a7) (AHead a3 a5)) \to ((eq A a6 
b2) \to (ex2 A (\lambda (b1: A).(leq g b1 b2)) (\lambda (b1: A).(aprem (S i0) 
(AHead a0 a4) b1))))) H9)) H7 H8)))) | (aprem_succ a6 a i1 H6 a7) \Rightarrow 
(\lambda (H7: (eq nat (S i1) (S i0))).(\lambda (H8: (eq A (AHead a7 a6) 
(AHead a3 a5))).(\lambda (H9: (eq A a b2)).((let H10 \def (f_equal nat nat 
(\lambda (e: nat).(match e in nat return (\lambda (_: nat).nat) with [O 
\Rightarrow i1 | (S n) \Rightarrow n])) (S i1) (S i0) H7) in (eq_ind nat i0 
(\lambda (n: nat).((eq A (AHead a7 a6) (AHead a3 a5)) \to ((eq A a b2) \to 
((aprem n a6 a) \to (ex2 A (\lambda (b1: A).(leq g b1 b2)) (\lambda (b1: 
A).(aprem (S i0) (AHead a0 a4) b1))))))) (\lambda (H11: (eq A (AHead a7 a6) 
(AHead a3 a5))).(let H12 \def (f_equal A A (\lambda (e: A).(match e in A 
return (\lambda (_: A).A) with [(ASort _ _) \Rightarrow a6 | (AHead _ a8) 
\Rightarrow a8])) (AHead a7 a6) (AHead a3 a5) H11) in ((let H13 \def (f_equal 
A A (\lambda (e: A).(match e in A return (\lambda (_: A).A) with [(ASort _ _) 
\Rightarrow a7 | (AHead a8 _) \Rightarrow a8])) (AHead a7 a6) (AHead a3 a5) 
H11) in (eq_ind A a3 (\lambda (_: A).((eq A a6 a5) \to ((eq A a b2) \to 
((aprem i0 a6 a) \to (ex2 A (\lambda (b1: A).(leq g b1 b2)) (\lambda (b1: 
A).(aprem (S i0) (AHead a0 a4) b1))))))) (\lambda (H14: (eq A a6 a5)).(eq_ind 
A a5 (\lambda (a8: A).((eq A a b2) \to ((aprem i0 a8 a) \to (ex2 A (\lambda 
(b1: A).(leq g b1 b2)) (\lambda (b1: A).(aprem (S i0) (AHead a0 a4) b1)))))) 
(\lambda (H15: (eq A a b2)).(eq_ind A b2 (\lambda (a8: A).((aprem i0 a5 a8) 
\to (ex2 A (\lambda (b1: A).(leq g b1 b2)) (\lambda (b1: A).(aprem (S i0) 
(AHead a0 a4) b1))))) (\lambda (H16: (aprem i0 a5 b2)).(let H_x \def (H3 i0 
b2 H16) in (let H17 \def H_x in (ex2_ind A (\lambda (b1: A).(leq g b1 b2)) 
(\lambda (b1: A).(aprem i0 a4 b1)) (ex2 A (\lambda (b1: A).(leq g b1 b2)) 
(\lambda (b1: A).(aprem (S i0) (AHead a0 a4) b1))) (\lambda (x: A).(\lambda 
(H18: (leq g x b2)).(\lambda (H19: (aprem i0 a4 x)).(ex_intro2 A (\lambda 
(b1: A).(leq g b1 b2)) (\lambda (b1: A).(aprem (S i0) (AHead a0 a4) b1)) x 
H18 (aprem_succ a4 x i0 H19 a0))))) H17)))) a (sym_eq A a b2 H15))) a6 
(sym_eq A a6 a5 H14))) a7 (sym_eq A a7 a3 H13))) H12))) i1 (sym_eq nat i1 i0 
H10))) H8 H9 H6))))]) in (H6 (refl_equal nat (S i0)) (refl_equal A (AHead a3 
a5)) (refl_equal A b2)))))) i H4)))))))))))) a1 a2 H)))).

theorem aprem_asucc:
 \forall (g: G).(\forall (a1: A).(\forall (a2: A).(\forall (i: nat).((aprem i 
a1 a2) \to (aprem i (asucc g a1) a2)))))
\def
 \lambda (g: G).(\lambda (a1: A).(\lambda (a2: A).(\lambda (i: nat).(\lambda 
(H: (aprem i a1 a2)).(aprem_ind (\lambda (n: nat).(\lambda (a: A).(\lambda 
(a0: A).(aprem n (asucc g a) a0)))) (\lambda (a0: A).(\lambda (a3: 
A).(aprem_zero a0 (asucc g a3)))) (\lambda (a0: A).(\lambda (a: A).(\lambda 
(i0: nat).(\lambda (_: (aprem i0 a0 a)).(\lambda (H1: (aprem i0 (asucc g a0) 
a)).(\lambda (a3: A).(aprem_succ (asucc g a0) a i0 H1 a3))))))) i a1 a2 
H))))).

