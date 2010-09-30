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

include "Basic-1/asucc/defs.ma".

theorem asucc_gen_sort:
 \forall (g: G).(\forall (h: nat).(\forall (n: nat).(\forall (a: A).((eq A 
(ASort h n) (asucc g a)) \to (ex_2 nat nat (\lambda (h0: nat).(\lambda (n0: 
nat).(eq A a (ASort h0 n0)))))))))
\def
 \lambda (g: G).(\lambda (h: nat).(\lambda (n: nat).(\lambda (a: A).(A_ind 
(\lambda (a0: A).((eq A (ASort h n) (asucc g a0)) \to (ex_2 nat nat (\lambda 
(h0: nat).(\lambda (n0: nat).(eq A a0 (ASort h0 n0))))))) (\lambda (n0: 
nat).(\lambda (n1: nat).(\lambda (H: (eq A (ASort h n) (asucc g (ASort n0 
n1)))).(let H0 \def (f_equal A A (\lambda (e: A).e) (ASort h n) (match n0 
with [O \Rightarrow (ASort O (next g n1)) | (S h0) \Rightarrow (ASort h0 
n1)]) H) in (ex_2_intro nat nat (\lambda (h0: nat).(\lambda (n2: nat).(eq A 
(ASort n0 n1) (ASort h0 n2)))) n0 n1 (refl_equal A (ASort n0 n1))))))) 
(\lambda (a0: A).(\lambda (_: (((eq A (ASort h n) (asucc g a0)) \to (ex_2 nat 
nat (\lambda (h0: nat).(\lambda (n0: nat).(eq A a0 (ASort h0 
n0)))))))).(\lambda (a1: A).(\lambda (_: (((eq A (ASort h n) (asucc g a1)) 
\to (ex_2 nat nat (\lambda (h0: nat).(\lambda (n0: nat).(eq A a1 (ASort h0 
n0)))))))).(\lambda (H1: (eq A (ASort h n) (asucc g (AHead a0 a1)))).(let H2 
\def (eq_ind A (ASort h n) (\lambda (ee: A).(match ee in A return (\lambda 
(_: A).Prop) with [(ASort _ _) \Rightarrow True | (AHead _ _) \Rightarrow 
False])) I (asucc g (AHead a0 a1)) H1) in (False_ind (ex_2 nat nat (\lambda 
(h0: nat).(\lambda (n0: nat).(eq A (AHead a0 a1) (ASort h0 n0))))) H2))))))) 
a)))).
(* COMMENTS
Initial nodes: 317
END *)

theorem asucc_gen_head:
 \forall (g: G).(\forall (a1: A).(\forall (a2: A).(\forall (a: A).((eq A 
(AHead a1 a2) (asucc g a)) \to (ex2 A (\lambda (a0: A).(eq A a (AHead a1 
a0))) (\lambda (a0: A).(eq A a2 (asucc g a0))))))))
\def
 \lambda (g: G).(\lambda (a1: A).(\lambda (a2: A).(\lambda (a: A).(A_ind 
(\lambda (a0: A).((eq A (AHead a1 a2) (asucc g a0)) \to (ex2 A (\lambda (a3: 
A).(eq A a0 (AHead a1 a3))) (\lambda (a3: A).(eq A a2 (asucc g a3)))))) 
(\lambda (n: nat).(\lambda (n0: nat).(\lambda (H: (eq A (AHead a1 a2) (asucc 
g (ASort n n0)))).(nat_ind (\lambda (n1: nat).((eq A (AHead a1 a2) (asucc g 
(ASort n1 n0))) \to (ex2 A (\lambda (a0: A).(eq A (ASort n1 n0) (AHead a1 
a0))) (\lambda (a0: A).(eq A a2 (asucc g a0)))))) (\lambda (H0: (eq A (AHead 
a1 a2) (asucc g (ASort O n0)))).(let H1 \def (eq_ind A (AHead a1 a2) (\lambda 
(ee: A).(match ee in A return (\lambda (_: A).Prop) with [(ASort _ _) 
\Rightarrow False | (AHead _ _) \Rightarrow True])) I (ASort O (next g n0)) 
H0) in (False_ind (ex2 A (\lambda (a0: A).(eq A (ASort O n0) (AHead a1 a0))) 
(\lambda (a0: A).(eq A a2 (asucc g a0)))) H1))) (\lambda (n1: nat).(\lambda 
(_: (((eq A (AHead a1 a2) (asucc g (ASort n1 n0))) \to (ex2 A (\lambda (a0: 
A).(eq A (ASort n1 n0) (AHead a1 a0))) (\lambda (a0: A).(eq A a2 (asucc g 
a0))))))).(\lambda (H0: (eq A (AHead a1 a2) (asucc g (ASort (S n1) 
n0)))).(let H1 \def (eq_ind A (AHead a1 a2) (\lambda (ee: A).(match ee in A 
return (\lambda (_: A).Prop) with [(ASort _ _) \Rightarrow False | (AHead _ 
_) \Rightarrow True])) I (ASort n1 n0) H0) in (False_ind (ex2 A (\lambda (a0: 
A).(eq A (ASort (S n1) n0) (AHead a1 a0))) (\lambda (a0: A).(eq A a2 (asucc g 
a0)))) H1))))) n H)))) (\lambda (a0: A).(\lambda (H: (((eq A (AHead a1 a2) 
(asucc g a0)) \to (ex2 A (\lambda (a3: A).(eq A a0 (AHead a1 a3))) (\lambda 
(a3: A).(eq A a2 (asucc g a3))))))).(\lambda (a3: A).(\lambda (H0: (((eq A 
(AHead a1 a2) (asucc g a3)) \to (ex2 A (\lambda (a4: A).(eq A a3 (AHead a1 
a4))) (\lambda (a4: A).(eq A a2 (asucc g a4))))))).(\lambda (H1: (eq A (AHead 
a1 a2) (asucc g (AHead a0 a3)))).(let H2 \def (f_equal A A (\lambda (e: 
A).(match e in A return (\lambda (_: A).A) with [(ASort _ _) \Rightarrow a1 | 
(AHead a4 _) \Rightarrow a4])) (AHead a1 a2) (AHead a0 (asucc g a3)) H1) in 
((let H3 \def (f_equal A A (\lambda (e: A).(match e in A return (\lambda (_: 
A).A) with [(ASort _ _) \Rightarrow a2 | (AHead _ a4) \Rightarrow a4])) 
(AHead a1 a2) (AHead a0 (asucc g a3)) H1) in (\lambda (H4: (eq A a1 a0)).(let 
H5 \def (eq_ind_r A a0 (\lambda (a4: A).((eq A (AHead a1 a2) (asucc g a4)) 
\to (ex2 A (\lambda (a5: A).(eq A a4 (AHead a1 a5))) (\lambda (a5: A).(eq A 
a2 (asucc g a5)))))) H a1 H4) in (eq_ind A a1 (\lambda (a4: A).(ex2 A 
(\lambda (a5: A).(eq A (AHead a4 a3) (AHead a1 a5))) (\lambda (a5: A).(eq A 
a2 (asucc g a5))))) (let H6 \def (eq_ind A a2 (\lambda (a4: A).((eq A (AHead 
a1 a4) (asucc g a3)) \to (ex2 A (\lambda (a5: A).(eq A a3 (AHead a1 a5))) 
(\lambda (a5: A).(eq A a4 (asucc g a5)))))) H0 (asucc g a3) H3) in (let H7 
\def (eq_ind A a2 (\lambda (a4: A).((eq A (AHead a1 a4) (asucc g a1)) \to 
(ex2 A (\lambda (a5: A).(eq A a1 (AHead a1 a5))) (\lambda (a5: A).(eq A a4 
(asucc g a5)))))) H5 (asucc g a3) H3) in (eq_ind_r A (asucc g a3) (\lambda 
(a4: A).(ex2 A (\lambda (a5: A).(eq A (AHead a1 a3) (AHead a1 a5))) (\lambda 
(a5: A).(eq A a4 (asucc g a5))))) (ex_intro2 A (\lambda (a4: A).(eq A (AHead 
a1 a3) (AHead a1 a4))) (\lambda (a4: A).(eq A (asucc g a3) (asucc g a4))) a3 
(refl_equal A (AHead a1 a3)) (refl_equal A (asucc g a3))) a2 H3))) a0 H4)))) 
H2))))))) a)))).
(* COMMENTS
Initial nodes: 957
END *)

