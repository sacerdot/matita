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

include "basic_1/T/defs.ma".

let rec T_rect (P: (T \to Type[0])) (f: (\forall (n: nat).(P (TSort n)))) 
(f0: (\forall (n: nat).(P (TLRef n)))) (f1: (\forall (k: K).(\forall (t: 
T).((P t) \to (\forall (t0: T).((P t0) \to (P (THead k t t0)))))))) (t: T) on 
t: P t \def match t in T with [(TSort n) \Rightarrow (f n) | (TLRef n) 
\Rightarrow (f0 n) | (THead k t0 t1) \Rightarrow (let TMP_2 \def ((T_rect P f 
f0 f1) t0) in (let TMP_1 \def ((T_rect P f f0 f1) t1) in (f1 k t0 TMP_2 t1 
TMP_1)))].

theorem T_ind:
 \forall (P: ((T \to Prop))).(((\forall (n: nat).(P (TSort n)))) \to 
(((\forall (n: nat).(P (TLRef n)))) \to (((\forall (k: K).(\forall (t: T).((P 
t) \to (\forall (t0: T).((P t0) \to (P (THead k t t0)))))))) \to (\forall (t: 
T).(P t)))))
\def
 \lambda (P: ((T \to Prop))).(T_rect P).

theorem thead_x_y_y:
 \forall (k: K).(\forall (v: T).(\forall (t: T).((eq T (THead k v t) t) \to 
(\forall (P: Prop).P))))
\def
 \lambda (k: K).(\lambda (v: T).(\lambda (t: T).(let TMP_676 \def (\lambda 
(t0: T).((eq T (THead k v t0) t0) \to (\forall (P: Prop).P))) in (let TMP_675 
\def (\lambda (n: nat).(\lambda (H: (eq T (THead k v (TSort n)) (TSort 
n))).(\lambda (P: Prop).(let TMP_673 \def (TSort n) in (let TMP_674 \def 
(THead k v TMP_673) in (let TMP_672 \def (\lambda (ee: T).(match ee in T with 
[(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | (THead _ _ _) 
\Rightarrow True])) in (let TMP_671 \def (TSort n) in (let H0 \def (eq_ind T 
TMP_674 TMP_672 I TMP_671 H) in (False_ind P H0))))))))) in (let TMP_670 \def 
(\lambda (n: nat).(\lambda (H: (eq T (THead k v (TLRef n)) (TLRef 
n))).(\lambda (P: Prop).(let TMP_668 \def (TLRef n) in (let TMP_669 \def 
(THead k v TMP_668) in (let TMP_667 \def (\lambda (ee: T).(match ee in T with 
[(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | (THead _ _ _) 
\Rightarrow True])) in (let TMP_666 \def (TLRef n) in (let H0 \def (eq_ind T 
TMP_669 TMP_667 I TMP_666 H) in (False_ind P H0))))))))) in (let TMP_665 \def 
(\lambda (k0: K).(\lambda (t0: T).(\lambda (_: (((eq T (THead k v t0) t0) \to 
(\forall (P: Prop).P)))).(\lambda (t1: T).(\lambda (H0: (((eq T (THead k v 
t1) t1) \to (\forall (P: Prop).P)))).(\lambda (H1: (eq T (THead k v (THead k0 
t0 t1)) (THead k0 t0 t1))).(\lambda (P: Prop).(let TMP_652 \def (\lambda (e: 
T).(match e in T with [(TSort _) \Rightarrow k | (TLRef _) \Rightarrow k | 
(THead k1 _ _) \Rightarrow k1])) in (let TMP_650 \def (THead k0 t0 t1) in 
(let TMP_651 \def (THead k v TMP_650) in (let TMP_649 \def (THead k0 t0 t1) 
in (let H2 \def (f_equal T K TMP_652 TMP_651 TMP_649 H1) in (let TMP_656 \def 
(\lambda (e: T).(match e in T with [(TSort _) \Rightarrow v | (TLRef _) 
\Rightarrow v | (THead _ t2 _) \Rightarrow t2])) in (let TMP_654 \def (THead 
k0 t0 t1) in (let TMP_655 \def (THead k v TMP_654) in (let TMP_653 \def 
(THead k0 t0 t1) in (let H3 \def (f_equal T T TMP_656 TMP_655 TMP_653 H1) in 
(let TMP_660 \def (\lambda (e: T).(match e in T with [(TSort _) \Rightarrow 
(THead k0 t0 t1) | (TLRef _) \Rightarrow (THead k0 t0 t1) | (THead _ _ t2) 
\Rightarrow t2])) in (let TMP_658 \def (THead k0 t0 t1) in (let TMP_659 \def 
(THead k v TMP_658) in (let TMP_657 \def (THead k0 t0 t1) in (let H4 \def 
(f_equal T T TMP_660 TMP_659 TMP_657 H1) in (let TMP_663 \def (\lambda (H5: 
(eq T v t0)).(\lambda (H6: (eq K k k0)).(let TMP_661 \def (\lambda (t2: 
T).((eq T (THead k t2 t1) t1) \to (\forall (P0: Prop).P0))) in (let H7 \def 
(eq_ind T v TMP_661 H0 t0 H5) in (let TMP_662 \def (\lambda (k1: K).((eq T 
(THead k1 t0 t1) t1) \to (\forall (P0: Prop).P0))) in (let H8 \def (eq_ind K 
k TMP_662 H7 k0 H6) in (H8 H4 P))))))) in (let TMP_664 \def (TMP_663 H3) in 
(TMP_664 H2))))))))))))))))))))))))) in (T_ind TMP_676 TMP_675 TMP_670 
TMP_665 t))))))).

