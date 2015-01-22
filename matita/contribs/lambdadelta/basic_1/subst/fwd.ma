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

include "Basic-1/subst/defs.ma".

theorem subst_sort:
 \forall (v: T).(\forall (d: nat).(\forall (k: nat).(eq T (subst d v (TSort 
k)) (TSort k))))
\def
 \lambda (_: T).(\lambda (_: nat).(\lambda (k: nat).(refl_equal T (TSort 
k)))).
(* COMMENTS
Initial nodes: 13
END *)

theorem subst_lref_lt:
 \forall (v: T).(\forall (d: nat).(\forall (i: nat).((lt i d) \to (eq T 
(subst d v (TLRef i)) (TLRef i)))))
\def
 \lambda (v: T).(\lambda (d: nat).(\lambda (i: nat).(\lambda (H: (lt i 
d)).(eq_ind_r bool true (\lambda (b: bool).(eq T (match b with [true 
\Rightarrow (TLRef i) | false \Rightarrow (match (blt d i) with [true 
\Rightarrow (TLRef (pred i)) | false \Rightarrow (lift d O v)])]) (TLRef i))) 
(refl_equal T (TLRef i)) (blt i d) (lt_blt d i H))))).
(* COMMENTS
Initial nodes: 73
END *)

theorem subst_lref_eq:
 \forall (v: T).(\forall (i: nat).(eq T (subst i v (TLRef i)) (lift i O v)))
\def
 \lambda (v: T).(\lambda (i: nat).(eq_ind_r bool false (\lambda (b: bool).(eq 
T (match b with [true \Rightarrow (TLRef i) | false \Rightarrow (match b with 
[true \Rightarrow (TLRef (pred i)) | false \Rightarrow (lift i O v)])]) (lift 
i O v))) (refl_equal T (lift i O v)) (blt i i) (le_bge i i (le_n i)))).
(* COMMENTS
Initial nodes: 71
END *)

theorem subst_lref_gt:
 \forall (v: T).(\forall (d: nat).(\forall (i: nat).((lt d i) \to (eq T 
(subst d v (TLRef i)) (TLRef (pred i))))))
\def
 \lambda (v: T).(\lambda (d: nat).(\lambda (i: nat).(\lambda (H: (lt d 
i)).(eq_ind_r bool false (\lambda (b: bool).(eq T (match b with [true 
\Rightarrow (TLRef i) | false \Rightarrow (match (blt d i) with [true 
\Rightarrow (TLRef (pred i)) | false \Rightarrow (lift d O v)])]) (TLRef 
(pred i)))) (eq_ind_r bool true (\lambda (b: bool).(eq T (match b with [true 
\Rightarrow (TLRef (pred i)) | false \Rightarrow (lift d O v)]) (TLRef (pred 
i)))) (refl_equal T (TLRef (pred i))) (blt d i) (lt_blt i d H)) (blt i d) 
(le_bge d i (lt_le_weak d i H)))))).
(* COMMENTS
Initial nodes: 130
END *)

theorem subst_head:
 \forall (k: K).(\forall (w: T).(\forall (u: T).(\forall (t: T).(\forall (d: 
nat).(eq T (subst d w (THead k u t)) (THead k (subst d w u) (subst (s k d) w 
t)))))))
\def
 \lambda (k: K).(\lambda (w: T).(\lambda (u: T).(\lambda (t: T).(\lambda (d: 
nat).(refl_equal T (THead k (subst d w u) (subst (s k d) w t))))))).
(* COMMENTS
Initial nodes: 37
END *)

