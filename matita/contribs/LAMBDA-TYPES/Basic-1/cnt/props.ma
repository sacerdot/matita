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

include "Basic-1/cnt/defs.ma".

include "Basic-1/lift/fwd.ma".

theorem cnt_lift:
 \forall (t: T).((cnt t) \to (\forall (i: nat).(\forall (d: nat).(cnt (lift i 
d t)))))
\def
 \lambda (t: T).(\lambda (H: (cnt t)).(cnt_ind (\lambda (t0: T).(\forall (i: 
nat).(\forall (d: nat).(cnt (lift i d t0))))) (\lambda (n: nat).(\lambda (i: 
nat).(\lambda (d: nat).(eq_ind_r T (TSort n) (\lambda (t0: T).(cnt t0)) 
(cnt_sort n) (lift i d (TSort n)) (lift_sort n i d))))) (\lambda (t0: 
T).(\lambda (_: (cnt t0)).(\lambda (H1: ((\forall (i: nat).(\forall (d: 
nat).(cnt (lift i d t0)))))).(\lambda (k: K).(\lambda (v: T).(\lambda (i: 
nat).(\lambda (d: nat).(eq_ind_r T (THead k (lift i d v) (lift i (s k d) t0)) 
(\lambda (t1: T).(cnt t1)) (cnt_head (lift i (s k d) t0) (H1 i (s k d)) k 
(lift i d v)) (lift i d (THead k v t0)) (lift_head k v t0 i d))))))))) t H)).
(* COMMENTS
Initial nodes: 191
END *)

