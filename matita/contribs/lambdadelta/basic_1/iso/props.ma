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

include "Basic-1/iso/fwd.ma".

theorem iso_refl:
 \forall (t: T).(iso t t)
\def
 \lambda (t: T).(T_ind (\lambda (t0: T).(iso t0 t0)) (\lambda (n: 
nat).(iso_sort n n)) (\lambda (n: nat).(iso_lref n n)) (\lambda (k: 
K).(\lambda (t0: T).(\lambda (_: (iso t0 t0)).(\lambda (t1: T).(\lambda (_: 
(iso t1 t1)).(iso_head t0 t0 t1 t1 k)))))) t).
(* COMMENTS
Initial nodes: 59
END *)

theorem iso_trans:
 \forall (t1: T).(\forall (t2: T).((iso t1 t2) \to (\forall (t3: T).((iso t2 
t3) \to (iso t1 t3)))))
\def
 \lambda (t1: T).(\lambda (t2: T).(\lambda (H: (iso t1 t2)).(iso_ind (\lambda 
(t: T).(\lambda (t0: T).(\forall (t3: T).((iso t0 t3) \to (iso t t3))))) 
(\lambda (n1: nat).(\lambda (n2: nat).(\lambda (t3: T).(\lambda (H0: (iso 
(TSort n2) t3)).(let H_x \def (iso_gen_sort t3 n2 H0) in (let H1 \def H_x in 
(ex_ind nat (\lambda (n3: nat).(eq T t3 (TSort n3))) (iso (TSort n1) t3) 
(\lambda (x: nat).(\lambda (H2: (eq T t3 (TSort x))).(eq_ind_r T (TSort x) 
(\lambda (t: T).(iso (TSort n1) t)) (iso_sort n1 x) t3 H2))) H1))))))) 
(\lambda (i1: nat).(\lambda (i2: nat).(\lambda (t3: T).(\lambda (H0: (iso 
(TLRef i2) t3)).(let H_x \def (iso_gen_lref t3 i2 H0) in (let H1 \def H_x in 
(ex_ind nat (\lambda (n2: nat).(eq T t3 (TLRef n2))) (iso (TLRef i1) t3) 
(\lambda (x: nat).(\lambda (H2: (eq T t3 (TLRef x))).(eq_ind_r T (TLRef x) 
(\lambda (t: T).(iso (TLRef i1) t)) (iso_lref i1 x) t3 H2))) H1))))))) 
(\lambda (v1: T).(\lambda (v2: T).(\lambda (t3: T).(\lambda (t4: T).(\lambda 
(k: K).(\lambda (t5: T).(\lambda (H0: (iso (THead k v2 t4) t5)).(let H_x \def 
(iso_gen_head k v2 t4 t5 H0) in (let H1 \def H_x in (ex_2_ind T T (\lambda 
(v3: T).(\lambda (t6: T).(eq T t5 (THead k v3 t6)))) (iso (THead k v1 t3) t5) 
(\lambda (x0: T).(\lambda (x1: T).(\lambda (H2: (eq T t5 (THead k x0 
x1))).(eq_ind_r T (THead k x0 x1) (\lambda (t: T).(iso (THead k v1 t3) t)) 
(iso_head v1 x0 t3 x1 k) t5 H2)))) H1)))))))))) t1 t2 H))).
(* COMMENTS
Initial nodes: 351
END *)

