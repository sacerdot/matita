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

include "basic_1/T/fwd.ma".

include "basic_1/iso/fwd.ma".

theorem iso_refl:
 \forall (t: T).(iso t t)
\def
 \lambda (t: T).(let TMP_1 \def (\lambda (t0: T).(iso t0 t0)) in (let TMP_2 
\def (\lambda (n: nat).(iso_sort n n)) in (let TMP_3 \def (\lambda (n: 
nat).(iso_lref n n)) in (let TMP_4 \def (\lambda (k: K).(\lambda (t0: 
T).(\lambda (_: (iso t0 t0)).(\lambda (t1: T).(\lambda (_: (iso t1 
t1)).(iso_head t0 t0 t1 t1 k)))))) in (T_ind TMP_1 TMP_2 TMP_3 TMP_4 t))))).

theorem iso_trans:
 \forall (t1: T).(\forall (t2: T).((iso t1 t2) \to (\forall (t3: T).((iso t2 
t3) \to (iso t1 t3)))))
\def
 \lambda (t1: T).(\lambda (t2: T).(\lambda (H: (iso t1 t2)).(let TMP_1 \def 
(\lambda (t: T).(\lambda (t0: T).(\forall (t3: T).((iso t0 t3) \to (iso t 
t3))))) in (let TMP_11 \def (\lambda (n1: nat).(\lambda (n2: nat).(\lambda 
(t3: T).(\lambda (H0: (iso (TSort n2) t3)).(let H_x \def (iso_gen_sort t3 n2 
H0) in (let H1 \def H_x in (let TMP_3 \def (\lambda (n3: nat).(let TMP_2 \def 
(TSort n3) in (eq T t3 TMP_2))) in (let TMP_4 \def (TSort n1) in (let TMP_5 
\def (iso TMP_4 t3) in (let TMP_10 \def (\lambda (x: nat).(\lambda (H2: (eq T 
t3 (TSort x))).(let TMP_6 \def (TSort x) in (let TMP_8 \def (\lambda (t: 
T).(let TMP_7 \def (TSort n1) in (iso TMP_7 t))) in (let TMP_9 \def (iso_sort 
n1 x) in (eq_ind_r T TMP_6 TMP_8 TMP_9 t3 H2)))))) in (ex_ind nat TMP_3 TMP_5 
TMP_10 H1))))))))))) in (let TMP_21 \def (\lambda (i1: nat).(\lambda (i2: 
nat).(\lambda (t3: T).(\lambda (H0: (iso (TLRef i2) t3)).(let H_x \def 
(iso_gen_lref t3 i2 H0) in (let H1 \def H_x in (let TMP_13 \def (\lambda (n2: 
nat).(let TMP_12 \def (TLRef n2) in (eq T t3 TMP_12))) in (let TMP_14 \def 
(TLRef i1) in (let TMP_15 \def (iso TMP_14 t3) in (let TMP_20 \def (\lambda 
(x: nat).(\lambda (H2: (eq T t3 (TLRef x))).(let TMP_16 \def (TLRef x) in 
(let TMP_18 \def (\lambda (t: T).(let TMP_17 \def (TLRef i1) in (iso TMP_17 
t))) in (let TMP_19 \def (iso_lref i1 x) in (eq_ind_r T TMP_16 TMP_18 TMP_19 
t3 H2)))))) in (ex_ind nat TMP_13 TMP_15 TMP_20 H1))))))))))) in (let TMP_31 
\def (\lambda (v1: T).(\lambda (v2: T).(\lambda (t3: T).(\lambda (t4: 
T).(\lambda (k: K).(\lambda (t5: T).(\lambda (H0: (iso (THead k v2 t4) 
t5)).(let H_x \def (iso_gen_head k v2 t4 t5 H0) in (let H1 \def H_x in (let 
TMP_23 \def (\lambda (v3: T).(\lambda (t6: T).(let TMP_22 \def (THead k v3 
t6) in (eq T t5 TMP_22)))) in (let TMP_24 \def (THead k v1 t3) in (let TMP_25 
\def (iso TMP_24 t5) in (let TMP_30 \def (\lambda (x0: T).(\lambda (x1: 
T).(\lambda (H2: (eq T t5 (THead k x0 x1))).(let TMP_26 \def (THead k x0 x1) 
in (let TMP_28 \def (\lambda (t: T).(let TMP_27 \def (THead k v1 t3) in (iso 
TMP_27 t))) in (let TMP_29 \def (iso_head v1 x0 t3 x1 k) in (eq_ind_r T 
TMP_26 TMP_28 TMP_29 t5 H2))))))) in (ex_2_ind T T TMP_23 TMP_25 TMP_30 
H1)))))))))))))) in (iso_ind TMP_1 TMP_11 TMP_21 TMP_31 t1 t2 H))))))).

