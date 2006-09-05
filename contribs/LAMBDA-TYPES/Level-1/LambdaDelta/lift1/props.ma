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

set "baseuri" "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/lift1/props".

include "lift1/defs.ma".

theorem lift1_xhg:
 \forall (hds: PList).(\forall (t: T).(eq T (lift1 (Ss hds) (lift (S O) O t)) 
(lift (S O) O (lift1 hds t))))
\def
 \lambda (hds: PList).(PList_ind (\lambda (p: PList).(\forall (t: T).(eq T 
(lift1 (Ss p) (lift (S O) O t)) (lift (S O) O (lift1 p t))))) (\lambda (t: 
T).(refl_equal T (lift (S O) O t))) (\lambda (h: nat).(\lambda (d: 
nat).(\lambda (p: PList).(\lambda (H: ((\forall (t: T).(eq T (lift1 (Ss p) 
(lift (S O) O t)) (lift (S O) O (lift1 p t)))))).(\lambda (t: T).(eq_ind_r T 
(lift (S O) O (lift1 p t)) (\lambda (t0: T).(eq T (lift h (S d) t0) (lift (S 
O) O (lift h d (lift1 p t))))) (eq_ind nat (plus (S O) d) (\lambda (n: 
nat).(eq T (lift h n (lift (S O) O (lift1 p t))) (lift (S O) O (lift h d 
(lift1 p t))))) (eq_ind_r T (lift (S O) O (lift h d (lift1 p t))) (\lambda 
(t0: T).(eq T t0 (lift (S O) O (lift h d (lift1 p t))))) (refl_equal T (lift 
(S O) O (lift h d (lift1 p t)))) (lift h (plus (S O) d) (lift (S O) O (lift1 
p t))) (lift_d (lift1 p t) h (S O) d O (le_O_n d))) (S d) (refl_equal nat (S 
d))) (lift1 (Ss p) (lift (S O) O t)) (H t))))))) hds).

theorem lifts1_xhg:
 \forall (hds: PList).(\forall (ts: TList).(eq TList (lifts1 (Ss hds) (lifts 
(S O) O ts)) (lifts (S O) O (lifts1 hds ts))))
\def
 \lambda (hds: PList).(\lambda (ts: TList).(TList_ind (\lambda (t: TList).(eq 
TList (lifts1 (Ss hds) (lifts (S O) O t)) (lifts (S O) O (lifts1 hds t)))) 
(refl_equal TList TNil) (\lambda (t: T).(\lambda (t0: TList).(\lambda (H: (eq 
TList (lifts1 (Ss hds) (lifts (S O) O t0)) (lifts (S O) O (lifts1 hds 
t0)))).(eq_ind_r T (lift (S O) O (lift1 hds t)) (\lambda (t1: T).(eq TList 
(TCons t1 (lifts1 (Ss hds) (lifts (S O) O t0))) (TCons (lift (S O) O (lift1 
hds t)) (lifts (S O) O (lifts1 hds t0))))) (eq_ind_r TList (lifts (S O) O 
(lifts1 hds t0)) (\lambda (t1: TList).(eq TList (TCons (lift (S O) O (lift1 
hds t)) t1) (TCons (lift (S O) O (lift1 hds t)) (lifts (S O) O (lifts1 hds 
t0))))) (refl_equal TList (TCons (lift (S O) O (lift1 hds t)) (lifts (S O) O 
(lifts1 hds t0)))) (lifts1 (Ss hds) (lifts (S O) O t0)) H) (lift1 (Ss hds) 
(lift (S O) O t)) (lift1_xhg hds t))))) ts)).

