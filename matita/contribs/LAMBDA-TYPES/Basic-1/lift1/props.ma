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

include "Basic-1/lift/props.ma".

include "Basic-1/drop1/defs.ma".

theorem lift1_lift1:
 \forall (is1: PList).(\forall (is2: PList).(\forall (t: T).(eq T (lift1 is1 
(lift1 is2 t)) (lift1 (papp is1 is2) t))))
\def
 \lambda (is1: PList).(PList_ind (\lambda (p: PList).(\forall (is2: 
PList).(\forall (t: T).(eq T (lift1 p (lift1 is2 t)) (lift1 (papp p is2) 
t))))) (\lambda (is2: PList).(\lambda (t: T).(refl_equal T (lift1 is2 t)))) 
(\lambda (n: nat).(\lambda (n0: nat).(\lambda (p: PList).(\lambda (H: 
((\forall (is2: PList).(\forall (t: T).(eq T (lift1 p (lift1 is2 t)) (lift1 
(papp p is2) t)))))).(\lambda (is2: PList).(\lambda (t: T).(f_equal3 nat nat 
T T lift n n n0 n0 (lift1 p (lift1 is2 t)) (lift1 (papp p is2) t) (refl_equal 
nat n) (refl_equal nat n0) (H is2 t)))))))) is1).
(* COMMENTS
Initial nodes: 145
END *)

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
(* COMMENTS
Initial nodes: 371
END *)

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
(* COMMENTS
Initial nodes: 307
END *)

theorem lift1_free:
 \forall (hds: PList).(\forall (i: nat).(\forall (t: T).(eq T (lift1 hds 
(lift (S i) O t)) (lift (S (trans hds i)) O (lift1 (ptrans hds i) t)))))
\def
 \lambda (hds: PList).(PList_ind (\lambda (p: PList).(\forall (i: 
nat).(\forall (t: T).(eq T (lift1 p (lift (S i) O t)) (lift (S (trans p i)) O 
(lift1 (ptrans p i) t)))))) (\lambda (i: nat).(\lambda (t: T).(refl_equal T 
(lift (S i) O t)))) (\lambda (h: nat).(\lambda (d: nat).(\lambda (hds0: 
PList).(\lambda (H: ((\forall (i: nat).(\forall (t: T).(eq T (lift1 hds0 
(lift (S i) O t)) (lift (S (trans hds0 i)) O (lift1 (ptrans hds0 i) 
t))))))).(\lambda (i: nat).(\lambda (t: T).(eq_ind_r T (lift (S (trans hds0 
i)) O (lift1 (ptrans hds0 i) t)) (\lambda (t0: T).(eq T (lift h d t0) (lift 
(S (match (blt (trans hds0 i) d) with [true \Rightarrow (trans hds0 i) | 
false \Rightarrow (plus (trans hds0 i) h)])) O (lift1 (match (blt (trans hds0 
i) d) with [true \Rightarrow (PCons h (minus d (S (trans hds0 i))) (ptrans 
hds0 i)) | false \Rightarrow (ptrans hds0 i)]) t)))) (xinduction bool (blt 
(trans hds0 i) d) (\lambda (b: bool).(eq T (lift h d (lift (S (trans hds0 i)) 
O (lift1 (ptrans hds0 i) t))) (lift (S (match b with [true \Rightarrow (trans 
hds0 i) | false \Rightarrow (plus (trans hds0 i) h)])) O (lift1 (match b with 
[true \Rightarrow (PCons h (minus d (S (trans hds0 i))) (ptrans hds0 i)) | 
false \Rightarrow (ptrans hds0 i)]) t)))) (\lambda (x_x: bool).(bool_ind 
(\lambda (b: bool).((eq bool (blt (trans hds0 i) d) b) \to (eq T (lift h d 
(lift (S (trans hds0 i)) O (lift1 (ptrans hds0 i) t))) (lift (S (match b with 
[true \Rightarrow (trans hds0 i) | false \Rightarrow (plus (trans hds0 i) 
h)])) O (lift1 (match b with [true \Rightarrow (PCons h (minus d (S (trans 
hds0 i))) (ptrans hds0 i)) | false \Rightarrow (ptrans hds0 i)]) t))))) 
(\lambda (H0: (eq bool (blt (trans hds0 i) d) true)).(eq_ind_r nat (plus (S 
(trans hds0 i)) (minus d (S (trans hds0 i)))) (\lambda (n: nat).(eq T (lift h 
n (lift (S (trans hds0 i)) O (lift1 (ptrans hds0 i) t))) (lift (S (trans hds0 
i)) O (lift1 (PCons h (minus d (S (trans hds0 i))) (ptrans hds0 i)) t)))) 
(eq_ind_r T (lift (S (trans hds0 i)) O (lift h (minus d (S (trans hds0 i))) 
(lift1 (ptrans hds0 i) t))) (\lambda (t0: T).(eq T t0 (lift (S (trans hds0 
i)) O (lift1 (PCons h (minus d (S (trans hds0 i))) (ptrans hds0 i)) t)))) 
(refl_equal T (lift (S (trans hds0 i)) O (lift1 (PCons h (minus d (S (trans 
hds0 i))) (ptrans hds0 i)) t))) (lift h (plus (S (trans hds0 i)) (minus d (S 
(trans hds0 i)))) (lift (S (trans hds0 i)) O (lift1 (ptrans hds0 i) t))) 
(lift_d (lift1 (ptrans hds0 i) t) h (S (trans hds0 i)) (minus d (S (trans 
hds0 i))) O (le_O_n (minus d (S (trans hds0 i)))))) d (le_plus_minus (S 
(trans hds0 i)) d (bge_le (S (trans hds0 i)) d (le_bge (S (trans hds0 i)) d 
(lt_le_S (trans hds0 i) d (blt_lt d (trans hds0 i) H0))))))) (\lambda (H0: 
(eq bool (blt (trans hds0 i) d) false)).(eq_ind_r T (lift (plus h (S (trans 
hds0 i))) O (lift1 (ptrans hds0 i) t)) (\lambda (t0: T).(eq T t0 (lift (S 
(plus (trans hds0 i) h)) O (lift1 (ptrans hds0 i) t)))) (eq_ind nat (S (plus 
h (trans hds0 i))) (\lambda (n: nat).(eq T (lift n O (lift1 (ptrans hds0 i) 
t)) (lift (S (plus (trans hds0 i) h)) O (lift1 (ptrans hds0 i) t)))) 
(eq_ind_r nat (plus (trans hds0 i) h) (\lambda (n: nat).(eq T (lift (S n) O 
(lift1 (ptrans hds0 i) t)) (lift (S (plus (trans hds0 i) h)) O (lift1 (ptrans 
hds0 i) t)))) (refl_equal T (lift (S (plus (trans hds0 i) h)) O (lift1 
(ptrans hds0 i) t))) (plus h (trans hds0 i)) (plus_sym h (trans hds0 i))) 
(plus h (S (trans hds0 i))) (plus_n_Sm h (trans hds0 i))) (lift h d (lift (S 
(trans hds0 i)) O (lift1 (ptrans hds0 i) t))) (lift_free (lift1 (ptrans hds0 
i) t) (S (trans hds0 i)) h O d (eq_ind nat (S (plus O (trans hds0 i))) 
(\lambda (n: nat).(le d n)) (eq_ind_r nat (plus (trans hds0 i) O) (\lambda 
(n: nat).(le d (S n))) (le_S d (plus (trans hds0 i) O) (le_plus_trans d 
(trans hds0 i) O (bge_le d (trans hds0 i) H0))) (plus O (trans hds0 i)) 
(plus_sym O (trans hds0 i))) (plus O (S (trans hds0 i))) (plus_n_Sm O (trans 
hds0 i))) (le_O_n d)))) x_x))) (lift1 hds0 (lift (S i) O t)) (H i t)))))))) 
hds).
(* COMMENTS
Initial nodes: 1339
END *)

