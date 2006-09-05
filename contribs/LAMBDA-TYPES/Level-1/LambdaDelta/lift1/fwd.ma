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

set "baseuri" "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/lift1/fwd".

include "lift1/defs.ma".

theorem lift1_lref:
 \forall (hds: PList).(\forall (i: nat).(eq T (lift1 hds (TLRef i)) (TLRef 
(trans hds i))))
\def
 \lambda (hds: PList).(PList_ind (\lambda (p: PList).(\forall (i: nat).(eq T 
(lift1 p (TLRef i)) (TLRef (trans p i))))) (\lambda (i: nat).(refl_equal T 
(TLRef (trans PNil i)))) (\lambda (h: nat).(\lambda (d: nat).(\lambda (p: 
PList).(\lambda (H: ((\forall (i: nat).(eq T (lift1 p (TLRef i)) (TLRef 
(trans p i)))))).(\lambda (i: nat).(eq_ind_r T (TLRef (trans p i)) (\lambda 
(t: T).(eq T (lift h d t) (TLRef (match (blt (trans p i) d) with [true 
\Rightarrow (trans p i) | false \Rightarrow (plus (trans p i) h)])))) 
(refl_equal T (TLRef (match (blt (trans p i) d) with [true \Rightarrow (trans 
p i) | false \Rightarrow (plus (trans p i) h)]))) (lift1 p (TLRef i)) (H 
i))))))) hds).

theorem lift1_bind:
 \forall (b: B).(\forall (hds: PList).(\forall (u: T).(\forall (t: T).(eq T 
(lift1 hds (THead (Bind b) u t)) (THead (Bind b) (lift1 hds u) (lift1 (Ss 
hds) t))))))
\def
 \lambda (b: B).(\lambda (hds: PList).(PList_ind (\lambda (p: PList).(\forall 
(u: T).(\forall (t: T).(eq T (lift1 p (THead (Bind b) u t)) (THead (Bind b) 
(lift1 p u) (lift1 (Ss p) t)))))) (\lambda (u: T).(\lambda (t: T).(refl_equal 
T (THead (Bind b) (lift1 PNil u) (lift1 (Ss PNil) t))))) (\lambda (h: 
nat).(\lambda (d: nat).(\lambda (p: PList).(\lambda (H: ((\forall (u: 
T).(\forall (t: T).(eq T (lift1 p (THead (Bind b) u t)) (THead (Bind b) 
(lift1 p u) (lift1 (Ss p) t))))))).(\lambda (u: T).(\lambda (t: T).(eq_ind_r 
T (THead (Bind b) (lift1 p u) (lift1 (Ss p) t)) (\lambda (t0: T).(eq T (lift 
h d t0) (THead (Bind b) (lift h d (lift1 p u)) (lift h (S d) (lift1 (Ss p) 
t))))) (eq_ind_r T (THead (Bind b) (lift h d (lift1 p u)) (lift h (S d) 
(lift1 (Ss p) t))) (\lambda (t0: T).(eq T t0 (THead (Bind b) (lift h d (lift1 
p u)) (lift h (S d) (lift1 (Ss p) t))))) (refl_equal T (THead (Bind b) (lift 
h d (lift1 p u)) (lift h (S d) (lift1 (Ss p) t)))) (lift h d (THead (Bind b) 
(lift1 p u) (lift1 (Ss p) t))) (lift_bind b (lift1 p u) (lift1 (Ss p) t) h 
d)) (lift1 p (THead (Bind b) u t)) (H u t)))))))) hds)).

theorem lift1_flat:
 \forall (f: F).(\forall (hds: PList).(\forall (u: T).(\forall (t: T).(eq T 
(lift1 hds (THead (Flat f) u t)) (THead (Flat f) (lift1 hds u) (lift1 hds 
t))))))
\def
 \lambda (f: F).(\lambda (hds: PList).(PList_ind (\lambda (p: PList).(\forall 
(u: T).(\forall (t: T).(eq T (lift1 p (THead (Flat f) u t)) (THead (Flat f) 
(lift1 p u) (lift1 p t)))))) (\lambda (u: T).(\lambda (t: T).(refl_equal T 
(THead (Flat f) (lift1 PNil u) (lift1 PNil t))))) (\lambda (h: nat).(\lambda 
(d: nat).(\lambda (p: PList).(\lambda (H: ((\forall (u: T).(\forall (t: 
T).(eq T (lift1 p (THead (Flat f) u t)) (THead (Flat f) (lift1 p u) (lift1 p 
t))))))).(\lambda (u: T).(\lambda (t: T).(eq_ind_r T (THead (Flat f) (lift1 p 
u) (lift1 p t)) (\lambda (t0: T).(eq T (lift h d t0) (THead (Flat f) (lift h 
d (lift1 p u)) (lift h d (lift1 p t))))) (eq_ind_r T (THead (Flat f) (lift h 
d (lift1 p u)) (lift h d (lift1 p t))) (\lambda (t0: T).(eq T t0 (THead (Flat 
f) (lift h d (lift1 p u)) (lift h d (lift1 p t))))) (refl_equal T (THead 
(Flat f) (lift h d (lift1 p u)) (lift h d (lift1 p t)))) (lift h d (THead 
(Flat f) (lift1 p u) (lift1 p t))) (lift_flat f (lift1 p u) (lift1 p t) h d)) 
(lift1 p (THead (Flat f) u t)) (H u t)))))))) hds)).

theorem lift1_cons_tail:
 \forall (t: T).(\forall (h: nat).(\forall (d: nat).(\forall (hds: PList).(eq 
T (lift1 (PConsTail hds h d) t) (lift1 hds (lift h d t))))))
\def
 \lambda (t: T).(\lambda (h: nat).(\lambda (d: nat).(\lambda (hds: 
PList).(PList_ind (\lambda (p: PList).(eq T (lift1 (PConsTail p h d) t) 
(lift1 p (lift h d t)))) (refl_equal T (lift h d t)) (\lambda (n: 
nat).(\lambda (n0: nat).(\lambda (p: PList).(\lambda (H: (eq T (lift1 
(PConsTail p h d) t) (lift1 p (lift h d t)))).(eq_ind_r T (lift1 p (lift h d 
t)) (\lambda (t0: T).(eq T (lift n n0 t0) (lift n n0 (lift1 p (lift h d 
t))))) (refl_equal T (lift n n0 (lift1 p (lift h d t)))) (lift1 (PConsTail p 
h d) t) H))))) hds)))).

theorem lifts1_flat:
 \forall (f: F).(\forall (hds: PList).(\forall (t: T).(\forall (ts: 
TList).(eq T (lift1 hds (THeads (Flat f) ts t)) (THeads (Flat f) (lifts1 hds 
ts) (lift1 hds t))))))
\def
 \lambda (f: F).(\lambda (hds: PList).(\lambda (t: T).(\lambda (ts: 
TList).(TList_ind (\lambda (t0: TList).(eq T (lift1 hds (THeads (Flat f) t0 
t)) (THeads (Flat f) (lifts1 hds t0) (lift1 hds t)))) (refl_equal T (lift1 
hds t)) (\lambda (t0: T).(\lambda (t1: TList).(\lambda (H: (eq T (lift1 hds 
(THeads (Flat f) t1 t)) (THeads (Flat f) (lifts1 hds t1) (lift1 hds 
t)))).(eq_ind_r T (THead (Flat f) (lift1 hds t0) (lift1 hds (THeads (Flat f) 
t1 t))) (\lambda (t2: T).(eq T t2 (THead (Flat f) (lift1 hds t0) (THeads 
(Flat f) (lifts1 hds t1) (lift1 hds t))))) (eq_ind_r T (THeads (Flat f) 
(lifts1 hds t1) (lift1 hds t)) (\lambda (t2: T).(eq T (THead (Flat f) (lift1 
hds t0) t2) (THead (Flat f) (lift1 hds t0) (THeads (Flat f) (lifts1 hds t1) 
(lift1 hds t))))) (refl_equal T (THead (Flat f) (lift1 hds t0) (THeads (Flat 
f) (lifts1 hds t1) (lift1 hds t)))) (lift1 hds (THeads (Flat f) t1 t)) H) 
(lift1 hds (THead (Flat f) t0 (THeads (Flat f) t1 t))) (lift1_flat f hds t0 
(THeads (Flat f) t1 t)))))) ts)))).

theorem lifts1_nil:
 \forall (ts: TList).(eq TList (lifts1 PNil ts) ts)
\def
 \lambda (ts: TList).(TList_ind (\lambda (t: TList).(eq TList (lifts1 PNil t) 
t)) (refl_equal TList TNil) (\lambda (t: T).(\lambda (t0: TList).(\lambda (H: 
(eq TList (lifts1 PNil t0) t0)).(eq_ind_r TList t0 (\lambda (t1: TList).(eq 
TList (TCons t t1) (TCons t t0))) (refl_equal TList (TCons t t0)) (lifts1 
PNil t0) H)))) ts).

theorem lifts1_cons:
 \forall (h: nat).(\forall (d: nat).(\forall (hds: PList).(\forall (ts: 
TList).(eq TList (lifts1 (PCons h d hds) ts) (lifts h d (lifts1 hds ts))))))
\def
 \lambda (h: nat).(\lambda (d: nat).(\lambda (hds: PList).(\lambda (ts: 
TList).(TList_ind (\lambda (t: TList).(eq TList (lifts1 (PCons h d hds) t) 
(lifts h d (lifts1 hds t)))) (refl_equal TList TNil) (\lambda (t: T).(\lambda 
(t0: TList).(\lambda (H: (eq TList (lifts1 (PCons h d hds) t0) (lifts h d 
(lifts1 hds t0)))).(eq_ind_r TList (lifts h d (lifts1 hds t0)) (\lambda (t1: 
TList).(eq TList (TCons (lift h d (lift1 hds t)) t1) (TCons (lift h d (lift1 
hds t)) (lifts h d (lifts1 hds t0))))) (refl_equal TList (TCons (lift h d 
(lift1 hds t)) (lifts h d (lifts1 hds t0)))) (lifts1 (PCons h d hds) t0) 
H)))) ts)))).

