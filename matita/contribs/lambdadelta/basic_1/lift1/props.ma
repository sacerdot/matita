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

include "basic_1/lift1/defs.ma".

include "basic_1/lift/props.ma".

theorem lift1_sort:
 \forall (n: nat).(\forall (is: PList).(eq T (lift1 is (TSort n)) (TSort n)))
\def
 \lambda (n: nat).(\lambda (is: PList).(let TMP_4 \def (\lambda (p: 
PList).(let TMP_1 \def (TSort n) in (let TMP_2 \def (lift1 p TMP_1) in (let 
TMP_3 \def (TSort n) in (eq T TMP_2 TMP_3))))) in (let TMP_5 \def (TSort n) 
in (let TMP_6 \def (refl_equal T TMP_5) in (let TMP_15 \def (\lambda (n0: 
nat).(\lambda (n1: nat).(\lambda (p: PList).(\lambda (H: (eq T (lift1 p 
(TSort n)) (TSort n))).(let TMP_7 \def (TSort n) in (let TMP_10 \def (\lambda 
(t: T).(let TMP_8 \def (lift n0 n1 t) in (let TMP_9 \def (TSort n) in (eq T 
TMP_8 TMP_9)))) in (let TMP_11 \def (TSort n) in (let TMP_12 \def (refl_equal 
T TMP_11) in (let TMP_13 \def (TSort n) in (let TMP_14 \def (lift1 p TMP_13) 
in (eq_ind_r T TMP_7 TMP_10 TMP_12 TMP_14 H))))))))))) in (PList_ind TMP_4 
TMP_6 TMP_15 is)))))).

theorem lift1_lref:
 \forall (hds: PList).(\forall (i: nat).(eq T (lift1 hds (TLRef i)) (TLRef 
(trans hds i))))
\def
 \lambda (hds: PList).(let TMP_5 \def (\lambda (p: PList).(\forall (i: 
nat).(let TMP_1 \def (TLRef i) in (let TMP_2 \def (lift1 p TMP_1) in (let 
TMP_3 \def (trans p i) in (let TMP_4 \def (TLRef TMP_3) in (eq T TMP_2 
TMP_4))))))) in (let TMP_7 \def (\lambda (i: nat).(let TMP_6 \def (TLRef i) 
in (refl_equal T TMP_6))) in (let TMP_26 \def (\lambda (n: nat).(\lambda (n0: 
nat).(\lambda (p: PList).(\lambda (H: ((\forall (i: nat).(eq T (lift1 p 
(TLRef i)) (TLRef (trans p i)))))).(\lambda (i: nat).(let TMP_8 \def (trans p 
i) in (let TMP_9 \def (TLRef TMP_8) in (let TMP_16 \def (\lambda (t: T).(let 
TMP_10 \def (lift n n0 t) in (let TMP_11 \def (trans p i) in (let TMP_12 \def 
(blt TMP_11 n0) in (let TMP_14 \def (match TMP_12 with [true \Rightarrow 
(trans p i) | false \Rightarrow (let TMP_13 \def (trans p i) in (plus TMP_13 
n))]) in (let TMP_15 \def (TLRef TMP_14) in (eq T TMP_10 TMP_15))))))) in 
(let TMP_17 \def (trans p i) in (let TMP_18 \def (blt TMP_17 n0) in (let 
TMP_20 \def (match TMP_18 with [true \Rightarrow (trans p i) | false 
\Rightarrow (let TMP_19 \def (trans p i) in (plus TMP_19 n))]) in (let TMP_21 
\def (TLRef TMP_20) in (let TMP_22 \def (refl_equal T TMP_21) in (let TMP_23 
\def (TLRef i) in (let TMP_24 \def (lift1 p TMP_23) in (let TMP_25 \def (H i) 
in (eq_ind_r T TMP_9 TMP_16 TMP_22 TMP_24 TMP_25))))))))))))))))) in 
(PList_ind TMP_5 TMP_7 TMP_26 hds)))).

theorem lift1_bind:
 \forall (b: B).(\forall (hds: PList).(\forall (u: T).(\forall (t: T).(eq T 
(lift1 hds (THead (Bind b) u t)) (THead (Bind b) (lift1 hds u) (lift1 (Ss 
hds) t))))))
\def
 \lambda (b: B).(\lambda (hds: PList).(let TMP_9 \def (\lambda (p: 
PList).(\forall (u: T).(\forall (t: T).(let TMP_1 \def (Bind b) in (let TMP_2 
\def (THead TMP_1 u t) in (let TMP_3 \def (lift1 p TMP_2) in (let TMP_4 \def 
(Bind b) in (let TMP_5 \def (lift1 p u) in (let TMP_6 \def (Ss p) in (let 
TMP_7 \def (lift1 TMP_6 t) in (let TMP_8 \def (THead TMP_4 TMP_5 TMP_7) in 
(eq T TMP_3 TMP_8)))))))))))) in (let TMP_12 \def (\lambda (u: T).(\lambda 
(t: T).(let TMP_10 \def (Bind b) in (let TMP_11 \def (THead TMP_10 u t) in 
(refl_equal T TMP_11))))) in (let TMP_69 \def (\lambda (n: nat).(\lambda (n0: 
nat).(\lambda (p: PList).(\lambda (H: ((\forall (u: T).(\forall (t: T).(eq T 
(lift1 p (THead (Bind b) u t)) (THead (Bind b) (lift1 p u) (lift1 (Ss p) 
t))))))).(\lambda (u: T).(\lambda (t: T).(let TMP_13 \def (Bind b) in (let 
TMP_14 \def (lift1 p u) in (let TMP_15 \def (Ss p) in (let TMP_16 \def (lift1 
TMP_15 t) in (let TMP_17 \def (THead TMP_13 TMP_14 TMP_16) in (let TMP_27 
\def (\lambda (t0: T).(let TMP_18 \def (lift n n0 t0) in (let TMP_19 \def 
(Bind b) in (let TMP_20 \def (lift1 p u) in (let TMP_21 \def (lift n n0 
TMP_20) in (let TMP_22 \def (S n0) in (let TMP_23 \def (Ss p) in (let TMP_24 
\def (lift1 TMP_23 t) in (let TMP_25 \def (lift n TMP_22 TMP_24) in (let 
TMP_26 \def (THead TMP_19 TMP_21 TMP_25) in (eq T TMP_18 TMP_26))))))))))) in 
(let TMP_28 \def (Bind b) in (let TMP_29 \def (lift1 p u) in (let TMP_30 \def 
(lift n n0 TMP_29) in (let TMP_31 \def (S n0) in (let TMP_32 \def (Ss p) in 
(let TMP_33 \def (lift1 TMP_32 t) in (let TMP_34 \def (lift n TMP_31 TMP_33) 
in (let TMP_35 \def (THead TMP_28 TMP_30 TMP_34) in (let TMP_44 \def (\lambda 
(t0: T).(let TMP_36 \def (Bind b) in (let TMP_37 \def (lift1 p u) in (let 
TMP_38 \def (lift n n0 TMP_37) in (let TMP_39 \def (S n0) in (let TMP_40 \def 
(Ss p) in (let TMP_41 \def (lift1 TMP_40 t) in (let TMP_42 \def (lift n 
TMP_39 TMP_41) in (let TMP_43 \def (THead TMP_36 TMP_38 TMP_42) in (eq T t0 
TMP_43)))))))))) in (let TMP_45 \def (Bind b) in (let TMP_46 \def (lift1 p u) 
in (let TMP_47 \def (lift n n0 TMP_46) in (let TMP_48 \def (S n0) in (let 
TMP_49 \def (Ss p) in (let TMP_50 \def (lift1 TMP_49 t) in (let TMP_51 \def 
(lift n TMP_48 TMP_50) in (let TMP_52 \def (THead TMP_45 TMP_47 TMP_51) in 
(let TMP_53 \def (refl_equal T TMP_52) in (let TMP_54 \def (Bind b) in (let 
TMP_55 \def (lift1 p u) in (let TMP_56 \def (Ss p) in (let TMP_57 \def (lift1 
TMP_56 t) in (let TMP_58 \def (THead TMP_54 TMP_55 TMP_57) in (let TMP_59 
\def (lift n n0 TMP_58) in (let TMP_60 \def (lift1 p u) in (let TMP_61 \def 
(Ss p) in (let TMP_62 \def (lift1 TMP_61 t) in (let TMP_63 \def (lift_bind b 
TMP_60 TMP_62 n n0) in (let TMP_64 \def (eq_ind_r T TMP_35 TMP_44 TMP_53 
TMP_59 TMP_63) in (let TMP_65 \def (Bind b) in (let TMP_66 \def (THead TMP_65 
u t) in (let TMP_67 \def (lift1 p TMP_66) in (let TMP_68 \def (H u t) in 
(eq_ind_r T TMP_17 TMP_27 TMP_64 TMP_67 
TMP_68)))))))))))))))))))))))))))))))))))))))))))))) in (PList_ind TMP_9 
TMP_12 TMP_69 hds))))).

theorem lift1_flat:
 \forall (f: F).(\forall (hds: PList).(\forall (u: T).(\forall (t: T).(eq T 
(lift1 hds (THead (Flat f) u t)) (THead (Flat f) (lift1 hds u) (lift1 hds 
t))))))
\def
 \lambda (f: F).(\lambda (hds: PList).(let TMP_8 \def (\lambda (p: 
PList).(\forall (u: T).(\forall (t: T).(let TMP_1 \def (Flat f) in (let TMP_2 
\def (THead TMP_1 u t) in (let TMP_3 \def (lift1 p TMP_2) in (let TMP_4 \def 
(Flat f) in (let TMP_5 \def (lift1 p u) in (let TMP_6 \def (lift1 p t) in 
(let TMP_7 \def (THead TMP_4 TMP_5 TMP_6) in (eq T TMP_3 TMP_7))))))))))) in 
(let TMP_11 \def (\lambda (u: T).(\lambda (t: T).(let TMP_9 \def (Flat f) in 
(let TMP_10 \def (THead TMP_9 u t) in (refl_equal T TMP_10))))) in (let 
TMP_57 \def (\lambda (n: nat).(\lambda (n0: nat).(\lambda (p: PList).(\lambda 
(H: ((\forall (u: T).(\forall (t: T).(eq T (lift1 p (THead (Flat f) u t)) 
(THead (Flat f) (lift1 p u) (lift1 p t))))))).(\lambda (u: T).(\lambda (t: 
T).(let TMP_12 \def (Flat f) in (let TMP_13 \def (lift1 p u) in (let TMP_14 
\def (lift1 p t) in (let TMP_15 \def (THead TMP_12 TMP_13 TMP_14) in (let 
TMP_23 \def (\lambda (t0: T).(let TMP_16 \def (lift n n0 t0) in (let TMP_17 
\def (Flat f) in (let TMP_18 \def (lift1 p u) in (let TMP_19 \def (lift n n0 
TMP_18) in (let TMP_20 \def (lift1 p t) in (let TMP_21 \def (lift n n0 
TMP_20) in (let TMP_22 \def (THead TMP_17 TMP_19 TMP_21) in (eq T TMP_16 
TMP_22))))))))) in (let TMP_24 \def (Flat f) in (let TMP_25 \def (lift1 p u) 
in (let TMP_26 \def (lift n n0 TMP_25) in (let TMP_27 \def (lift1 p t) in 
(let TMP_28 \def (lift n n0 TMP_27) in (let TMP_29 \def (THead TMP_24 TMP_26 
TMP_28) in (let TMP_36 \def (\lambda (t0: T).(let TMP_30 \def (Flat f) in 
(let TMP_31 \def (lift1 p u) in (let TMP_32 \def (lift n n0 TMP_31) in (let 
TMP_33 \def (lift1 p t) in (let TMP_34 \def (lift n n0 TMP_33) in (let TMP_35 
\def (THead TMP_30 TMP_32 TMP_34) in (eq T t0 TMP_35)))))))) in (let TMP_37 
\def (Flat f) in (let TMP_38 \def (lift1 p u) in (let TMP_39 \def (lift n n0 
TMP_38) in (let TMP_40 \def (lift1 p t) in (let TMP_41 \def (lift n n0 
TMP_40) in (let TMP_42 \def (THead TMP_37 TMP_39 TMP_41) in (let TMP_43 \def 
(refl_equal T TMP_42) in (let TMP_44 \def (Flat f) in (let TMP_45 \def (lift1 
p u) in (let TMP_46 \def (lift1 p t) in (let TMP_47 \def (THead TMP_44 TMP_45 
TMP_46) in (let TMP_48 \def (lift n n0 TMP_47) in (let TMP_49 \def (lift1 p 
u) in (let TMP_50 \def (lift1 p t) in (let TMP_51 \def (lift_flat f TMP_49 
TMP_50 n n0) in (let TMP_52 \def (eq_ind_r T TMP_29 TMP_36 TMP_43 TMP_48 
TMP_51) in (let TMP_53 \def (Flat f) in (let TMP_54 \def (THead TMP_53 u t) 
in (let TMP_55 \def (lift1 p TMP_54) in (let TMP_56 \def (H u t) in (eq_ind_r 
T TMP_15 TMP_23 TMP_52 TMP_55 TMP_56))))))))))))))))))))))))))))))))))))))) 
in (PList_ind TMP_8 TMP_11 TMP_57 hds))))).

theorem lift1_cons_tail:
 \forall (t: T).(\forall (h: nat).(\forall (d: nat).(\forall (hds: PList).(eq 
T (lift1 (PConsTail hds h d) t) (lift1 hds (lift h d t))))))
\def
 \lambda (t: T).(\lambda (h: nat).(\lambda (d: nat).(\lambda (hds: 
PList).(let TMP_5 \def (\lambda (p: PList).(let TMP_1 \def (PConsTail p h d) 
in (let TMP_2 \def (lift1 TMP_1 t) in (let TMP_3 \def (lift h d t) in (let 
TMP_4 \def (lift1 p TMP_3) in (eq T TMP_2 TMP_4)))))) in (let TMP_6 \def 
(lift h d t) in (let TMP_7 \def (refl_equal T TMP_6) in (let TMP_21 \def 
(\lambda (n: nat).(\lambda (n0: nat).(\lambda (p: PList).(\lambda (H: (eq T 
(lift1 (PConsTail p h d) t) (lift1 p (lift h d t)))).(let TMP_8 \def (lift h 
d t) in (let TMP_9 \def (lift1 p TMP_8) in (let TMP_14 \def (\lambda (t0: 
T).(let TMP_10 \def (lift n n0 t0) in (let TMP_11 \def (lift h d t) in (let 
TMP_12 \def (lift1 p TMP_11) in (let TMP_13 \def (lift n n0 TMP_12) in (eq T 
TMP_10 TMP_13)))))) in (let TMP_15 \def (lift h d t) in (let TMP_16 \def 
(lift1 p TMP_15) in (let TMP_17 \def (lift n n0 TMP_16) in (let TMP_18 \def 
(refl_equal T TMP_17) in (let TMP_19 \def (PConsTail p h d) in (let TMP_20 
\def (lift1 TMP_19 t) in (eq_ind_r T TMP_9 TMP_14 TMP_18 TMP_20 
H)))))))))))))) in (PList_ind TMP_5 TMP_7 TMP_21 hds)))))))).

theorem lifts1_flat:
 \forall (f: F).(\forall (hds: PList).(\forall (t: T).(\forall (ts: 
TList).(eq T (lift1 hds (THeads (Flat f) ts t)) (THeads (Flat f) (lifts1 hds 
ts) (lift1 hds t))))))
\def
 \lambda (f: F).(\lambda (hds: PList).(\lambda (t: T).(\lambda (ts: 
TList).(let TMP_8 \def (\lambda (t0: TList).(let TMP_1 \def (Flat f) in (let 
TMP_2 \def (THeads TMP_1 t0 t) in (let TMP_3 \def (lift1 hds TMP_2) in (let 
TMP_4 \def (Flat f) in (let TMP_5 \def (lifts1 hds t0) in (let TMP_6 \def 
(lift1 hds t) in (let TMP_7 \def (THeads TMP_4 TMP_5 TMP_6) in (eq T TMP_3 
TMP_7))))))))) in (let TMP_9 \def (lift1 hds t) in (let TMP_10 \def 
(refl_equal T TMP_9) in (let TMP_60 \def (\lambda (t0: T).(\lambda (t1: 
TList).(\lambda (H: (eq T (lift1 hds (THeads (Flat f) t1 t)) (THeads (Flat f) 
(lifts1 hds t1) (lift1 hds t)))).(let TMP_11 \def (Flat f) in (let TMP_12 
\def (lift1 hds t0) in (let TMP_13 \def (Flat f) in (let TMP_14 \def (THeads 
TMP_13 t1 t) in (let TMP_15 \def (lift1 hds TMP_14) in (let TMP_16 \def 
(THead TMP_11 TMP_12 TMP_15) in (let TMP_24 \def (\lambda (t2: T).(let TMP_17 
\def (Flat f) in (let TMP_18 \def (lift1 hds t0) in (let TMP_19 \def (Flat f) 
in (let TMP_20 \def (lifts1 hds t1) in (let TMP_21 \def (lift1 hds t) in (let 
TMP_22 \def (THeads TMP_19 TMP_20 TMP_21) in (let TMP_23 \def (THead TMP_17 
TMP_18 TMP_22) in (eq T t2 TMP_23))))))))) in (let TMP_25 \def (Flat f) in 
(let TMP_26 \def (lifts1 hds t1) in (let TMP_27 \def (lift1 hds t) in (let 
TMP_28 \def (THeads TMP_25 TMP_26 TMP_27) in (let TMP_39 \def (\lambda (t2: 
T).(let TMP_29 \def (Flat f) in (let TMP_30 \def (lift1 hds t0) in (let 
TMP_31 \def (THead TMP_29 TMP_30 t2) in (let TMP_32 \def (Flat f) in (let 
TMP_33 \def (lift1 hds t0) in (let TMP_34 \def (Flat f) in (let TMP_35 \def 
(lifts1 hds t1) in (let TMP_36 \def (lift1 hds t) in (let TMP_37 \def (THeads 
TMP_34 TMP_35 TMP_36) in (let TMP_38 \def (THead TMP_32 TMP_33 TMP_37) in (eq 
T TMP_31 TMP_38)))))))))))) in (let TMP_40 \def (Flat f) in (let TMP_41 \def 
(lift1 hds t0) in (let TMP_42 \def (Flat f) in (let TMP_43 \def (lifts1 hds 
t1) in (let TMP_44 \def (lift1 hds t) in (let TMP_45 \def (THeads TMP_42 
TMP_43 TMP_44) in (let TMP_46 \def (THead TMP_40 TMP_41 TMP_45) in (let 
TMP_47 \def (refl_equal T TMP_46) in (let TMP_48 \def (Flat f) in (let TMP_49 
\def (THeads TMP_48 t1 t) in (let TMP_50 \def (lift1 hds TMP_49) in (let 
TMP_51 \def (eq_ind_r T TMP_28 TMP_39 TMP_47 TMP_50 H) in (let TMP_52 \def 
(Flat f) in (let TMP_53 \def (Flat f) in (let TMP_54 \def (THeads TMP_53 t1 
t) in (let TMP_55 \def (THead TMP_52 t0 TMP_54) in (let TMP_56 \def (lift1 
hds TMP_55) in (let TMP_57 \def (Flat f) in (let TMP_58 \def (THeads TMP_57 
t1 t) in (let TMP_59 \def (lift1_flat f hds t0 TMP_58) in (eq_ind_r T TMP_16 
TMP_24 TMP_51 TMP_56 TMP_59)))))))))))))))))))))))))))))))))))) in (TList_ind 
TMP_8 TMP_10 TMP_60 ts)))))))).

theorem lifts1_nil:
 \forall (ts: TList).(eq TList (lifts1 PNil ts) ts)
\def
 \lambda (ts: TList).(let TMP_2 \def (\lambda (t: TList).(let TMP_1 \def 
(lifts1 PNil t) in (eq TList TMP_1 t))) in (let TMP_3 \def (refl_equal TList 
TNil) in (let TMP_10 \def (\lambda (t: T).(\lambda (t0: TList).(\lambda (H: 
(eq TList (lifts1 PNil t0) t0)).(let TMP_6 \def (\lambda (t1: TList).(let 
TMP_4 \def (TCons t t1) in (let TMP_5 \def (TCons t t0) in (eq TList TMP_4 
TMP_5)))) in (let TMP_7 \def (TCons t t0) in (let TMP_8 \def (refl_equal 
TList TMP_7) in (let TMP_9 \def (lifts1 PNil t0) in (eq_ind_r TList t0 TMP_6 
TMP_8 TMP_9 H)))))))) in (TList_ind TMP_2 TMP_3 TMP_10 ts)))).

theorem lifts1_cons:
 \forall (h: nat).(\forall (d: nat).(\forall (hds: PList).(\forall (ts: 
TList).(eq TList (lifts1 (PCons h d hds) ts) (lifts h d (lifts1 hds ts))))))
\def
 \lambda (h: nat).(\lambda (d: nat).(\lambda (hds: PList).(\lambda (ts: 
TList).(let TMP_5 \def (\lambda (t: TList).(let TMP_1 \def (PCons h d hds) in 
(let TMP_2 \def (lifts1 TMP_1 t) in (let TMP_3 \def (lifts1 hds t) in (let 
TMP_4 \def (lifts h d TMP_3) in (eq TList TMP_2 TMP_4)))))) in (let TMP_6 
\def (refl_equal TList TNil) in (let TMP_26 \def (\lambda (t: T).(\lambda 
(t0: TList).(\lambda (H: (eq TList (lifts1 (PCons h d hds) t0) (lifts h d 
(lifts1 hds t0)))).(let TMP_7 \def (lifts1 hds t0) in (let TMP_8 \def (lifts 
h d TMP_7) in (let TMP_17 \def (\lambda (t1: TList).(let TMP_9 \def (lift1 
hds t) in (let TMP_10 \def (lift h d TMP_9) in (let TMP_11 \def (TCons TMP_10 
t1) in (let TMP_12 \def (lift1 hds t) in (let TMP_13 \def (lift h d TMP_12) 
in (let TMP_14 \def (lifts1 hds t0) in (let TMP_15 \def (lifts h d TMP_14) in 
(let TMP_16 \def (TCons TMP_13 TMP_15) in (eq TList TMP_11 TMP_16)))))))))) 
in (let TMP_18 \def (lift1 hds t) in (let TMP_19 \def (lift h d TMP_18) in 
(let TMP_20 \def (lifts1 hds t0) in (let TMP_21 \def (lifts h d TMP_20) in 
(let TMP_22 \def (TCons TMP_19 TMP_21) in (let TMP_23 \def (refl_equal TList 
TMP_22) in (let TMP_24 \def (PCons h d hds) in (let TMP_25 \def (lifts1 
TMP_24 t0) in (eq_ind_r TList TMP_8 TMP_17 TMP_23 TMP_25 H))))))))))))))) in 
(TList_ind TMP_5 TMP_6 TMP_26 ts))))))).

