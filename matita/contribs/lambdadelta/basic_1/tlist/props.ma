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

include "basic_1/tlist/defs.ma".

theorem theads_tapp:
 \forall (k: K).(\forall (v: T).(\forall (t: T).(\forall (vs: TList).(eq T 
(THeads k (TApp vs v) t) (THeads k vs (THead k v t))))))
\def
 \lambda (k: K).(\lambda (v: T).(\lambda (t: T).(\lambda (vs: TList).(let 
TMP_5 \def (\lambda (t0: TList).(let TMP_1 \def (TApp t0 v) in (let TMP_2 
\def (THeads k TMP_1 t) in (let TMP_3 \def (THead k v t) in (let TMP_4 \def 
(THeads k t0 TMP_3) in (eq T TMP_2 TMP_4)))))) in (let TMP_6 \def (THead k v 
t) in (let TMP_7 \def (refl_equal T TMP_6) in (let TMP_21 \def (\lambda (t0: 
T).(\lambda (t1: TList).(\lambda (H: (eq T (THeads k (TApp t1 v) t) (THeads k 
t1 (THead k v t)))).(let TMP_8 \def (TApp t1 v) in (let TMP_9 \def (THeads k 
TMP_8 t) in (let TMP_14 \def (\lambda (t2: T).(let TMP_10 \def (TApp t1 v) in 
(let TMP_11 \def (THeads k TMP_10 t) in (let TMP_12 \def (THead k t0 TMP_11) 
in (let TMP_13 \def (THead k t0 t2) in (eq T TMP_12 TMP_13)))))) in (let 
TMP_15 \def (TApp t1 v) in (let TMP_16 \def (THeads k TMP_15 t) in (let 
TMP_17 \def (THead k t0 TMP_16) in (let TMP_18 \def (refl_equal T TMP_17) in 
(let TMP_19 \def (THead k v t) in (let TMP_20 \def (THeads k t1 TMP_19) in 
(eq_ind T TMP_9 TMP_14 TMP_18 TMP_20 H))))))))))))) in (TList_ind TMP_5 TMP_7 
TMP_21 vs)))))))).

theorem tcons_tapp_ex:
 \forall (ts1: TList).(\forall (t1: T).(ex2_2 TList T (\lambda (ts2: 
TList).(\lambda (t2: T).(eq TList (TCons t1 ts1) (TApp ts2 t2)))) (\lambda 
(ts2: TList).(\lambda (_: T).(eq nat (tslen ts1) (tslen ts2))))))
\def
 \lambda (ts1: TList).(let TMP_7 \def (\lambda (t: TList).(\forall (t1: 
T).(let TMP_3 \def (\lambda (ts2: TList).(\lambda (t2: T).(let TMP_1 \def 
(TCons t1 t) in (let TMP_2 \def (TApp ts2 t2) in (eq TList TMP_1 TMP_2))))) 
in (let TMP_6 \def (\lambda (ts2: TList).(\lambda (_: T).(let TMP_4 \def 
(tslen t) in (let TMP_5 \def (tslen ts2) in (eq nat TMP_4 TMP_5))))) in 
(ex2_2 TList T TMP_3 TMP_6))))) in (let TMP_17 \def (\lambda (t1: T).(let 
TMP_10 \def (\lambda (ts2: TList).(\lambda (t2: T).(let TMP_8 \def (TCons t1 
TNil) in (let TMP_9 \def (TApp ts2 t2) in (eq TList TMP_8 TMP_9))))) in (let 
TMP_12 \def (\lambda (ts2: TList).(\lambda (_: T).(let TMP_11 \def (tslen 
ts2) in (eq nat O TMP_11)))) in (let TMP_13 \def (TApp TNil t1) in (let 
TMP_14 \def (refl_equal TList TMP_13) in (let TMP_15 \def (tslen TNil) in 
(let TMP_16 \def (refl_equal nat TMP_15) in (ex2_2_intro TList T TMP_10 
TMP_12 TNil t1 TMP_14 TMP_16)))))))) in (let TMP_71 \def (\lambda (t: 
T).(\lambda (t0: TList).(\lambda (H: ((\forall (t1: T).(ex2_2 TList T 
(\lambda (ts2: TList).(\lambda (t2: T).(eq TList (TCons t1 t0) (TApp ts2 
t2)))) (\lambda (ts2: TList).(\lambda (_: T).(eq nat (tslen t0) (tslen 
ts2)))))))).(\lambda (t1: T).(let H_x \def (H t) in (let H0 \def H_x in (let 
TMP_20 \def (\lambda (ts2: TList).(\lambda (t2: T).(let TMP_18 \def (TCons t 
t0) in (let TMP_19 \def (TApp ts2 t2) in (eq TList TMP_18 TMP_19))))) in (let 
TMP_23 \def (\lambda (ts2: TList).(\lambda (_: T).(let TMP_21 \def (tslen t0) 
in (let TMP_22 \def (tslen ts2) in (eq nat TMP_21 TMP_22))))) in (let TMP_27 
\def (\lambda (ts2: TList).(\lambda (t2: T).(let TMP_24 \def (TCons t t0) in 
(let TMP_25 \def (TCons t1 TMP_24) in (let TMP_26 \def (TApp ts2 t2) in (eq 
TList TMP_25 TMP_26)))))) in (let TMP_31 \def (\lambda (ts2: TList).(\lambda 
(_: T).(let TMP_28 \def (tslen t0) in (let TMP_29 \def (S TMP_28) in (let 
TMP_30 \def (tslen ts2) in (eq nat TMP_29 TMP_30)))))) in (let TMP_32 \def 
(ex2_2 TList T TMP_27 TMP_31) in (let TMP_70 \def (\lambda (x0: 
TList).(\lambda (x1: T).(\lambda (H1: (eq TList (TCons t t0) (TApp x0 
x1))).(\lambda (H2: (eq nat (tslen t0) (tslen x0))).(let TMP_33 \def (TApp x0 
x1) in (let TMP_41 \def (\lambda (t2: TList).(let TMP_36 \def (\lambda (ts2: 
TList).(\lambda (t3: T).(let TMP_34 \def (TCons t1 t2) in (let TMP_35 \def 
(TApp ts2 t3) in (eq TList TMP_34 TMP_35))))) in (let TMP_40 \def (\lambda 
(ts2: TList).(\lambda (_: T).(let TMP_37 \def (tslen t0) in (let TMP_38 \def 
(S TMP_37) in (let TMP_39 \def (tslen ts2) in (eq nat TMP_38 TMP_39)))))) in 
(ex2_2 TList T TMP_36 TMP_40)))) in (let TMP_42 \def (tslen x0) in (let 
TMP_50 \def (\lambda (n: nat).(let TMP_46 \def (\lambda (ts2: TList).(\lambda 
(t2: T).(let TMP_43 \def (TApp x0 x1) in (let TMP_44 \def (TCons t1 TMP_43) 
in (let TMP_45 \def (TApp ts2 t2) in (eq TList TMP_44 TMP_45)))))) in (let 
TMP_49 \def (\lambda (ts2: TList).(\lambda (_: T).(let TMP_47 \def (S n) in 
(let TMP_48 \def (tslen ts2) in (eq nat TMP_47 TMP_48))))) in (ex2_2 TList T 
TMP_46 TMP_49)))) in (let TMP_54 \def (\lambda (ts2: TList).(\lambda (t2: 
T).(let TMP_51 \def (TApp x0 x1) in (let TMP_52 \def (TCons t1 TMP_51) in 
(let TMP_53 \def (TApp ts2 t2) in (eq TList TMP_52 TMP_53)))))) in (let 
TMP_58 \def (\lambda (ts2: TList).(\lambda (_: T).(let TMP_55 \def (tslen x0) 
in (let TMP_56 \def (S TMP_55) in (let TMP_57 \def (tslen ts2) in (eq nat 
TMP_56 TMP_57)))))) in (let TMP_59 \def (TCons t1 x0) in (let TMP_60 \def 
(TCons t1 x0) in (let TMP_61 \def (TApp TMP_60 x1) in (let TMP_62 \def 
(refl_equal TList TMP_61) in (let TMP_63 \def (TCons t1 x0) in (let TMP_64 
\def (tslen TMP_63) in (let TMP_65 \def (refl_equal nat TMP_64) in (let 
TMP_66 \def (ex2_2_intro TList T TMP_54 TMP_58 TMP_59 x1 TMP_62 TMP_65) in 
(let TMP_67 \def (tslen t0) in (let TMP_68 \def (eq_ind_r nat TMP_42 TMP_50 
TMP_66 TMP_67 H2) in (let TMP_69 \def (TCons t t0) in (eq_ind_r TList TMP_33 
TMP_41 TMP_68 TMP_69 H1)))))))))))))))))))))) in (ex2_2_ind TList T TMP_20 
TMP_23 TMP_32 TMP_70 H0))))))))))))) in (TList_ind TMP_7 TMP_17 TMP_71 
ts1)))).

