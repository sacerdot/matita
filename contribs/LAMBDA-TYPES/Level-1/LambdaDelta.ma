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

set "baseuri" "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta".

include "LambdaDelta/theory.ma".

definition TApp:
 TList \to (T \to TList)
\def
 let rec TApp (ts: TList) on ts: (T \to TList) \def (\lambda (v: T).(match ts 
with [TNil \Rightarrow (TCons v TNil) | (TCons t ts0) \Rightarrow (TCons t 
(TApp ts0 v))])) in TApp.

definition tslen:
 TList \to nat
\def
 let rec tslen (ts: TList) on ts: nat \def (match ts with [TNil \Rightarrow O 
| (TCons _ ts0) \Rightarrow (S (tslen ts0))]) in tslen.

definition tslt:
 TList \to (TList \to Prop)
\def
 \lambda (ts1: TList).(\lambda (ts2: TList).(lt (tslen ts1) (tslen ts2))).

theorem tslt_wf__q_ind:
 \forall (P: ((TList \to Prop))).(((\forall (n: nat).((\lambda (P0: ((TList 
\to Prop))).(\lambda (n0: nat).(\forall (ts: TList).((eq nat (tslen ts) n0) 
\to (P0 ts))))) P n))) \to (\forall (ts: TList).(P ts)))
\def
 let Q \def (\lambda (P: ((TList \to Prop))).(\lambda (n: nat).(\forall (ts: 
TList).((eq nat (tslen ts) n) \to (P ts))))) in (\lambda (P: ((TList \to 
Prop))).(\lambda (H: ((\forall (n: nat).(\forall (ts: TList).((eq nat (tslen 
ts) n) \to (P ts)))))).(\lambda (ts: TList).(H (tslen ts) ts (refl_equal nat 
(tslen ts)))))).

theorem tslt_wf_ind:
 \forall (P: ((TList \to Prop))).(((\forall (ts2: TList).(((\forall (ts1: 
TList).((tslt ts1 ts2) \to (P ts1)))) \to (P ts2)))) \to (\forall (ts: 
TList).(P ts)))
\def
 let Q \def (\lambda (P: ((TList \to Prop))).(\lambda (n: nat).(\forall (ts: 
TList).((eq nat (tslen ts) n) \to (P ts))))) in (\lambda (P: ((TList \to 
Prop))).(\lambda (H: ((\forall (ts2: TList).(((\forall (ts1: TList).((lt 
(tslen ts1) (tslen ts2)) \to (P ts1)))) \to (P ts2))))).(\lambda (ts: 
TList).(tslt_wf__q_ind (\lambda (t: TList).(P t)) (\lambda (n: 
nat).(lt_wf_ind n (Q (\lambda (t: TList).(P t))) (\lambda (n0: nat).(\lambda 
(H0: ((\forall (m: nat).((lt m n0) \to (Q (\lambda (t: TList).(P t)) 
m))))).(\lambda (ts0: TList).(\lambda (H1: (eq nat (tslen ts0) n0)).(let H2 
\def (eq_ind_r nat n0 (\lambda (n1: nat).(\forall (m: nat).((lt m n1) \to 
(\forall (ts1: TList).((eq nat (tslen ts1) m) \to (P ts1)))))) H0 (tslen ts0) 
H1) in (H ts0 (\lambda (ts1: TList).(\lambda (H3: (lt (tslen ts1) (tslen 
ts0))).(H2 (tslen ts1) H3 ts1 (refl_equal nat (tslen ts1))))))))))))) ts)))).

theorem theads_tapp:
 \forall (k: K).(\forall (vs: TList).(\forall (v: T).(\forall (t: T).(eq T 
(THeads k (TApp vs v) t) (THeads k vs (THead k v t))))))
\def
 \lambda (k: K).(\lambda (vs: TList).(TList_ind (\lambda (t: TList).(\forall 
(v: T).(\forall (t0: T).(eq T (THeads k (TApp t v) t0) (THeads k t (THead k v 
t0)))))) (\lambda (v: T).(\lambda (t: T).(refl_equal T (THead k v t)))) 
(\lambda (t: T).(\lambda (t0: TList).(\lambda (H: ((\forall (v: T).(\forall 
(t1: T).(eq T (THeads k (TApp t0 v) t1) (THeads k t0 (THead k v 
t1))))))).(\lambda (v: T).(\lambda (t1: T).(eq_ind_r T (THeads k t0 (THead k 
v t1)) (\lambda (t2: T).(eq T (THead k t t2) (THead k t (THeads k t0 (THead k 
v t1))))) (refl_equal T (THead k t (THeads k t0 (THead k v t1)))) (THeads k 
(TApp t0 v) t1) (H v t1))))))) vs)).

theorem tcons_tapp_ex:
 \forall (ts1: TList).(\forall (t1: T).(ex2_2 TList T (\lambda (ts2: 
TList).(\lambda (t2: T).(eq TList (TCons t1 ts1) (TApp ts2 t2)))) (\lambda 
(ts2: TList).(\lambda (_: T).(eq nat (tslen ts1) (tslen ts2))))))
\def
 \lambda (ts1: TList).(TList_ind (\lambda (t: TList).(\forall (t1: T).(ex2_2 
TList T (\lambda (ts2: TList).(\lambda (t2: T).(eq TList (TCons t1 t) (TApp 
ts2 t2)))) (\lambda (ts2: TList).(\lambda (_: T).(eq nat (tslen t) (tslen 
ts2))))))) (\lambda (t1: T).(ex2_2_intro TList T (\lambda (ts2: 
TList).(\lambda (t2: T).(eq TList (TCons t1 TNil) (TApp ts2 t2)))) (\lambda 
(ts2: TList).(\lambda (_: T).(eq nat O (tslen ts2)))) TNil t1 (refl_equal 
TList (TApp TNil t1)) (refl_equal nat (tslen TNil)))) (\lambda (t: 
T).(\lambda (t0: TList).(\lambda (H: ((\forall (t1: T).(ex2_2 TList T 
(\lambda (ts2: TList).(\lambda (t2: T).(eq TList (TCons t1 t0) (TApp ts2 
t2)))) (\lambda (ts2: TList).(\lambda (_: T).(eq nat (tslen t0) (tslen 
ts2)))))))).(\lambda (t1: T).(let H_x \def (H t) in (let H0 \def H_x in 
(ex2_2_ind TList T (\lambda (ts2: TList).(\lambda (t2: T).(eq TList (TCons t 
t0) (TApp ts2 t2)))) (\lambda (ts2: TList).(\lambda (_: T).(eq nat (tslen t0) 
(tslen ts2)))) (ex2_2 TList T (\lambda (ts2: TList).(\lambda (t2: T).(eq 
TList (TCons t1 (TCons t t0)) (TApp ts2 t2)))) (\lambda (ts2: TList).(\lambda 
(_: T).(eq nat (S (tslen t0)) (tslen ts2))))) (\lambda (x0: TList).(\lambda 
(x1: T).(\lambda (H1: (eq TList (TCons t t0) (TApp x0 x1))).(\lambda (H2: (eq 
nat (tslen t0) (tslen x0))).(eq_ind_r TList (TApp x0 x1) (\lambda (t2: 
TList).(ex2_2 TList T (\lambda (ts2: TList).(\lambda (t3: T).(eq TList (TCons 
t1 t2) (TApp ts2 t3)))) (\lambda (ts2: TList).(\lambda (_: T).(eq nat (S 
(tslen t0)) (tslen ts2)))))) (eq_ind_r nat (tslen x0) (\lambda (n: 
nat).(ex2_2 TList T (\lambda (ts2: TList).(\lambda (t2: T).(eq TList (TCons 
t1 (TApp x0 x1)) (TApp ts2 t2)))) (\lambda (ts2: TList).(\lambda (_: T).(eq 
nat (S n) (tslen ts2)))))) (ex2_2_intro TList T (\lambda (ts2: 
TList).(\lambda (t2: T).(eq TList (TCons t1 (TApp x0 x1)) (TApp ts2 t2)))) 
(\lambda (ts2: TList).(\lambda (_: T).(eq nat (S (tslen x0)) (tslen ts2)))) 
(TCons t1 x0) x1 (refl_equal TList (TApp (TCons t1 x0) x1)) (refl_equal nat 
(tslen (TCons t1 x0)))) (tslen t0) H2) (TCons t t0) H1))))) H0))))))) ts1).

theorem tlist_ind_rew:
 \forall (P: ((TList \to Prop))).((P TNil) \to (((\forall (ts: 
TList).(\forall (t: T).((P ts) \to (P (TApp ts t)))))) \to (\forall (ts: 
TList).(P ts))))
\def
 \lambda (P: ((TList \to Prop))).(\lambda (H: (P TNil)).(\lambda (H0: 
((\forall (ts: TList).(\forall (t: T).((P ts) \to (P (TApp ts 
t))))))).(\lambda (ts: TList).(tslt_wf_ind (\lambda (t: TList).(P t)) 
(\lambda (ts2: TList).(match ts2 in TList return (\lambda (t: 
TList).(((\forall (ts1: TList).((tslt ts1 t) \to (P ts1)))) \to (P t))) with 
[TNil \Rightarrow (\lambda (_: ((\forall (ts1: TList).((tslt ts1 TNil) \to (P 
ts1))))).H) | (TCons t t0) \Rightarrow (\lambda (H1: ((\forall (ts1: 
TList).((tslt ts1 (TCons t t0)) \to (P ts1))))).(let H_x \def (tcons_tapp_ex 
t0 t) in (let H2 \def H_x in (ex2_2_ind TList T (\lambda (ts3: 
TList).(\lambda (t2: T).(eq TList (TCons t t0) (TApp ts3 t2)))) (\lambda 
(ts3: TList).(\lambda (_: T).(eq nat (tslen t0) (tslen ts3)))) (P (TCons t 
t0)) (\lambda (x0: TList).(\lambda (x1: T).(\lambda (H3: (eq TList (TCons t 
t0) (TApp x0 x1))).(\lambda (H4: (eq nat (tslen t0) (tslen x0))).(eq_ind_r 
TList (TApp x0 x1) (\lambda (t1: TList).(P t1)) (H0 x0 x1 (H1 x0 (eq_ind nat 
(tslen t0) (\lambda (n: nat).(lt n (tslen (TCons t t0)))) (le_n (tslen (TCons 
t t0))) (tslen x0) H4))) (TCons t t0) H3))))) H2))))])) ts)))).

theorem iso_gen_sort:
 \forall (u2: T).(\forall (n1: nat).((iso (TSort n1) u2) \to (ex nat (\lambda 
(n2: nat).(eq T u2 (TSort n2))))))
\def
 \lambda (u2: T).(\lambda (n1: nat).(\lambda (H: (iso (TSort n1) u2)).(let H0 
\def (match H in iso return (\lambda (t: T).(\lambda (t0: T).(\lambda (_: 
(iso t t0)).((eq T t (TSort n1)) \to ((eq T t0 u2) \to (ex nat (\lambda (n2: 
nat).(eq T u2 (TSort n2))))))))) with [(iso_sort n0 n2) \Rightarrow (\lambda 
(H0: (eq T (TSort n0) (TSort n1))).(\lambda (H1: (eq T (TSort n2) u2)).((let 
H2 \def (f_equal T nat (\lambda (e: T).(match e in T return (\lambda (_: 
T).nat) with [(TSort n) \Rightarrow n | (TLRef _) \Rightarrow n0 | (THead _ _ 
_) \Rightarrow n0])) (TSort n0) (TSort n1) H0) in (eq_ind nat n1 (\lambda (_: 
nat).((eq T (TSort n2) u2) \to (ex nat (\lambda (n3: nat).(eq T u2 (TSort 
n3)))))) (\lambda (H3: (eq T (TSort n2) u2)).(eq_ind T (TSort n2) (\lambda 
(t: T).(ex nat (\lambda (n3: nat).(eq T t (TSort n3))))) (ex_intro nat 
(\lambda (n3: nat).(eq T (TSort n2) (TSort n3))) n2 (refl_equal T (TSort 
n2))) u2 H3)) n0 (sym_eq nat n0 n1 H2))) H1))) | (iso_lref i1 i2) \Rightarrow 
(\lambda (H0: (eq T (TLRef i1) (TSort n1))).(\lambda (H1: (eq T (TLRef i2) 
u2)).((let H2 \def (eq_ind T (TLRef i1) (\lambda (e: T).(match e in T return 
(\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow True | (THead _ _ _) \Rightarrow False])) I (TSort n1) H0) in 
(False_ind ((eq T (TLRef i2) u2) \to (ex nat (\lambda (n2: nat).(eq T u2 
(TSort n2))))) H2)) H1))) | (iso_head v1 v2 t1 t2 k) \Rightarrow (\lambda 
(H0: (eq T (THead k v1 t1) (TSort n1))).(\lambda (H1: (eq T (THead k v2 t2) 
u2)).((let H2 \def (eq_ind T (THead k v1 t1) (\lambda (e: T).(match e in T 
return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow False | (THead _ _ _) \Rightarrow True])) I (TSort n1) H0) in 
(False_ind ((eq T (THead k v2 t2) u2) \to (ex nat (\lambda (n2: nat).(eq T u2 
(TSort n2))))) H2)) H1)))]) in (H0 (refl_equal T (TSort n1)) (refl_equal T 
u2))))).

theorem iso_gen_lref:
 \forall (u2: T).(\forall (n1: nat).((iso (TLRef n1) u2) \to (ex nat (\lambda 
(n2: nat).(eq T u2 (TLRef n2))))))
\def
 \lambda (u2: T).(\lambda (n1: nat).(\lambda (H: (iso (TLRef n1) u2)).(let H0 
\def (match H in iso return (\lambda (t: T).(\lambda (t0: T).(\lambda (_: 
(iso t t0)).((eq T t (TLRef n1)) \to ((eq T t0 u2) \to (ex nat (\lambda (n2: 
nat).(eq T u2 (TLRef n2))))))))) with [(iso_sort n0 n2) \Rightarrow (\lambda 
(H0: (eq T (TSort n0) (TLRef n1))).(\lambda (H1: (eq T (TSort n2) u2)).((let 
H2 \def (eq_ind T (TSort n0) (\lambda (e: T).(match e in T return (\lambda 
(_: T).Prop) with [(TSort _) \Rightarrow True | (TLRef _) \Rightarrow False | 
(THead _ _ _) \Rightarrow False])) I (TLRef n1) H0) in (False_ind ((eq T 
(TSort n2) u2) \to (ex nat (\lambda (n3: nat).(eq T u2 (TLRef n3))))) H2)) 
H1))) | (iso_lref i1 i2) \Rightarrow (\lambda (H0: (eq T (TLRef i1) (TLRef 
n1))).(\lambda (H1: (eq T (TLRef i2) u2)).((let H2 \def (f_equal T nat 
(\lambda (e: T).(match e in T return (\lambda (_: T).nat) with [(TSort _) 
\Rightarrow i1 | (TLRef n) \Rightarrow n | (THead _ _ _) \Rightarrow i1])) 
(TLRef i1) (TLRef n1) H0) in (eq_ind nat n1 (\lambda (_: nat).((eq T (TLRef 
i2) u2) \to (ex nat (\lambda (n2: nat).(eq T u2 (TLRef n2)))))) (\lambda (H3: 
(eq T (TLRef i2) u2)).(eq_ind T (TLRef i2) (\lambda (t: T).(ex nat (\lambda 
(n2: nat).(eq T t (TLRef n2))))) (ex_intro nat (\lambda (n2: nat).(eq T 
(TLRef i2) (TLRef n2))) i2 (refl_equal T (TLRef i2))) u2 H3)) i1 (sym_eq nat 
i1 n1 H2))) H1))) | (iso_head v1 v2 t1 t2 k) \Rightarrow (\lambda (H0: (eq T 
(THead k v1 t1) (TLRef n1))).(\lambda (H1: (eq T (THead k v2 t2) u2)).((let 
H2 \def (eq_ind T (THead k v1 t1) (\lambda (e: T).(match e in T return 
(\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow False | (THead _ _ _) \Rightarrow True])) I (TLRef n1) H0) in 
(False_ind ((eq T (THead k v2 t2) u2) \to (ex nat (\lambda (n2: nat).(eq T u2 
(TLRef n2))))) H2)) H1)))]) in (H0 (refl_equal T (TLRef n1)) (refl_equal T 
u2))))).

theorem iso_gen_head:
 \forall (k: K).(\forall (v1: T).(\forall (t1: T).(\forall (u2: T).((iso 
(THead k v1 t1) u2) \to (ex_2 T T (\lambda (v2: T).(\lambda (t2: T).(eq T u2 
(THead k v2 t2)))))))))
\def
 \lambda (k: K).(\lambda (v1: T).(\lambda (t1: T).(\lambda (u2: T).(\lambda 
(H: (iso (THead k v1 t1) u2)).(let H0 \def (match H in iso return (\lambda 
(t: T).(\lambda (t0: T).(\lambda (_: (iso t t0)).((eq T t (THead k v1 t1)) 
\to ((eq T t0 u2) \to (ex_2 T T (\lambda (v2: T).(\lambda (t2: T).(eq T u2 
(THead k v2 t2)))))))))) with [(iso_sort n1 n2) \Rightarrow (\lambda (H0: (eq 
T (TSort n1) (THead k v1 t1))).(\lambda (H1: (eq T (TSort n2) u2)).((let H2 
\def (eq_ind T (TSort n1) (\lambda (e: T).(match e in T return (\lambda (_: 
T).Prop) with [(TSort _) \Rightarrow True | (TLRef _) \Rightarrow False | 
(THead _ _ _) \Rightarrow False])) I (THead k v1 t1) H0) in (False_ind ((eq T 
(TSort n2) u2) \to (ex_2 T T (\lambda (v2: T).(\lambda (t2: T).(eq T u2 
(THead k v2 t2)))))) H2)) H1))) | (iso_lref i1 i2) \Rightarrow (\lambda (H0: 
(eq T (TLRef i1) (THead k v1 t1))).(\lambda (H1: (eq T (TLRef i2) u2)).((let 
H2 \def (eq_ind T (TLRef i1) (\lambda (e: T).(match e in T return (\lambda 
(_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow True | 
(THead _ _ _) \Rightarrow False])) I (THead k v1 t1) H0) in (False_ind ((eq T 
(TLRef i2) u2) \to (ex_2 T T (\lambda (v2: T).(\lambda (t2: T).(eq T u2 
(THead k v2 t2)))))) H2)) H1))) | (iso_head v0 v2 t0 t2 k0) \Rightarrow 
(\lambda (H0: (eq T (THead k0 v0 t0) (THead k v1 t1))).(\lambda (H1: (eq T 
(THead k0 v2 t2) u2)).((let H2 \def (f_equal T T (\lambda (e: T).(match e in 
T return (\lambda (_: T).T) with [(TSort _) \Rightarrow t0 | (TLRef _) 
\Rightarrow t0 | (THead _ _ t) \Rightarrow t])) (THead k0 v0 t0) (THead k v1 
t1) H0) in ((let H3 \def (f_equal T T (\lambda (e: T).(match e in T return 
(\lambda (_: T).T) with [(TSort _) \Rightarrow v0 | (TLRef _) \Rightarrow v0 
| (THead _ t _) \Rightarrow t])) (THead k0 v0 t0) (THead k v1 t1) H0) in 
((let H4 \def (f_equal T K (\lambda (e: T).(match e in T return (\lambda (_: 
T).K) with [(TSort _) \Rightarrow k0 | (TLRef _) \Rightarrow k0 | (THead k1 _ 
_) \Rightarrow k1])) (THead k0 v0 t0) (THead k v1 t1) H0) in (eq_ind K k 
(\lambda (k1: K).((eq T v0 v1) \to ((eq T t0 t1) \to ((eq T (THead k1 v2 t2) 
u2) \to (ex_2 T T (\lambda (v3: T).(\lambda (t3: T).(eq T u2 (THead k v3 
t3))))))))) (\lambda (H5: (eq T v0 v1)).(eq_ind T v1 (\lambda (_: T).((eq T 
t0 t1) \to ((eq T (THead k v2 t2) u2) \to (ex_2 T T (\lambda (v3: T).(\lambda 
(t3: T).(eq T u2 (THead k v3 t3)))))))) (\lambda (H6: (eq T t0 t1)).(eq_ind T 
t1 (\lambda (_: T).((eq T (THead k v2 t2) u2) \to (ex_2 T T (\lambda (v3: 
T).(\lambda (t3: T).(eq T u2 (THead k v3 t3))))))) (\lambda (H7: (eq T (THead 
k v2 t2) u2)).(eq_ind T (THead k v2 t2) (\lambda (t: T).(ex_2 T T (\lambda 
(v3: T).(\lambda (t3: T).(eq T t (THead k v3 t3)))))) (ex_2_intro T T 
(\lambda (v3: T).(\lambda (t3: T).(eq T (THead k v2 t2) (THead k v3 t3)))) v2 
t2 (refl_equal T (THead k v2 t2))) u2 H7)) t0 (sym_eq T t0 t1 H6))) v0 
(sym_eq T v0 v1 H5))) k0 (sym_eq K k0 k H4))) H3)) H2)) H1)))]) in (H0 
(refl_equal T (THead k v1 t1)) (refl_equal T u2))))))).

theorem iso_refl:
 \forall (t: T).(iso t t)
\def
 \lambda (t: T).(T_ind (\lambda (t0: T).(iso t0 t0)) (\lambda (n: 
nat).(iso_sort n n)) (\lambda (n: nat).(iso_lref n n)) (\lambda (k: 
K).(\lambda (t0: T).(\lambda (_: (iso t0 t0)).(\lambda (t1: T).(\lambda (_: 
(iso t1 t1)).(iso_head t0 t0 t1 t1 k)))))) t).

theorem lifts_tapp:
 \forall (h: nat).(\forall (d: nat).(\forall (v: T).(\forall (vs: TList).(eq 
TList (lifts h d (TApp vs v)) (TApp (lifts h d vs) (lift h d v))))))
\def
 \lambda (h: nat).(\lambda (d: nat).(\lambda (v: T).(\lambda (vs: 
TList).(TList_ind (\lambda (t: TList).(eq TList (lifts h d (TApp t v)) (TApp 
(lifts h d t) (lift h d v)))) (refl_equal TList (TCons (lift h d v) TNil)) 
(\lambda (t: T).(\lambda (t0: TList).(\lambda (H: (eq TList (lifts h d (TApp 
t0 v)) (TApp (lifts h d t0) (lift h d v)))).(eq_ind_r TList (TApp (lifts h d 
t0) (lift h d v)) (\lambda (t1: TList).(eq TList (TCons (lift h d t) t1) 
(TCons (lift h d t) (TApp (lifts h d t0) (lift h d v))))) (refl_equal TList 
(TCons (lift h d t) (TApp (lifts h d t0) (lift h d v)))) (lifts h d (TApp t0 
v)) H)))) vs)))).

theorem pr3_flat:
 \forall (c: C).(\forall (u1: T).(\forall (u2: T).((pr3 c u1 u2) \to (\forall 
(t1: T).(\forall (t2: T).((pr3 c t1 t2) \to (\forall (f: F).(pr3 c (THead 
(Flat f) u1 t1) (THead (Flat f) u2 t2)))))))))
\def
 \lambda (c: C).(\lambda (u1: T).(\lambda (u2: T).(\lambda (H: (pr3 c u1 
u2)).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H0: (pr3 c t1 t2)).(\lambda 
(f: F).(pr3_head_12 c u1 u2 H (Flat f) t1 t2 (pr3_cflat c t1 t2 H0 f 
u2))))))))).

theorem pr3_gen_bind:
 \forall (b: B).((not (eq B b Abst)) \to (\forall (c: C).(\forall (u1: 
T).(\forall (t1: T).(\forall (x: T).((pr3 c (THead (Bind b) u1 t1) x) \to (or 
(ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T x (THead (Bind b) u2 
t2)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c u1 u2))) (\lambda (_: 
T).(\lambda (t2: T).(pr3 (CHead c (Bind b) u1) t1 t2)))) (pr3 (CHead c (Bind 
b) u1) t1 (lift (S O) O x)))))))))
\def
 \lambda (b: B).(match b in B return (\lambda (b0: B).((not (eq B b0 Abst)) 
\to (\forall (c: C).(\forall (u1: T).(\forall (t1: T).(\forall (x: T).((pr3 c 
(THead (Bind b0) u1 t1) x) \to (or (ex3_2 T T (\lambda (u2: T).(\lambda (t2: 
T).(eq T x (THead (Bind b0) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c 
u1 u2))) (\lambda (_: T).(\lambda (t2: T).(pr3 (CHead c (Bind b0) u1) t1 
t2)))) (pr3 (CHead c (Bind b0) u1) t1 (lift (S O) O x)))))))))) with [Abbr 
\Rightarrow (\lambda (_: (not (eq B Abbr Abst))).(\lambda (c: C).(\lambda 
(u1: T).(\lambda (t1: T).(\lambda (x: T).(\lambda (H0: (pr3 c (THead (Bind 
Abbr) u1 t1) x)).(let H1 \def (pr3_gen_abbr c u1 t1 x H0) in (or_ind (ex3_2 T 
T (\lambda (u2: T).(\lambda (t2: T).(eq T x (THead (Bind Abbr) u2 t2)))) 
(\lambda (u2: T).(\lambda (_: T).(pr3 c u1 u2))) (\lambda (_: T).(\lambda 
(t2: T).(pr3 (CHead c (Bind Abbr) u1) t1 t2)))) (pr3 (CHead c (Bind Abbr) u1) 
t1 (lift (S O) O x)) (or (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T x 
(THead (Bind Abbr) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c u1 u2))) 
(\lambda (_: T).(\lambda (t2: T).(pr3 (CHead c (Bind Abbr) u1) t1 t2)))) (pr3 
(CHead c (Bind Abbr) u1) t1 (lift (S O) O x))) (\lambda (H2: (ex3_2 T T 
(\lambda (u2: T).(\lambda (t2: T).(eq T x (THead (Bind Abbr) u2 t2)))) 
(\lambda (u2: T).(\lambda (_: T).(pr3 c u1 u2))) (\lambda (_: T).(\lambda 
(t2: T).(pr3 (CHead c (Bind Abbr) u1) t1 t2))))).(ex3_2_ind T T (\lambda (u2: 
T).(\lambda (t2: T).(eq T x (THead (Bind Abbr) u2 t2)))) (\lambda (u2: 
T).(\lambda (_: T).(pr3 c u1 u2))) (\lambda (_: T).(\lambda (t2: T).(pr3 
(CHead c (Bind Abbr) u1) t1 t2))) (or (ex3_2 T T (\lambda (u2: T).(\lambda 
(t2: T).(eq T x (THead (Bind Abbr) u2 t2)))) (\lambda (u2: T).(\lambda (_: 
T).(pr3 c u1 u2))) (\lambda (_: T).(\lambda (t2: T).(pr3 (CHead c (Bind Abbr) 
u1) t1 t2)))) (pr3 (CHead c (Bind Abbr) u1) t1 (lift (S O) O x))) (\lambda 
(x0: T).(\lambda (x1: T).(\lambda (H3: (eq T x (THead (Bind Abbr) x0 
x1))).(\lambda (H4: (pr3 c u1 x0)).(\lambda (H5: (pr3 (CHead c (Bind Abbr) 
u1) t1 x1)).(or_introl (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T x 
(THead (Bind Abbr) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c u1 u2))) 
(\lambda (_: T).(\lambda (t2: T).(pr3 (CHead c (Bind Abbr) u1) t1 t2)))) (pr3 
(CHead c (Bind Abbr) u1) t1 (lift (S O) O x)) (ex3_2_intro T T (\lambda (u2: 
T).(\lambda (t2: T).(eq T x (THead (Bind Abbr) u2 t2)))) (\lambda (u2: 
T).(\lambda (_: T).(pr3 c u1 u2))) (\lambda (_: T).(\lambda (t2: T).(pr3 
(CHead c (Bind Abbr) u1) t1 t2))) x0 x1 H3 H4 H5))))))) H2)) (\lambda (H2: 
(pr3 (CHead c (Bind Abbr) u1) t1 (lift (S O) O x))).(or_intror (ex3_2 T T 
(\lambda (u2: T).(\lambda (t2: T).(eq T x (THead (Bind Abbr) u2 t2)))) 
(\lambda (u2: T).(\lambda (_: T).(pr3 c u1 u2))) (\lambda (_: T).(\lambda 
(t2: T).(pr3 (CHead c (Bind Abbr) u1) t1 t2)))) (pr3 (CHead c (Bind Abbr) u1) 
t1 (lift (S O) O x)) H2)) H1)))))))) | Abst \Rightarrow (\lambda (H: (not (eq 
B Abst Abst))).(\lambda (c: C).(\lambda (u1: T).(\lambda (t1: T).(\lambda (x: 
T).(\lambda (_: (pr3 c (THead (Bind Abst) u1 t1) x)).(let H1 \def (match (H 
(refl_equal B Abst)) in False return (\lambda (_: False).(or (ex3_2 T T 
(\lambda (u2: T).(\lambda (t2: T).(eq T x (THead (Bind Abst) u2 t2)))) 
(\lambda (u2: T).(\lambda (_: T).(pr3 c u1 u2))) (\lambda (_: T).(\lambda 
(t2: T).(pr3 (CHead c (Bind Abst) u1) t1 t2)))) (pr3 (CHead c (Bind Abst) u1) 
t1 (lift (S O) O x)))) with []) in H1))))))) | Void \Rightarrow (\lambda (_: 
(not (eq B Void Abst))).(\lambda (c: C).(\lambda (u1: T).(\lambda (t1: 
T).(\lambda (x: T).(\lambda (H0: (pr3 c (THead (Bind Void) u1 t1) x)).(let H1 
\def (pr3_gen_void c u1 t1 x H0) in (or_ind (ex3_2 T T (\lambda (u2: 
T).(\lambda (t2: T).(eq T x (THead (Bind Void) u2 t2)))) (\lambda (u2: 
T).(\lambda (_: T).(pr3 c u1 u2))) (\lambda (_: T).(\lambda (t2: T).(\forall 
(b0: B).(\forall (u: T).(pr3 (CHead c (Bind b0) u) t1 t2)))))) (pr3 (CHead c 
(Bind Void) u1) t1 (lift (S O) O x)) (or (ex3_2 T T (\lambda (u2: T).(\lambda 
(t2: T).(eq T x (THead (Bind Void) u2 t2)))) (\lambda (u2: T).(\lambda (_: 
T).(pr3 c u1 u2))) (\lambda (_: T).(\lambda (t2: T).(pr3 (CHead c (Bind Void) 
u1) t1 t2)))) (pr3 (CHead c (Bind Void) u1) t1 (lift (S O) O x))) (\lambda 
(H2: (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T x (THead (Bind Void) 
u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c u1 u2))) (\lambda (_: 
T).(\lambda (t2: T).(\forall (b0: B).(\forall (u: T).(pr3 (CHead c (Bind b0) 
u) t1 t2))))))).(ex3_2_ind T T (\lambda (u2: T).(\lambda (t2: T).(eq T x 
(THead (Bind Void) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c u1 u2))) 
(\lambda (_: T).(\lambda (t2: T).(\forall (b0: B).(\forall (u: T).(pr3 (CHead 
c (Bind b0) u) t1 t2))))) (or (ex3_2 T T (\lambda (u2: T).(\lambda (t2: 
T).(eq T x (THead (Bind Void) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr3 
c u1 u2))) (\lambda (_: T).(\lambda (t2: T).(pr3 (CHead c (Bind Void) u1) t1 
t2)))) (pr3 (CHead c (Bind Void) u1) t1 (lift (S O) O x))) (\lambda (x0: 
T).(\lambda (x1: T).(\lambda (H3: (eq T x (THead (Bind Void) x0 
x1))).(\lambda (H4: (pr3 c u1 x0)).(\lambda (H5: ((\forall (b0: B).(\forall 
(u: T).(pr3 (CHead c (Bind b0) u) t1 x1))))).(or_introl (ex3_2 T T (\lambda 
(u2: T).(\lambda (t2: T).(eq T x (THead (Bind Void) u2 t2)))) (\lambda (u2: 
T).(\lambda (_: T).(pr3 c u1 u2))) (\lambda (_: T).(\lambda (t2: T).(pr3 
(CHead c (Bind Void) u1) t1 t2)))) (pr3 (CHead c (Bind Void) u1) t1 (lift (S 
O) O x)) (ex3_2_intro T T (\lambda (u2: T).(\lambda (t2: T).(eq T x (THead 
(Bind Void) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c u1 u2))) 
(\lambda (_: T).(\lambda (t2: T).(pr3 (CHead c (Bind Void) u1) t1 t2))) x0 x1 
H3 H4 (H5 Void u1)))))))) H2)) (\lambda (H2: (pr3 (CHead c (Bind Void) u1) t1 
(lift (S O) O x))).(or_intror (ex3_2 T T (\lambda (u2: T).(\lambda (t2: 
T).(eq T x (THead (Bind Void) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr3 
c u1 u2))) (\lambda (_: T).(\lambda (t2: T).(pr3 (CHead c (Bind Void) u1) t1 
t2)))) (pr3 (CHead c (Bind Void) u1) t1 (lift (S O) O x)) H2)) H1))))))))]).

theorem pr3_iso_appls_abbr:
 \forall (c: C).(\forall (d: C).(\forall (w: T).(\forall (i: nat).((getl i c 
(CHead d (Bind Abbr) w)) \to (\forall (vs: TList).(let u1 \def (THeads (Flat 
Appl) vs (TLRef i)) in (\forall (u2: T).((pr3 c u1 u2) \to ((((iso u1 u2) \to 
(\forall (P: Prop).P))) \to (pr3 c (THeads (Flat Appl) vs (lift (S i) O w)) 
u2))))))))))
\def
 \lambda (c: C).(\lambda (d: C).(\lambda (w: T).(\lambda (i: nat).(\lambda 
(H: (getl i c (CHead d (Bind Abbr) w))).(\lambda (vs: TList).(TList_ind 
(\lambda (t: TList).(let u1 \def (THeads (Flat Appl) t (TLRef i)) in (\forall 
(u2: T).((pr3 c u1 u2) \to ((((iso u1 u2) \to (\forall (P: Prop).P))) \to 
(pr3 c (THeads (Flat Appl) t (lift (S i) O w)) u2)))))) (\lambda (u2: 
T).(\lambda (H0: (pr3 c (TLRef i) u2)).(\lambda (H1: (((iso (TLRef i) u2) \to 
(\forall (P: Prop).P)))).(let H2 \def (pr3_gen_lref c u2 i H0) in (or_ind (eq 
T u2 (TLRef i)) (ex3_3 C T T (\lambda (d0: C).(\lambda (u: T).(\lambda (_: 
T).(getl i c (CHead d0 (Bind Abbr) u))))) (\lambda (d0: C).(\lambda (u: 
T).(\lambda (v: T).(pr3 d0 u v)))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(v: T).(eq T u2 (lift (S i) O v)))))) (pr3 c (lift (S i) O w) u2) (\lambda 
(H3: (eq T u2 (TLRef i))).(let H4 \def (eq_ind T u2 (\lambda (t: T).((iso 
(TLRef i) t) \to (\forall (P: Prop).P))) H1 (TLRef i) H3) in (eq_ind_r T 
(TLRef i) (\lambda (t: T).(pr3 c (lift (S i) O w) t)) (H4 (iso_refl (TLRef 
i)) (pr3 c (lift (S i) O w) (TLRef i))) u2 H3))) (\lambda (H3: (ex3_3 C T T 
(\lambda (d0: C).(\lambda (u: T).(\lambda (_: T).(getl i c (CHead d0 (Bind 
Abbr) u))))) (\lambda (d0: C).(\lambda (u: T).(\lambda (v: T).(pr3 d0 u v)))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (v: T).(eq T u2 (lift (S i) O 
v))))))).(ex3_3_ind C T T (\lambda (d0: C).(\lambda (u: T).(\lambda (_: 
T).(getl i c (CHead d0 (Bind Abbr) u))))) (\lambda (d0: C).(\lambda (u: 
T).(\lambda (v: T).(pr3 d0 u v)))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(v: T).(eq T u2 (lift (S i) O v))))) (pr3 c (lift (S i) O w) u2) (\lambda 
(x0: C).(\lambda (x1: T).(\lambda (x2: T).(\lambda (H4: (getl i c (CHead x0 
(Bind Abbr) x1))).(\lambda (H5: (pr3 x0 x1 x2)).(\lambda (H6: (eq T u2 (lift 
(S i) O x2))).(let H7 \def (eq_ind T u2 (\lambda (t: T).((iso (TLRef i) t) 
\to (\forall (P: Prop).P))) H1 (lift (S i) O x2) H6) in (eq_ind_r T (lift (S 
i) O x2) (\lambda (t: T).(pr3 c (lift (S i) O w) t)) (let H8 \def (eq_ind C 
(CHead d (Bind Abbr) w) (\lambda (c0: C).(getl i c c0)) H (CHead x0 (Bind 
Abbr) x1) (getl_mono c (CHead d (Bind Abbr) w) i H (CHead x0 (Bind Abbr) x1) 
H4)) in (let H9 \def (f_equal C C (\lambda (e: C).(match e in C return 
(\lambda (_: C).C) with [(CSort _) \Rightarrow d | (CHead c0 _ _) \Rightarrow 
c0])) (CHead d (Bind Abbr) w) (CHead x0 (Bind Abbr) x1) (getl_mono c (CHead d 
(Bind Abbr) w) i H (CHead x0 (Bind Abbr) x1) H4)) in ((let H10 \def (f_equal 
C T (\lambda (e: C).(match e in C return (\lambda (_: C).T) with [(CSort _) 
\Rightarrow w | (CHead _ _ t) \Rightarrow t])) (CHead d (Bind Abbr) w) (CHead 
x0 (Bind Abbr) x1) (getl_mono c (CHead d (Bind Abbr) w) i H (CHead x0 (Bind 
Abbr) x1) H4)) in (\lambda (H11: (eq C d x0)).(let H12 \def (eq_ind_r T x1 
(\lambda (t: T).(getl i c (CHead x0 (Bind Abbr) t))) H8 w H10) in (let H13 
\def (eq_ind_r T x1 (\lambda (t: T).(pr3 x0 t x2)) H5 w H10) in (let H14 \def 
(eq_ind_r C x0 (\lambda (c0: C).(getl i c (CHead c0 (Bind Abbr) w))) H12 d 
H11) in (let H15 \def (eq_ind_r C x0 (\lambda (c0: C).(pr3 c0 w x2)) H13 d 
H11) in (pr3_lift c d (S i) O (getl_drop Abbr c d w i H14) w x2 H15))))))) 
H9))) u2 H6)))))))) H3)) H2))))) (\lambda (t: T).(\lambda (t0: 
TList).(\lambda (H0: ((\forall (u2: T).((pr3 c (THeads (Flat Appl) t0 (TLRef 
i)) u2) \to ((((iso (THeads (Flat Appl) t0 (TLRef i)) u2) \to (\forall (P: 
Prop).P))) \to (pr3 c (THeads (Flat Appl) t0 (lift (S i) O w)) 
u2)))))).(\lambda (u2: T).(\lambda (H1: (pr3 c (THead (Flat Appl) t (THeads 
(Flat Appl) t0 (TLRef i))) u2)).(\lambda (H2: (((iso (THead (Flat Appl) t 
(THeads (Flat Appl) t0 (TLRef i))) u2) \to (\forall (P: Prop).P)))).(let H3 
\def (pr3_gen_appl c t (THeads (Flat Appl) t0 (TLRef i)) u2 H1) in (or3_ind 
(ex3_2 T T (\lambda (u3: T).(\lambda (t2: T).(eq T u2 (THead (Flat Appl) u3 
t2)))) (\lambda (u3: T).(\lambda (_: T).(pr3 c t u3))) (\lambda (_: 
T).(\lambda (t2: T).(pr3 c (THeads (Flat Appl) t0 (TLRef i)) t2)))) (ex4_4 T 
T T T (\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda (t2: T).(pr3 
c (THead (Bind Abbr) u3 t2) u2))))) (\lambda (_: T).(\lambda (_: T).(\lambda 
(u3: T).(\lambda (_: T).(pr3 c t u3))))) (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(pr3 c (THeads (Flat Appl) t0 (TLRef i)) 
(THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t2: T).(\forall (b: B).(\forall (u: T).(pr3 (CHead c (Bind b) u) 
z1 t2)))))))) (ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) 
(\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(pr3 c (THeads (Flat Appl) t0 (TLRef i)) (THead (Bind 
b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(z2: T).(\lambda (u3: T).(\lambda (y2: T).(pr3 c (THead (Bind b) y2 (THead 
(Flat Appl) (lift (S O) O u3) z2)) u2))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda (_: T).(pr3 c t 
u3))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr3 c y1 y2))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr3 (CHead c (Bind b) y2) z1 z2)))))))) (pr3 c (THead (Flat Appl) t 
(THeads (Flat Appl) t0 (lift (S i) O w))) u2) (\lambda (H4: (ex3_2 T T 
(\lambda (u3: T).(\lambda (t2: T).(eq T u2 (THead (Flat Appl) u3 t2)))) 
(\lambda (u3: T).(\lambda (_: T).(pr3 c t u3))) (\lambda (_: T).(\lambda (t2: 
T).(pr3 c (THeads (Flat Appl) t0 (TLRef i)) t2))))).(ex3_2_ind T T (\lambda 
(u3: T).(\lambda (t2: T).(eq T u2 (THead (Flat Appl) u3 t2)))) (\lambda (u3: 
T).(\lambda (_: T).(pr3 c t u3))) (\lambda (_: T).(\lambda (t2: T).(pr3 c 
(THeads (Flat Appl) t0 (TLRef i)) t2))) (pr3 c (THead (Flat Appl) t (THeads 
(Flat Appl) t0 (lift (S i) O w))) u2) (\lambda (x0: T).(\lambda (x1: 
T).(\lambda (H5: (eq T u2 (THead (Flat Appl) x0 x1))).(\lambda (_: (pr3 c t 
x0)).(\lambda (_: (pr3 c (THeads (Flat Appl) t0 (TLRef i)) x1)).(let H8 \def 
(eq_ind T u2 (\lambda (t1: T).((iso (THead (Flat Appl) t (THeads (Flat Appl) 
t0 (TLRef i))) t1) \to (\forall (P: Prop).P))) H2 (THead (Flat Appl) x0 x1) 
H5) in (eq_ind_r T (THead (Flat Appl) x0 x1) (\lambda (t1: T).(pr3 c (THead 
(Flat Appl) t (THeads (Flat Appl) t0 (lift (S i) O w))) t1)) (H8 (iso_head t 
x0 (THeads (Flat Appl) t0 (TLRef i)) x1 (Flat Appl)) (pr3 c (THead (Flat 
Appl) t (THeads (Flat Appl) t0 (lift (S i) O w))) (THead (Flat Appl) x0 x1))) 
u2 H5))))))) H4)) (\lambda (H4: (ex4_4 T T T T (\lambda (_: T).(\lambda (_: 
T).(\lambda (u3: T).(\lambda (t2: T).(pr3 c (THead (Bind Abbr) u3 t2) u2))))) 
(\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda (_: T).(pr3 c t 
u3))))) (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: 
T).(pr3 c (THeads (Flat Appl) t0 (TLRef i)) (THead (Bind Abst) y1 z1)))))) 
(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t2: T).(\forall 
(b: B).(\forall (u: T).(pr3 (CHead c (Bind b) u) z1 t2))))))))).(ex4_4_ind T 
T T T (\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda (t2: T).(pr3 
c (THead (Bind Abbr) u3 t2) u2))))) (\lambda (_: T).(\lambda (_: T).(\lambda 
(u3: T).(\lambda (_: T).(pr3 c t u3))))) (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(pr3 c (THeads (Flat Appl) t0 (TLRef i)) 
(THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t2: T).(\forall (b: B).(\forall (u: T).(pr3 (CHead c (Bind b) u) 
z1 t2))))))) (pr3 c (THead (Flat Appl) t (THeads (Flat Appl) t0 (lift (S i) O 
w))) u2) (\lambda (x0: T).(\lambda (x1: T).(\lambda (x2: T).(\lambda (x3: 
T).(\lambda (H5: (pr3 c (THead (Bind Abbr) x2 x3) u2)).(\lambda (H6: (pr3 c t 
x2)).(\lambda (H7: (pr3 c (THeads (Flat Appl) t0 (TLRef i)) (THead (Bind 
Abst) x0 x1))).(\lambda (H8: ((\forall (b: B).(\forall (u: T).(pr3 (CHead c 
(Bind b) u) x1 x3))))).(pr3_t (THead (Bind Abbr) t x1) (THead (Flat Appl) t 
(THeads (Flat Appl) t0 (lift (S i) O w))) c (pr3_t (THead (Flat Appl) t 
(THead (Bind Abst) x0 x1)) (THead (Flat Appl) t (THeads (Flat Appl) t0 (lift 
(S i) O w))) c (pr3_thin_dx c (THeads (Flat Appl) t0 (lift (S i) O w)) (THead 
(Bind Abst) x0 x1) (H0 (THead (Bind Abst) x0 x1) H7 (\lambda (H9: (iso 
(THeads (Flat Appl) t0 (TLRef i)) (THead (Bind Abst) x0 x1))).(\lambda (P: 
Prop).(iso_flats_lref_bind_false Appl Abst i x0 x1 t0 H9 P)))) t Appl) (THead 
(Bind Abbr) t x1) (pr3_pr2 c (THead (Flat Appl) t (THead (Bind Abst) x0 x1)) 
(THead (Bind Abbr) t x1) (pr2_free c (THead (Flat Appl) t (THead (Bind Abst) 
x0 x1)) (THead (Bind Abbr) t x1) (pr0_beta x0 t t (pr0_refl t) x1 x1 
(pr0_refl x1))))) u2 (pr3_t (THead (Bind Abbr) x2 x3) (THead (Bind Abbr) t 
x1) c (pr3_head_12 c t x2 H6 (Bind Abbr) x1 x3 (H8 Abbr x2)) u2 H5)))))))))) 
H4)) (\lambda (H4: (ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B 
b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(pr3 c (THeads (Flat Appl) t0 (TLRef i)) 
(THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (z2: T).(\lambda (u3: T).(\lambda (y2: T).(pr3 c (THead (Bind b) 
y2 (THead (Flat Appl) (lift (S O) O u3) z2)) u2))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda 
(_: T).(pr3 c t u3))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr3 c y1 y2))))))) 
(\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda 
(_: T).(\lambda (y2: T).(pr3 (CHead c (Bind b) y2) z1 z2))))))))).(ex6_6_ind 
B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(pr3 c (THeads (Flat Appl) t0 (TLRef i)) (THead (Bind b) y1 z1)))))))) 
(\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda 
(u3: T).(\lambda (y2: T).(pr3 c (THead (Bind b) y2 (THead (Flat Appl) (lift 
(S O) O u3) z2)) u2))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u3: T).(\lambda (_: T).(pr3 c t u3))))))) 
(\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (y2: T).(pr3 c y1 y2))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr3 
(CHead c (Bind b) y2) z1 z2))))))) (pr3 c (THead (Flat Appl) t (THeads (Flat 
Appl) t0 (lift (S i) O w))) u2) (\lambda (x0: B).(\lambda (x1: T).(\lambda 
(x2: T).(\lambda (x3: T).(\lambda (x4: T).(\lambda (x5: T).(\lambda (H5: (not 
(eq B x0 Abst))).(\lambda (H6: (pr3 c (THeads (Flat Appl) t0 (TLRef i)) 
(THead (Bind x0) x1 x2))).(\lambda (H7: (pr3 c (THead (Bind x0) x5 (THead 
(Flat Appl) (lift (S O) O x4) x3)) u2)).(\lambda (H8: (pr3 c t x4)).(\lambda 
(H9: (pr3 c x1 x5)).(\lambda (H10: (pr3 (CHead c (Bind x0) x5) x2 x3)).(pr3_t 
(THead (Bind x0) x1 (THead (Flat Appl) (lift (S O) O x4) x2)) (THead (Flat 
Appl) t (THeads (Flat Appl) t0 (lift (S i) O w))) c (pr3_t (THead (Bind x0) 
x1 (THead (Flat Appl) (lift (S O) O t) x2)) (THead (Flat Appl) t (THeads 
(Flat Appl) t0 (lift (S i) O w))) c (pr3_t (THead (Flat Appl) t (THead (Bind 
x0) x1 x2)) (THead (Flat Appl) t (THeads (Flat Appl) t0 (lift (S i) O w))) c 
(pr3_thin_dx c (THeads (Flat Appl) t0 (lift (S i) O w)) (THead (Bind x0) x1 
x2) (H0 (THead (Bind x0) x1 x2) H6 (\lambda (H11: (iso (THeads (Flat Appl) t0 
(TLRef i)) (THead (Bind x0) x1 x2))).(\lambda (P: 
Prop).(iso_flats_lref_bind_false Appl x0 i x1 x2 t0 H11 P)))) t Appl) (THead 
(Bind x0) x1 (THead (Flat Appl) (lift (S O) O t) x2)) (pr3_pr2 c (THead (Flat 
Appl) t (THead (Bind x0) x1 x2)) (THead (Bind x0) x1 (THead (Flat Appl) (lift 
(S O) O t) x2)) (pr2_free c (THead (Flat Appl) t (THead (Bind x0) x1 x2)) 
(THead (Bind x0) x1 (THead (Flat Appl) (lift (S O) O t) x2)) (pr0_upsilon x0 
H5 t t (pr0_refl t) x1 x1 (pr0_refl x1) x2 x2 (pr0_refl x2))))) (THead (Bind 
x0) x1 (THead (Flat Appl) (lift (S O) O x4) x2)) (pr3_head_12 c x1 x1 
(pr3_refl c x1) (Bind x0) (THead (Flat Appl) (lift (S O) O t) x2) (THead 
(Flat Appl) (lift (S O) O x4) x2) (pr3_head_12 (CHead c (Bind x0) x1) (lift 
(S O) O t) (lift (S O) O x4) (pr3_lift (CHead c (Bind x0) x1) c (S O) O 
(drop_drop (Bind x0) O c c (drop_refl c) x1) t x4 H8) (Flat Appl) x2 x2 
(pr3_refl (CHead (CHead c (Bind x0) x1) (Flat Appl) (lift (S O) O x4)) x2)))) 
u2 (pr3_t (THead (Bind x0) x5 (THead (Flat Appl) (lift (S O) O x4) x3)) 
(THead (Bind x0) x1 (THead (Flat Appl) (lift (S O) O x4) x2)) c (pr3_head_12 
c x1 x5 H9 (Bind x0) (THead (Flat Appl) (lift (S O) O x4) x2) (THead (Flat 
Appl) (lift (S O) O x4) x3) (pr3_thin_dx (CHead c (Bind x0) x5) x2 x3 H10 
(lift (S O) O x4) Appl)) u2 H7)))))))))))))) H4)) H3)))))))) vs)))))).

theorem pr3_iso_appl_bind:
 \forall (b: B).((not (eq B b Abst)) \to (\forall (v1: T).(\forall (v2: 
T).(\forall (t: T).(let u1 \def (THead (Flat Appl) v1 (THead (Bind b) v2 t)) 
in (\forall (c: C).(\forall (u2: T).((pr3 c u1 u2) \to ((((iso u1 u2) \to 
(\forall (P: Prop).P))) \to (pr3 c (THead (Bind b) v2 (THead (Flat Appl) 
(lift (S O) O v1) t)) u2))))))))))
\def
 \lambda (b: B).(\lambda (H: (not (eq B b Abst))).(\lambda (v1: T).(\lambda 
(v2: T).(\lambda (t: T).(\lambda (c: C).(\lambda (u2: T).(\lambda (H0: (pr3 c 
(THead (Flat Appl) v1 (THead (Bind b) v2 t)) u2)).(\lambda (H1: (((iso (THead 
(Flat Appl) v1 (THead (Bind b) v2 t)) u2) \to (\forall (P: Prop).P)))).(let 
H2 \def (pr3_gen_appl c v1 (THead (Bind b) v2 t) u2 H0) in (or3_ind (ex3_2 T 
T (\lambda (u3: T).(\lambda (t2: T).(eq T u2 (THead (Flat Appl) u3 t2)))) 
(\lambda (u3: T).(\lambda (_: T).(pr3 c v1 u3))) (\lambda (_: T).(\lambda 
(t2: T).(pr3 c (THead (Bind b) v2 t) t2)))) (ex4_4 T T T T (\lambda (_: 
T).(\lambda (_: T).(\lambda (u3: T).(\lambda (t2: T).(pr3 c (THead (Bind 
Abbr) u3 t2) u2))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u3: 
T).(\lambda (_: T).(pr3 c v1 u3))))) (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(pr3 c (THead (Bind b) v2 t) (THead (Bind 
Abst) y1 z1)))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda 
(t2: T).(\forall (b0: B).(\forall (u: T).(pr3 (CHead c (Bind b0) u) z1 
t2)))))))) (ex6_6 B T T T T T (\lambda (b0: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b0 Abst)))))))) 
(\lambda (b0: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(pr3 c (THead (Bind b) v2 t) (THead (Bind b0) y1 
z1)))))))) (\lambda (b0: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: 
T).(\lambda (u3: T).(\lambda (y2: T).(pr3 c (THead (Bind b0) y2 (THead (Flat 
Appl) (lift (S O) O u3) z2)) u2))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda (_: T).(pr3 c v1 
u3))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr3 c y1 y2))))))) (\lambda (b0: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr3 (CHead c (Bind b0) y2) z1 z2)))))))) (pr3 c (THead (Bind b) v2 
(THead (Flat Appl) (lift (S O) O v1) t)) u2) (\lambda (H3: (ex3_2 T T 
(\lambda (u3: T).(\lambda (t2: T).(eq T u2 (THead (Flat Appl) u3 t2)))) 
(\lambda (u3: T).(\lambda (_: T).(pr3 c v1 u3))) (\lambda (_: T).(\lambda 
(t2: T).(pr3 c (THead (Bind b) v2 t) t2))))).(ex3_2_ind T T (\lambda (u3: 
T).(\lambda (t2: T).(eq T u2 (THead (Flat Appl) u3 t2)))) (\lambda (u3: 
T).(\lambda (_: T).(pr3 c v1 u3))) (\lambda (_: T).(\lambda (t2: T).(pr3 c 
(THead (Bind b) v2 t) t2))) (pr3 c (THead (Bind b) v2 (THead (Flat Appl) 
(lift (S O) O v1) t)) u2) (\lambda (x0: T).(\lambda (x1: T).(\lambda (H4: (eq 
T u2 (THead (Flat Appl) x0 x1))).(\lambda (_: (pr3 c v1 x0)).(\lambda (_: 
(pr3 c (THead (Bind b) v2 t) x1)).(let H7 \def (eq_ind T u2 (\lambda (t0: 
T).((iso (THead (Flat Appl) v1 (THead (Bind b) v2 t)) t0) \to (\forall (P: 
Prop).P))) H1 (THead (Flat Appl) x0 x1) H4) in (eq_ind_r T (THead (Flat Appl) 
x0 x1) (\lambda (t0: T).(pr3 c (THead (Bind b) v2 (THead (Flat Appl) (lift (S 
O) O v1) t)) t0)) (H7 (iso_head v1 x0 (THead (Bind b) v2 t) x1 (Flat Appl)) 
(pr3 c (THead (Bind b) v2 (THead (Flat Appl) (lift (S O) O v1) t)) (THead 
(Flat Appl) x0 x1))) u2 H4))))))) H3)) (\lambda (H3: (ex4_4 T T T T (\lambda 
(_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda (t2: T).(pr3 c (THead (Bind 
Abbr) u3 t2) u2))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u3: 
T).(\lambda (_: T).(pr3 c v1 u3))))) (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(pr3 c (THead (Bind b) v2 t) (THead (Bind 
Abst) y1 z1)))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda 
(t2: T).(\forall (b0: B).(\forall (u: T).(pr3 (CHead c (Bind b0) u) z1 
t2))))))))).(ex4_4_ind T T T T (\lambda (_: T).(\lambda (_: T).(\lambda (u3: 
T).(\lambda (t2: T).(pr3 c (THead (Bind Abbr) u3 t2) u2))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u3: T).(\lambda (_: T).(pr3 c v1 u3))))) 
(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(pr3 c 
(THead (Bind b) v2 t) (THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (t2: T).(\forall (b0: B).(\forall (u: 
T).(pr3 (CHead c (Bind b0) u) z1 t2))))))) (pr3 c (THead (Bind b) v2 (THead 
(Flat Appl) (lift (S O) O v1) t)) u2) (\lambda (x0: T).(\lambda (x1: 
T).(\lambda (x2: T).(\lambda (x3: T).(\lambda (H4: (pr3 c (THead (Bind Abbr) 
x2 x3) u2)).(\lambda (H5: (pr3 c v1 x2)).(\lambda (H6: (pr3 c (THead (Bind b) 
v2 t) (THead (Bind Abst) x0 x1))).(\lambda (H7: ((\forall (b0: B).(\forall 
(u: T).(pr3 (CHead c (Bind b0) u) x1 x3))))).(pr3_t (THead (Bind Abbr) x2 x3) 
(THead (Bind b) v2 (THead (Flat Appl) (lift (S O) O v1) t)) c (let H_x \def 
(pr3_gen_bind b H c v2 t (THead (Bind Abst) x0 x1) H6) in (let H8 \def H_x in 
(or_ind (ex3_2 T T (\lambda (u3: T).(\lambda (t2: T).(eq T (THead (Bind Abst) 
x0 x1) (THead (Bind b) u3 t2)))) (\lambda (u3: T).(\lambda (_: T).(pr3 c v2 
u3))) (\lambda (_: T).(\lambda (t2: T).(pr3 (CHead c (Bind b) v2) t t2)))) 
(pr3 (CHead c (Bind b) v2) t (lift (S O) O (THead (Bind Abst) x0 x1))) (pr3 c 
(THead (Bind b) v2 (THead (Flat Appl) (lift (S O) O v1) t)) (THead (Bind 
Abbr) x2 x3)) (\lambda (H9: (ex3_2 T T (\lambda (u3: T).(\lambda (t2: T).(eq 
T (THead (Bind Abst) x0 x1) (THead (Bind b) u3 t2)))) (\lambda (u3: 
T).(\lambda (_: T).(pr3 c v2 u3))) (\lambda (_: T).(\lambda (t2: T).(pr3 
(CHead c (Bind b) v2) t t2))))).(ex3_2_ind T T (\lambda (u3: T).(\lambda (t2: 
T).(eq T (THead (Bind Abst) x0 x1) (THead (Bind b) u3 t2)))) (\lambda (u3: 
T).(\lambda (_: T).(pr3 c v2 u3))) (\lambda (_: T).(\lambda (t2: T).(pr3 
(CHead c (Bind b) v2) t t2))) (pr3 c (THead (Bind b) v2 (THead (Flat Appl) 
(lift (S O) O v1) t)) (THead (Bind Abbr) x2 x3)) (\lambda (x4: T).(\lambda 
(x5: T).(\lambda (H10: (eq T (THead (Bind Abst) x0 x1) (THead (Bind b) x4 
x5))).(\lambda (H11: (pr3 c v2 x4)).(\lambda (H12: (pr3 (CHead c (Bind b) v2) 
t x5)).(let H13 \def (f_equal T B (\lambda (e: T).(match e in T return 
(\lambda (_: T).B) with [(TSort _) \Rightarrow Abst | (TLRef _) \Rightarrow 
Abst | (THead k _ _) \Rightarrow (match k in K return (\lambda (_: K).B) with 
[(Bind b0) \Rightarrow b0 | (Flat _) \Rightarrow Abst])])) (THead (Bind Abst) 
x0 x1) (THead (Bind b) x4 x5) H10) in ((let H14 \def (f_equal T T (\lambda 
(e: T).(match e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow x0 
| (TLRef _) \Rightarrow x0 | (THead _ t0 _) \Rightarrow t0])) (THead (Bind 
Abst) x0 x1) (THead (Bind b) x4 x5) H10) in ((let H15 \def (f_equal T T 
(\lambda (e: T).(match e in T return (\lambda (_: T).T) with [(TSort _) 
\Rightarrow x1 | (TLRef _) \Rightarrow x1 | (THead _ _ t0) \Rightarrow t0])) 
(THead (Bind Abst) x0 x1) (THead (Bind b) x4 x5) H10) in (\lambda (H16: (eq T 
x0 x4)).(\lambda (H17: (eq B Abst b)).(let H18 \def (eq_ind_r T x5 (\lambda 
(t0: T).(pr3 (CHead c (Bind b) v2) t t0)) H12 x1 H15) in (let H19 \def 
(eq_ind_r T x4 (\lambda (t0: T).(pr3 c v2 t0)) H11 x0 H16) in (let H20 \def 
(eq_ind_r B b (\lambda (b0: B).(pr3 (CHead c (Bind b0) v2) t x1)) H18 Abst 
H17) in (let H21 \def (eq_ind_r B b (\lambda (b0: B).(not (eq B b0 Abst))) H 
Abst H17) in (eq_ind B Abst (\lambda (b0: B).(pr3 c (THead (Bind b0) v2 
(THead (Flat Appl) (lift (S O) O v1) t)) (THead (Bind Abbr) x2 x3))) (let H22 
\def (match (H21 (refl_equal B Abst)) in False return (\lambda (_: 
False).(pr3 c (THead (Bind Abst) v2 (THead (Flat Appl) (lift (S O) O v1) t)) 
(THead (Bind Abbr) x2 x3))) with []) in H22) b H17)))))))) H14)) H13))))))) 
H9)) (\lambda (H9: (pr3 (CHead c (Bind b) v2) t (lift (S O) O (THead (Bind 
Abst) x0 x1)))).(pr3_t (THead (Bind b) v2 (THead (Flat Appl) (lift (S O) O 
x2) (lift (S O) O (THead (Bind Abst) x0 x1)))) (THead (Bind b) v2 (THead 
(Flat Appl) (lift (S O) O v1) t)) c (pr3_head_2 c v2 (THead (Flat Appl) (lift 
(S O) O v1) t) (THead (Flat Appl) (lift (S O) O x2) (lift (S O) O (THead 
(Bind Abst) x0 x1))) (Bind b) (pr3_flat (CHead c (Bind b) v2) (lift (S O) O 
v1) (lift (S O) O x2) (pr3_lift (CHead c (Bind b) v2) c (S O) O (drop_drop 
(Bind b) O c c (drop_refl c) v2) v1 x2 H5) t (lift (S O) O (THead (Bind Abst) 
x0 x1)) H9 Appl)) (THead (Bind Abbr) x2 x3) (eq_ind T (lift (S O) O (THead 
(Flat Appl) x2 (THead (Bind Abst) x0 x1))) (\lambda (t0: T).(pr3 c (THead 
(Bind b) v2 t0) (THead (Bind Abbr) x2 x3))) (pr3_sing c (THead (Bind Abbr) x2 
x1) (THead (Bind b) v2 (lift (S O) O (THead (Flat Appl) x2 (THead (Bind Abst) 
x0 x1)))) (pr2_free c (THead (Bind b) v2 (lift (S O) O (THead (Flat Appl) x2 
(THead (Bind Abst) x0 x1)))) (THead (Bind Abbr) x2 x1) (pr0_zeta b H (THead 
(Flat Appl) x2 (THead (Bind Abst) x0 x1)) (THead (Bind Abbr) x2 x1) (pr0_beta 
x0 x2 x2 (pr0_refl x2) x1 x1 (pr0_refl x1)) v2)) (THead (Bind Abbr) x2 x3) 
(pr3_head_12 c x2 x2 (pr3_refl c x2) (Bind Abbr) x1 x3 (H7 Abbr x2))) (THead 
(Flat Appl) (lift (S O) O x2) (lift (S O) O (THead (Bind Abst) x0 x1))) 
(lift_flat Appl x2 (THead (Bind Abst) x0 x1) (S O) O)))) H8))) u2 H4))))))))) 
H3)) (\lambda (H3: (ex6_6 B T T T T T (\lambda (b0: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B 
b0 Abst)))))))) (\lambda (b0: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(pr3 c (THead (Bind b) v2 t) (THead 
(Bind b0) y1 z1)))))))) (\lambda (b0: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (z2: T).(\lambda (u3: T).(\lambda (y2: T).(pr3 c (THead (Bind b0) 
y2 (THead (Flat Appl) (lift (S O) O u3) z2)) u2))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda 
(_: T).(pr3 c v1 u3))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr3 c y1 y2))))))) 
(\lambda (b0: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda 
(_: T).(\lambda (y2: T).(pr3 (CHead c (Bind b0) y2) z1 z2))))))))).(ex6_6_ind 
B T T T T T (\lambda (b0: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(not (eq B b0 Abst)))))))) (\lambda (b0: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(pr3 c (THead (Bind b) v2 t) (THead (Bind b0) y1 z1)))))))) (\lambda 
(b0: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u3: 
T).(\lambda (y2: T).(pr3 c (THead (Bind b0) y2 (THead (Flat Appl) (lift (S O) 
O u3) z2)) u2))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (u3: T).(\lambda (_: T).(pr3 c v1 u3))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr3 c y1 y2))))))) (\lambda (b0: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr3 (CHead c (Bind b0) 
y2) z1 z2))))))) (pr3 c (THead (Bind b) v2 (THead (Flat Appl) (lift (S O) O 
v1) t)) u2) (\lambda (x0: B).(\lambda (x1: T).(\lambda (x2: T).(\lambda (x3: 
T).(\lambda (x4: T).(\lambda (x5: T).(\lambda (H4: (not (eq B x0 
Abst))).(\lambda (H5: (pr3 c (THead (Bind b) v2 t) (THead (Bind x0) x1 
x2))).(\lambda (H6: (pr3 c (THead (Bind x0) x5 (THead (Flat Appl) (lift (S O) 
O x4) x3)) u2)).(\lambda (H7: (pr3 c v1 x4)).(\lambda (H8: (pr3 c x1 
x5)).(\lambda (H9: (pr3 (CHead c (Bind x0) x5) x2 x3)).(pr3_t (THead (Bind 
x0) x5 (THead (Flat Appl) (lift (S O) O x4) x3)) (THead (Bind b) v2 (THead 
(Flat Appl) (lift (S O) O v1) t)) c (let H_x \def (pr3_gen_bind b H c v2 t 
(THead (Bind x0) x1 x2) H5) in (let H10 \def H_x in (or_ind (ex3_2 T T 
(\lambda (u3: T).(\lambda (t2: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind 
b) u3 t2)))) (\lambda (u3: T).(\lambda (_: T).(pr3 c v2 u3))) (\lambda (_: 
T).(\lambda (t2: T).(pr3 (CHead c (Bind b) v2) t t2)))) (pr3 (CHead c (Bind 
b) v2) t (lift (S O) O (THead (Bind x0) x1 x2))) (pr3 c (THead (Bind b) v2 
(THead (Flat Appl) (lift (S O) O v1) t)) (THead (Bind x0) x5 (THead (Flat 
Appl) (lift (S O) O x4) x3))) (\lambda (H11: (ex3_2 T T (\lambda (u3: 
T).(\lambda (t2: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind b) u3 t2)))) 
(\lambda (u3: T).(\lambda (_: T).(pr3 c v2 u3))) (\lambda (_: T).(\lambda 
(t2: T).(pr3 (CHead c (Bind b) v2) t t2))))).(ex3_2_ind T T (\lambda (u3: 
T).(\lambda (t2: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind b) u3 t2)))) 
(\lambda (u3: T).(\lambda (_: T).(pr3 c v2 u3))) (\lambda (_: T).(\lambda 
(t2: T).(pr3 (CHead c (Bind b) v2) t t2))) (pr3 c (THead (Bind b) v2 (THead 
(Flat Appl) (lift (S O) O v1) t)) (THead (Bind x0) x5 (THead (Flat Appl) 
(lift (S O) O x4) x3))) (\lambda (x6: T).(\lambda (x7: T).(\lambda (H12: (eq 
T (THead (Bind x0) x1 x2) (THead (Bind b) x6 x7))).(\lambda (H13: (pr3 c v2 
x6)).(\lambda (H14: (pr3 (CHead c (Bind b) v2) t x7)).(let H15 \def (f_equal 
T B (\lambda (e: T).(match e in T return (\lambda (_: T).B) with [(TSort _) 
\Rightarrow x0 | (TLRef _) \Rightarrow x0 | (THead k _ _) \Rightarrow (match 
k in K return (\lambda (_: K).B) with [(Bind b0) \Rightarrow b0 | (Flat _) 
\Rightarrow x0])])) (THead (Bind x0) x1 x2) (THead (Bind b) x6 x7) H12) in 
((let H16 \def (f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: 
T).T) with [(TSort _) \Rightarrow x1 | (TLRef _) \Rightarrow x1 | (THead _ t0 
_) \Rightarrow t0])) (THead (Bind x0) x1 x2) (THead (Bind b) x6 x7) H12) in 
((let H17 \def (f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: 
T).T) with [(TSort _) \Rightarrow x2 | (TLRef _) \Rightarrow x2 | (THead _ _ 
t0) \Rightarrow t0])) (THead (Bind x0) x1 x2) (THead (Bind b) x6 x7) H12) in 
(\lambda (H18: (eq T x1 x6)).(\lambda (H19: (eq B x0 b)).(let H20 \def 
(eq_ind_r T x7 (\lambda (t0: T).(pr3 (CHead c (Bind b) v2) t t0)) H14 x2 H17) 
in (let H21 \def (eq_ind_r T x6 (\lambda (t0: T).(pr3 c v2 t0)) H13 x1 H18) 
in (let H22 \def (eq_ind B x0 (\lambda (b0: B).(pr3 (CHead c (Bind b0) x5) x2 
x3)) H9 b H19) in (let H23 \def (eq_ind B x0 (\lambda (b0: B).(not (eq B b0 
Abst))) H4 b H19) in (eq_ind_r B b (\lambda (b0: B).(pr3 c (THead (Bind b) v2 
(THead (Flat Appl) (lift (S O) O v1) t)) (THead (Bind b0) x5 (THead (Flat 
Appl) (lift (S O) O x4) x3)))) (pr3_head_21 c v2 x5 (pr3_t x1 v2 c H21 x5 H8) 
(Bind b) (THead (Flat Appl) (lift (S O) O v1) t) (THead (Flat Appl) (lift (S 
O) O x4) x3) (pr3_flat (CHead c (Bind b) v2) (lift (S O) O v1) (lift (S O) O 
x4) (pr3_lift (CHead c (Bind b) v2) c (S O) O (drop_drop (Bind b) O c c 
(drop_refl c) v2) v1 x4 H7) t x3 (pr3_t x2 t (CHead c (Bind b) v2) H20 x3 
(pr3_pr3_pr3_t c v2 x1 H21 x2 x3 (Bind b) (pr3_pr3_pr3_t c x1 x5 H8 x2 x3 
(Bind b) H22))) Appl)) x0 H19)))))))) H16)) H15))))))) H11)) (\lambda (H11: 
(pr3 (CHead c (Bind b) v2) t (lift (S O) O (THead (Bind x0) x1 x2)))).(pr3_t 
(THead (Bind b) v2 (THead (Flat Appl) (lift (S O) O x4) (lift (S O) O (THead 
(Bind x0) x1 x2)))) (THead (Bind b) v2 (THead (Flat Appl) (lift (S O) O v1) 
t)) c (pr3_head_2 c v2 (THead (Flat Appl) (lift (S O) O v1) t) (THead (Flat 
Appl) (lift (S O) O x4) (lift (S O) O (THead (Bind x0) x1 x2))) (Bind b) 
(pr3_flat (CHead c (Bind b) v2) (lift (S O) O v1) (lift (S O) O x4) (pr3_lift 
(CHead c (Bind b) v2) c (S O) O (drop_drop (Bind b) O c c (drop_refl c) v2) 
v1 x4 H7) t (lift (S O) O (THead (Bind x0) x1 x2)) H11 Appl)) (THead (Bind 
x0) x5 (THead (Flat Appl) (lift (S O) O x4) x3)) (eq_ind T (lift (S O) O 
(THead (Flat Appl) x4 (THead (Bind x0) x1 x2))) (\lambda (t0: T).(pr3 c 
(THead (Bind b) v2 t0) (THead (Bind x0) x5 (THead (Flat Appl) (lift (S O) O 
x4) x3)))) (pr3_sing c (THead (Bind x0) x1 (THead (Flat Appl) (lift (S O) O 
x4) x2)) (THead (Bind b) v2 (lift (S O) O (THead (Flat Appl) x4 (THead (Bind 
x0) x1 x2)))) (pr2_free c (THead (Bind b) v2 (lift (S O) O (THead (Flat Appl) 
x4 (THead (Bind x0) x1 x2)))) (THead (Bind x0) x1 (THead (Flat Appl) (lift (S 
O) O x4) x2)) (pr0_zeta b H (THead (Flat Appl) x4 (THead (Bind x0) x1 x2)) 
(THead (Bind x0) x1 (THead (Flat Appl) (lift (S O) O x4) x2)) (pr0_upsilon x0 
H4 x4 x4 (pr0_refl x4) x1 x1 (pr0_refl x1) x2 x2 (pr0_refl x2)) v2)) (THead 
(Bind x0) x5 (THead (Flat Appl) (lift (S O) O x4) x3)) (pr3_head_12 c x1 x5 
H8 (Bind x0) (THead (Flat Appl) (lift (S O) O x4) x2) (THead (Flat Appl) 
(lift (S O) O x4) x3) (pr3_thin_dx (CHead c (Bind x0) x5) x2 x3 H9 (lift (S 
O) O x4) Appl))) (THead (Flat Appl) (lift (S O) O x4) (lift (S O) O (THead 
(Bind x0) x1 x2))) (lift_flat Appl x4 (THead (Bind x0) x1 x2) (S O) O)))) 
H10))) u2 H6))))))))))))) H3)) H2)))))))))).

theorem pr3_iso_appls_appl_bind:
 \forall (b: B).((not (eq B b Abst)) \to (\forall (v: T).(\forall (u: 
T).(\forall (t: T).(\forall (vs: TList).(let u1 \def (THeads (Flat Appl) vs 
(THead (Flat Appl) v (THead (Bind b) u t))) in (\forall (c: C).(\forall (u2: 
T).((pr3 c u1 u2) \to ((((iso u1 u2) \to (\forall (P: Prop).P))) \to (pr3 c 
(THeads (Flat Appl) vs (THead (Bind b) u (THead (Flat Appl) (lift (S O) O v) 
t))) u2)))))))))))
\def
 \lambda (b: B).(\lambda (H: (not (eq B b Abst))).(\lambda (v: T).(\lambda 
(u: T).(\lambda (t: T).(\lambda (vs: TList).(TList_ind (\lambda (t0: 
TList).(let u1 \def (THeads (Flat Appl) t0 (THead (Flat Appl) v (THead (Bind 
b) u t))) in (\forall (c: C).(\forall (u2: T).((pr3 c u1 u2) \to ((((iso u1 
u2) \to (\forall (P: Prop).P))) \to (pr3 c (THeads (Flat Appl) t0 (THead 
(Bind b) u (THead (Flat Appl) (lift (S O) O v) t))) u2))))))) (\lambda (c: 
C).(\lambda (u2: T).(\lambda (H0: (pr3 c (THead (Flat Appl) v (THead (Bind b) 
u t)) u2)).(\lambda (H1: (((iso (THead (Flat Appl) v (THead (Bind b) u t)) 
u2) \to (\forall (P: Prop).P)))).(pr3_iso_appl_bind b H v u t c u2 H0 H1))))) 
(\lambda (t0: T).(\lambda (t1: TList).(\lambda (H0: ((\forall (c: C).(\forall 
(u2: T).((pr3 c (THeads (Flat Appl) t1 (THead (Flat Appl) v (THead (Bind b) u 
t))) u2) \to ((((iso (THeads (Flat Appl) t1 (THead (Flat Appl) v (THead (Bind 
b) u t))) u2) \to (\forall (P: Prop).P))) \to (pr3 c (THeads (Flat Appl) t1 
(THead (Bind b) u (THead (Flat Appl) (lift (S O) O v) t))) u2))))))).(\lambda 
(c: C).(\lambda (u2: T).(\lambda (H1: (pr3 c (THead (Flat Appl) t0 (THeads 
(Flat Appl) t1 (THead (Flat Appl) v (THead (Bind b) u t)))) u2)).(\lambda 
(H2: (((iso (THead (Flat Appl) t0 (THeads (Flat Appl) t1 (THead (Flat Appl) v 
(THead (Bind b) u t)))) u2) \to (\forall (P: Prop).P)))).(let H3 \def 
(pr3_gen_appl c t0 (THeads (Flat Appl) t1 (THead (Flat Appl) v (THead (Bind 
b) u t))) u2 H1) in (or3_ind (ex3_2 T T (\lambda (u3: T).(\lambda (t2: T).(eq 
T u2 (THead (Flat Appl) u3 t2)))) (\lambda (u3: T).(\lambda (_: T).(pr3 c t0 
u3))) (\lambda (_: T).(\lambda (t2: T).(pr3 c (THeads (Flat Appl) t1 (THead 
(Flat Appl) v (THead (Bind b) u t))) t2)))) (ex4_4 T T T T (\lambda (_: 
T).(\lambda (_: T).(\lambda (u3: T).(\lambda (t2: T).(pr3 c (THead (Bind 
Abbr) u3 t2) u2))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u3: 
T).(\lambda (_: T).(pr3 c t0 u3))))) (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(pr3 c (THeads (Flat Appl) t1 (THead (Flat 
Appl) v (THead (Bind b) u t))) (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t2: T).(\forall (b0: 
B).(\forall (u0: T).(pr3 (CHead c (Bind b0) u0) z1 t2)))))))) (ex6_6 B T T T 
T T (\lambda (b0: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(not (eq B b0 Abst)))))))) (\lambda (b0: B).(\lambda 
(y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(pr3 
c (THeads (Flat Appl) t1 (THead (Flat Appl) v (THead (Bind b) u t))) (THead 
(Bind b0) y1 z1)))))))) (\lambda (b0: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (z2: T).(\lambda (u3: T).(\lambda (y2: T).(pr3 c (THead (Bind b0) 
y2 (THead (Flat Appl) (lift (S O) O u3) z2)) u2))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda 
(_: T).(pr3 c t0 u3))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr3 c y1 y2))))))) 
(\lambda (b0: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda 
(_: T).(\lambda (y2: T).(pr3 (CHead c (Bind b0) y2) z1 z2)))))))) (pr3 c 
(THead (Flat Appl) t0 (THeads (Flat Appl) t1 (THead (Bind b) u (THead (Flat 
Appl) (lift (S O) O v) t)))) u2) (\lambda (H4: (ex3_2 T T (\lambda (u3: 
T).(\lambda (t2: T).(eq T u2 (THead (Flat Appl) u3 t2)))) (\lambda (u3: 
T).(\lambda (_: T).(pr3 c t0 u3))) (\lambda (_: T).(\lambda (t2: T).(pr3 c 
(THeads (Flat Appl) t1 (THead (Flat Appl) v (THead (Bind b) u t))) 
t2))))).(ex3_2_ind T T (\lambda (u3: T).(\lambda (t2: T).(eq T u2 (THead 
(Flat Appl) u3 t2)))) (\lambda (u3: T).(\lambda (_: T).(pr3 c t0 u3))) 
(\lambda (_: T).(\lambda (t2: T).(pr3 c (THeads (Flat Appl) t1 (THead (Flat 
Appl) v (THead (Bind b) u t))) t2))) (pr3 c (THead (Flat Appl) t0 (THeads 
(Flat Appl) t1 (THead (Bind b) u (THead (Flat Appl) (lift (S O) O v) t)))) 
u2) (\lambda (x0: T).(\lambda (x1: T).(\lambda (H5: (eq T u2 (THead (Flat 
Appl) x0 x1))).(\lambda (_: (pr3 c t0 x0)).(\lambda (_: (pr3 c (THeads (Flat 
Appl) t1 (THead (Flat Appl) v (THead (Bind b) u t))) x1)).(let H8 \def 
(eq_ind T u2 (\lambda (t2: T).((iso (THead (Flat Appl) t0 (THeads (Flat Appl) 
t1 (THead (Flat Appl) v (THead (Bind b) u t)))) t2) \to (\forall (P: 
Prop).P))) H2 (THead (Flat Appl) x0 x1) H5) in (eq_ind_r T (THead (Flat Appl) 
x0 x1) (\lambda (t2: T).(pr3 c (THead (Flat Appl) t0 (THeads (Flat Appl) t1 
(THead (Bind b) u (THead (Flat Appl) (lift (S O) O v) t)))) t2)) (H8 
(iso_head t0 x0 (THeads (Flat Appl) t1 (THead (Flat Appl) v (THead (Bind b) u 
t))) x1 (Flat Appl)) (pr3 c (THead (Flat Appl) t0 (THeads (Flat Appl) t1 
(THead (Bind b) u (THead (Flat Appl) (lift (S O) O v) t)))) (THead (Flat 
Appl) x0 x1))) u2 H5))))))) H4)) (\lambda (H4: (ex4_4 T T T T (\lambda (_: 
T).(\lambda (_: T).(\lambda (u3: T).(\lambda (t2: T).(pr3 c (THead (Bind 
Abbr) u3 t2) u2))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u3: 
T).(\lambda (_: T).(pr3 c t0 u3))))) (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(pr3 c (THeads (Flat Appl) t1 (THead (Flat 
Appl) v (THead (Bind b) u t))) (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t2: T).(\forall (b0: 
B).(\forall (u0: T).(pr3 (CHead c (Bind b0) u0) z1 t2))))))))).(ex4_4_ind T T 
T T (\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda (t2: T).(pr3 c 
(THead (Bind Abbr) u3 t2) u2))))) (\lambda (_: T).(\lambda (_: T).(\lambda 
(u3: T).(\lambda (_: T).(pr3 c t0 u3))))) (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(pr3 c (THeads (Flat Appl) t1 (THead (Flat 
Appl) v (THead (Bind b) u t))) (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t2: T).(\forall (b0: 
B).(\forall (u0: T).(pr3 (CHead c (Bind b0) u0) z1 t2))))))) (pr3 c (THead 
(Flat Appl) t0 (THeads (Flat Appl) t1 (THead (Bind b) u (THead (Flat Appl) 
(lift (S O) O v) t)))) u2) (\lambda (x0: T).(\lambda (x1: T).(\lambda (x2: 
T).(\lambda (x3: T).(\lambda (H5: (pr3 c (THead (Bind Abbr) x2 x3) 
u2)).(\lambda (H6: (pr3 c t0 x2)).(\lambda (H7: (pr3 c (THeads (Flat Appl) t1 
(THead (Flat Appl) v (THead (Bind b) u t))) (THead (Bind Abst) x0 
x1))).(\lambda (H8: ((\forall (b0: B).(\forall (u0: T).(pr3 (CHead c (Bind 
b0) u0) x1 x3))))).(pr3_t (THead (Bind Abbr) t0 x1) (THead (Flat Appl) t0 
(THeads (Flat Appl) t1 (THead (Bind b) u (THead (Flat Appl) (lift (S O) O v) 
t)))) c (pr3_t (THead (Flat Appl) t0 (THead (Bind Abst) x0 x1)) (THead (Flat 
Appl) t0 (THeads (Flat Appl) t1 (THead (Bind b) u (THead (Flat Appl) (lift (S 
O) O v) t)))) c (pr3_thin_dx c (THeads (Flat Appl) t1 (THead (Bind b) u 
(THead (Flat Appl) (lift (S O) O v) t))) (THead (Bind Abst) x0 x1) (H0 c 
(THead (Bind Abst) x0 x1) H7 (\lambda (H9: (iso (THeads (Flat Appl) t1 (THead 
(Flat Appl) v (THead (Bind b) u t))) (THead (Bind Abst) x0 x1))).(\lambda (P: 
Prop).(iso_flats_flat_bind_false Appl Appl Abst x0 v x1 (THead (Bind b) u t) 
t1 H9 P)))) t0 Appl) (THead (Bind Abbr) t0 x1) (pr3_pr2 c (THead (Flat Appl) 
t0 (THead (Bind Abst) x0 x1)) (THead (Bind Abbr) t0 x1) (pr2_free c (THead 
(Flat Appl) t0 (THead (Bind Abst) x0 x1)) (THead (Bind Abbr) t0 x1) (pr0_beta 
x0 t0 t0 (pr0_refl t0) x1 x1 (pr0_refl x1))))) u2 (pr3_t (THead (Bind Abbr) 
x2 x3) (THead (Bind Abbr) t0 x1) c (pr3_head_12 c t0 x2 H6 (Bind Abbr) x1 x3 
(H8 Abbr x2)) u2 H5)))))))))) H4)) (\lambda (H4: (ex6_6 B T T T T T (\lambda 
(b0: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b0 Abst)))))))) (\lambda (b0: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(pr3 c 
(THeads (Flat Appl) t1 (THead (Flat Appl) v (THead (Bind b) u t))) (THead 
(Bind b0) y1 z1)))))))) (\lambda (b0: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (z2: T).(\lambda (u3: T).(\lambda (y2: T).(pr3 c (THead (Bind b0) 
y2 (THead (Flat Appl) (lift (S O) O u3) z2)) u2))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda 
(_: T).(pr3 c t0 u3))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr3 c y1 y2))))))) 
(\lambda (b0: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda 
(_: T).(\lambda (y2: T).(pr3 (CHead c (Bind b0) y2) z1 z2))))))))).(ex6_6_ind 
B T T T T T (\lambda (b0: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(not (eq B b0 Abst)))))))) (\lambda (b0: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(pr3 c (THeads (Flat Appl) t1 (THead (Flat Appl) v (THead (Bind b) u 
t))) (THead (Bind b0) y1 z1)))))))) (\lambda (b0: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (z2: T).(\lambda (u3: T).(\lambda (y2: T).(pr3 c (THead (Bind 
b0) y2 (THead (Flat Appl) (lift (S O) O u3) z2)) u2))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda 
(_: T).(pr3 c t0 u3))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr3 c y1 y2))))))) 
(\lambda (b0: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda 
(_: T).(\lambda (y2: T).(pr3 (CHead c (Bind b0) y2) z1 z2))))))) (pr3 c 
(THead (Flat Appl) t0 (THeads (Flat Appl) t1 (THead (Bind b) u (THead (Flat 
Appl) (lift (S O) O v) t)))) u2) (\lambda (x0: B).(\lambda (x1: T).(\lambda 
(x2: T).(\lambda (x3: T).(\lambda (x4: T).(\lambda (x5: T).(\lambda (H5: (not 
(eq B x0 Abst))).(\lambda (H6: (pr3 c (THeads (Flat Appl) t1 (THead (Flat 
Appl) v (THead (Bind b) u t))) (THead (Bind x0) x1 x2))).(\lambda (H7: (pr3 c 
(THead (Bind x0) x5 (THead (Flat Appl) (lift (S O) O x4) x3)) u2)).(\lambda 
(H8: (pr3 c t0 x4)).(\lambda (H9: (pr3 c x1 x5)).(\lambda (H10: (pr3 (CHead c 
(Bind x0) x5) x2 x3)).(pr3_t (THead (Bind x0) x1 (THead (Flat Appl) (lift (S 
O) O x4) x2)) (THead (Flat Appl) t0 (THeads (Flat Appl) t1 (THead (Bind b) u 
(THead (Flat Appl) (lift (S O) O v) t)))) c (pr3_t (THead (Bind x0) x1 (THead 
(Flat Appl) (lift (S O) O t0) x2)) (THead (Flat Appl) t0 (THeads (Flat Appl) 
t1 (THead (Bind b) u (THead (Flat Appl) (lift (S O) O v) t)))) c (pr3_t 
(THead (Flat Appl) t0 (THead (Bind x0) x1 x2)) (THead (Flat Appl) t0 (THeads 
(Flat Appl) t1 (THead (Bind b) u (THead (Flat Appl) (lift (S O) O v) t)))) c 
(pr3_thin_dx c (THeads (Flat Appl) t1 (THead (Bind b) u (THead (Flat Appl) 
(lift (S O) O v) t))) (THead (Bind x0) x1 x2) (H0 c (THead (Bind x0) x1 x2) 
H6 (\lambda (H11: (iso (THeads (Flat Appl) t1 (THead (Flat Appl) v (THead 
(Bind b) u t))) (THead (Bind x0) x1 x2))).(\lambda (P: 
Prop).(iso_flats_flat_bind_false Appl Appl x0 x1 v x2 (THead (Bind b) u t) t1 
H11 P)))) t0 Appl) (THead (Bind x0) x1 (THead (Flat Appl) (lift (S O) O t0) 
x2)) (pr3_pr2 c (THead (Flat Appl) t0 (THead (Bind x0) x1 x2)) (THead (Bind 
x0) x1 (THead (Flat Appl) (lift (S O) O t0) x2)) (pr2_free c (THead (Flat 
Appl) t0 (THead (Bind x0) x1 x2)) (THead (Bind x0) x1 (THead (Flat Appl) 
(lift (S O) O t0) x2)) (pr0_upsilon x0 H5 t0 t0 (pr0_refl t0) x1 x1 (pr0_refl 
x1) x2 x2 (pr0_refl x2))))) (THead (Bind x0) x1 (THead (Flat Appl) (lift (S 
O) O x4) x2)) (pr3_head_12 c x1 x1 (pr3_refl c x1) (Bind x0) (THead (Flat 
Appl) (lift (S O) O t0) x2) (THead (Flat Appl) (lift (S O) O x4) x2) 
(pr3_head_12 (CHead c (Bind x0) x1) (lift (S O) O t0) (lift (S O) O x4) 
(pr3_lift (CHead c (Bind x0) x1) c (S O) O (drop_drop (Bind x0) O c c 
(drop_refl c) x1) t0 x4 H8) (Flat Appl) x2 x2 (pr3_refl (CHead (CHead c (Bind 
x0) x1) (Flat Appl) (lift (S O) O x4)) x2)))) u2 (pr3_t (THead (Bind x0) x5 
(THead (Flat Appl) (lift (S O) O x4) x3)) (THead (Bind x0) x1 (THead (Flat 
Appl) (lift (S O) O x4) x2)) c (pr3_head_12 c x1 x5 H9 (Bind x0) (THead (Flat 
Appl) (lift (S O) O x4) x2) (THead (Flat Appl) (lift (S O) O x4) x3) 
(pr3_thin_dx (CHead c (Bind x0) x5) x2 x3 H10 (lift (S O) O x4) Appl)) u2 
H7)))))))))))))) H4)) H3))))))))) vs)))))).

theorem pr3_iso_appls_bind:
 \forall (b: B).((not (eq B b Abst)) \to (\forall (vs: TList).(\forall (u: 
T).(\forall (t: T).(let u1 \def (THeads (Flat Appl) vs (THead (Bind b) u t)) 
in (\forall (c: C).(\forall (u2: T).((pr3 c u1 u2) \to ((((iso u1 u2) \to 
(\forall (P: Prop).P))) \to (pr3 c (THead (Bind b) u (THeads (Flat Appl) 
(lifts (S O) O vs) t)) u2))))))))))
\def
 \lambda (b: B).(\lambda (H: (not (eq B b Abst))).(\lambda (vs: 
TList).(tlist_ind_rew (\lambda (t: TList).(\forall (u: T).(\forall (t0: 
T).(let u1 \def (THeads (Flat Appl) t (THead (Bind b) u t0)) in (\forall (c: 
C).(\forall (u2: T).((pr3 c u1 u2) \to ((((iso u1 u2) \to (\forall (P: 
Prop).P))) \to (pr3 c (THead (Bind b) u (THeads (Flat Appl) (lifts (S O) O t) 
t0)) u2))))))))) (\lambda (u: T).(\lambda (t: T).(\lambda (c: C).(\lambda 
(u2: T).(\lambda (H0: (pr3 c (THead (Bind b) u t) u2)).(\lambda (_: (((iso 
(THead (Bind b) u t) u2) \to (\forall (P: Prop).P)))).H0)))))) (\lambda (ts: 
TList).(\lambda (t: T).(\lambda (H0: ((\forall (u: T).(\forall (t0: 
T).(\forall (c: C).(\forall (u2: T).((pr3 c (THeads (Flat Appl) ts (THead 
(Bind b) u t0)) u2) \to ((((iso (THeads (Flat Appl) ts (THead (Bind b) u t0)) 
u2) \to (\forall (P: Prop).P))) \to (pr3 c (THead (Bind b) u (THeads (Flat 
Appl) (lifts (S O) O ts) t0)) u2))))))))).(\lambda (u: T).(\lambda (t0: 
T).(\lambda (c: C).(\lambda (u2: T).(\lambda (H1: (pr3 c (THeads (Flat Appl) 
(TApp ts t) (THead (Bind b) u t0)) u2)).(\lambda (H2: (((iso (THeads (Flat 
Appl) (TApp ts t) (THead (Bind b) u t0)) u2) \to (\forall (P: 
Prop).P)))).(eq_ind_r TList (TApp (lifts (S O) O ts) (lift (S O) O t)) 
(\lambda (t1: TList).(pr3 c (THead (Bind b) u (THeads (Flat Appl) t1 t0)) 
u2)) (eq_ind_r T (THeads (Flat Appl) (lifts (S O) O ts) (THead (Flat Appl) 
(lift (S O) O t) t0)) (\lambda (t1: T).(pr3 c (THead (Bind b) u t1) u2)) (let 
H3 \def (eq_ind T (THeads (Flat Appl) (TApp ts t) (THead (Bind b) u t0)) 
(\lambda (t1: T).(pr3 c t1 u2)) H1 (THeads (Flat Appl) ts (THead (Flat Appl) 
t (THead (Bind b) u t0))) (theads_tapp (Flat Appl) ts t (THead (Bind b) u 
t0))) in (let H4 \def (eq_ind T (THeads (Flat Appl) (TApp ts t) (THead (Bind 
b) u t0)) (\lambda (t1: T).((iso t1 u2) \to (\forall (P: Prop).P))) H2 
(THeads (Flat Appl) ts (THead (Flat Appl) t (THead (Bind b) u t0))) 
(theads_tapp (Flat Appl) ts t (THead (Bind b) u t0))) in ((match ts in TList 
return (\lambda (t1: TList).(((\forall (u0: T).(\forall (t2: T).(\forall (c0: 
C).(\forall (u3: T).((pr3 c0 (THeads (Flat Appl) t1 (THead (Bind b) u0 t2)) 
u3) \to ((((iso (THeads (Flat Appl) t1 (THead (Bind b) u0 t2)) u3) \to 
(\forall (P: Prop).P))) \to (pr3 c0 (THead (Bind b) u0 (THeads (Flat Appl) 
(lifts (S O) O t1) t2)) u3)))))))) \to ((pr3 c (THeads (Flat Appl) t1 (THead 
(Flat Appl) t (THead (Bind b) u t0))) u2) \to ((((iso (THeads (Flat Appl) t1 
(THead (Flat Appl) t (THead (Bind b) u t0))) u2) \to (\forall (P: Prop).P))) 
\to (pr3 c (THead (Bind b) u (THeads (Flat Appl) (lifts (S O) O t1) (THead 
(Flat Appl) (lift (S O) O t) t0))) u2))))) with [TNil \Rightarrow (\lambda 
(_: ((\forall (u0: T).(\forall (t1: T).(\forall (c0: C).(\forall (u3: 
T).((pr3 c0 (THeads (Flat Appl) TNil (THead (Bind b) u0 t1)) u3) \to ((((iso 
(THeads (Flat Appl) TNil (THead (Bind b) u0 t1)) u3) \to (\forall (P: 
Prop).P))) \to (pr3 c0 (THead (Bind b) u0 (THeads (Flat Appl) (lifts (S O) O 
TNil) t1)) u3))))))))).(\lambda (H6: (pr3 c (THeads (Flat Appl) TNil (THead 
(Flat Appl) t (THead (Bind b) u t0))) u2)).(\lambda (H7: (((iso (THeads (Flat 
Appl) TNil (THead (Flat Appl) t (THead (Bind b) u t0))) u2) \to (\forall (P: 
Prop).P)))).(pr3_iso_appl_bind b H t u t0 c u2 H6 H7)))) | (TCons t1 t2) 
\Rightarrow (\lambda (H5: ((\forall (u0: T).(\forall (t3: T).(\forall (c0: 
C).(\forall (u3: T).((pr3 c0 (THeads (Flat Appl) (TCons t1 t2) (THead (Bind 
b) u0 t3)) u3) \to ((((iso (THeads (Flat Appl) (TCons t1 t2) (THead (Bind b) 
u0 t3)) u3) \to (\forall (P: Prop).P))) \to (pr3 c0 (THead (Bind b) u0 
(THeads (Flat Appl) (lifts (S O) O (TCons t1 t2)) t3)) u3))))))))).(\lambda 
(H6: (pr3 c (THeads (Flat Appl) (TCons t1 t2) (THead (Flat Appl) t (THead 
(Bind b) u t0))) u2)).(\lambda (H7: (((iso (THeads (Flat Appl) (TCons t1 t2) 
(THead (Flat Appl) t (THead (Bind b) u t0))) u2) \to (\forall (P: 
Prop).P)))).(H5 u (THead (Flat Appl) (lift (S O) O t) t0) c u2 
(pr3_iso_appls_appl_bind b H t u t0 (TCons t1 t2) c u2 H6 H7) (\lambda (H8: 
(iso (THeads (Flat Appl) (TCons t1 t2) (THead (Bind b) u (THead (Flat Appl) 
(lift (S O) O t) t0))) u2)).(\lambda (P: Prop).(H7 (iso_trans (THeads (Flat 
Appl) (TCons t1 t2) (THead (Flat Appl) t (THead (Bind b) u t0))) (THeads 
(Flat Appl) (TCons t1 t2) (THead (Bind b) u (THead (Flat Appl) (lift (S O) O 
t) t0))) (iso_head t1 t1 (THeads (Flat Appl) t2 (THead (Flat Appl) t (THead 
(Bind b) u t0))) (THeads (Flat Appl) t2 (THead (Bind b) u (THead (Flat Appl) 
(lift (S O) O t) t0))) (Flat Appl)) u2 H8) P)))))))]) H0 H3 H4))) (THeads 
(Flat Appl) (TApp (lifts (S O) O ts) (lift (S O) O t)) t0) (theads_tapp (Flat 
Appl) (lifts (S O) O ts) (lift (S O) O t) t0)) (lifts (S O) O (TApp ts t)) 
(lifts_tapp (S O) O t ts))))))))))) vs))).

theorem pr3_iso_beta:
 \forall (v: T).(\forall (w: T).(\forall (t: T).(let u1 \def (THead (Flat 
Appl) v (THead (Bind Abst) w t)) in (\forall (c: C).(\forall (u2: T).((pr3 c 
u1 u2) \to ((((iso u1 u2) \to (\forall (P: Prop).P))) \to (pr3 c (THead (Bind 
Abbr) v t) u2))))))))
\def
 \lambda (v: T).(\lambda (w: T).(\lambda (t: T).(\lambda (c: C).(\lambda (u2: 
T).(\lambda (H: (pr3 c (THead (Flat Appl) v (THead (Bind Abst) w t)) 
u2)).(\lambda (H0: (((iso (THead (Flat Appl) v (THead (Bind Abst) w t)) u2) 
\to (\forall (P: Prop).P)))).(let H1 \def (pr3_gen_appl c v (THead (Bind 
Abst) w t) u2 H) in (or3_ind (ex3_2 T T (\lambda (u3: T).(\lambda (t2: T).(eq 
T u2 (THead (Flat Appl) u3 t2)))) (\lambda (u3: T).(\lambda (_: T).(pr3 c v 
u3))) (\lambda (_: T).(\lambda (t2: T).(pr3 c (THead (Bind Abst) w t) t2)))) 
(ex4_4 T T T T (\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda (t2: 
T).(pr3 c (THead (Bind Abbr) u3 t2) u2))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u3: T).(\lambda (_: T).(pr3 c v u3))))) (\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(pr3 c (THead (Bind Abst) 
w t) (THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (z1: T).(\lambda 
(_: T).(\lambda (t2: T).(\forall (b: B).(\forall (u: T).(pr3 (CHead c (Bind 
b) u) z1 t2)))))))) (ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B 
b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(pr3 c (THead (Bind Abst) w t) (THead 
(Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (z2: T).(\lambda (u3: T).(\lambda (y2: T).(pr3 c (THead (Bind b) 
y2 (THead (Flat Appl) (lift (S O) O u3) z2)) u2))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda 
(_: T).(pr3 c v u3))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr3 c y1 y2))))))) 
(\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda 
(_: T).(\lambda (y2: T).(pr3 (CHead c (Bind b) y2) z1 z2)))))))) (pr3 c 
(THead (Bind Abbr) v t) u2) (\lambda (H2: (ex3_2 T T (\lambda (u3: 
T).(\lambda (t2: T).(eq T u2 (THead (Flat Appl) u3 t2)))) (\lambda (u3: 
T).(\lambda (_: T).(pr3 c v u3))) (\lambda (_: T).(\lambda (t2: T).(pr3 c 
(THead (Bind Abst) w t) t2))))).(ex3_2_ind T T (\lambda (u3: T).(\lambda (t2: 
T).(eq T u2 (THead (Flat Appl) u3 t2)))) (\lambda (u3: T).(\lambda (_: 
T).(pr3 c v u3))) (\lambda (_: T).(\lambda (t2: T).(pr3 c (THead (Bind Abst) 
w t) t2))) (pr3 c (THead (Bind Abbr) v t) u2) (\lambda (x0: T).(\lambda (x1: 
T).(\lambda (H3: (eq T u2 (THead (Flat Appl) x0 x1))).(\lambda (_: (pr3 c v 
x0)).(\lambda (_: (pr3 c (THead (Bind Abst) w t) x1)).(let H6 \def (eq_ind T 
u2 (\lambda (t0: T).((iso (THead (Flat Appl) v (THead (Bind Abst) w t)) t0) 
\to (\forall (P: Prop).P))) H0 (THead (Flat Appl) x0 x1) H3) in (eq_ind_r T 
(THead (Flat Appl) x0 x1) (\lambda (t0: T).(pr3 c (THead (Bind Abbr) v t) 
t0)) (H6 (iso_head v x0 (THead (Bind Abst) w t) x1 (Flat Appl)) (pr3 c (THead 
(Bind Abbr) v t) (THead (Flat Appl) x0 x1))) u2 H3))))))) H2)) (\lambda (H2: 
(ex4_4 T T T T (\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda (t2: 
T).(pr3 c (THead (Bind Abbr) u3 t2) u2))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u3: T).(\lambda (_: T).(pr3 c v u3))))) (\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(pr3 c (THead (Bind Abst) 
w t) (THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (z1: T).(\lambda 
(_: T).(\lambda (t2: T).(\forall (b: B).(\forall (u: T).(pr3 (CHead c (Bind 
b) u) z1 t2))))))))).(ex4_4_ind T T T T (\lambda (_: T).(\lambda (_: 
T).(\lambda (u3: T).(\lambda (t2: T).(pr3 c (THead (Bind Abbr) u3 t2) u2))))) 
(\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda (_: T).(pr3 c v 
u3))))) (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: 
T).(pr3 c (THead (Bind Abst) w t) (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t2: T).(\forall (b: B).(\forall 
(u: T).(pr3 (CHead c (Bind b) u) z1 t2))))))) (pr3 c (THead (Bind Abbr) v t) 
u2) (\lambda (x0: T).(\lambda (x1: T).(\lambda (x2: T).(\lambda (x3: 
T).(\lambda (H3: (pr3 c (THead (Bind Abbr) x2 x3) u2)).(\lambda (H4: (pr3 c v 
x2)).(\lambda (H5: (pr3 c (THead (Bind Abst) w t) (THead (Bind Abst) x0 
x1))).(\lambda (H6: ((\forall (b: B).(\forall (u: T).(pr3 (CHead c (Bind b) 
u) x1 x3))))).(let H7 \def (pr3_gen_abst c w t (THead (Bind Abst) x0 x1) H5) 
in (ex3_2_ind T T (\lambda (u3: T).(\lambda (t2: T).(eq T (THead (Bind Abst) 
x0 x1) (THead (Bind Abst) u3 t2)))) (\lambda (u3: T).(\lambda (_: T).(pr3 c w 
u3))) (\lambda (_: T).(\lambda (t2: T).(\forall (b: B).(\forall (u: T).(pr3 
(CHead c (Bind b) u) t t2))))) (pr3 c (THead (Bind Abbr) v t) u2) (\lambda 
(x4: T).(\lambda (x5: T).(\lambda (H8: (eq T (THead (Bind Abst) x0 x1) (THead 
(Bind Abst) x4 x5))).(\lambda (H9: (pr3 c w x4)).(\lambda (H10: ((\forall (b: 
B).(\forall (u: T).(pr3 (CHead c (Bind b) u) t x5))))).(let H11 \def (f_equal 
T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) with [(TSort _) 
\Rightarrow x0 | (TLRef _) \Rightarrow x0 | (THead _ t0 _) \Rightarrow t0])) 
(THead (Bind Abst) x0 x1) (THead (Bind Abst) x4 x5) H8) in ((let H12 \def 
(f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) with 
[(TSort _) \Rightarrow x1 | (TLRef _) \Rightarrow x1 | (THead _ _ t0) 
\Rightarrow t0])) (THead (Bind Abst) x0 x1) (THead (Bind Abst) x4 x5) H8) in 
(\lambda (H13: (eq T x0 x4)).(let H14 \def (eq_ind_r T x5 (\lambda (t0: 
T).(\forall (b: B).(\forall (u: T).(pr3 (CHead c (Bind b) u) t t0)))) H10 x1 
H12) in (let H15 \def (eq_ind_r T x4 (\lambda (t0: T).(pr3 c w t0)) H9 x0 
H13) in (pr3_t (THead (Bind Abbr) x2 x3) (THead (Bind Abbr) v t) c 
(pr3_head_12 c v x2 H4 (Bind Abbr) t x3 (pr3_t x1 t (CHead c (Bind Abbr) x2) 
(H14 Abbr x2) x3 (H6 Abbr x2))) u2 H3))))) H11))))))) H7)))))))))) H2)) 
(\lambda (H2: (ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) 
(\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(pr3 c (THead (Bind Abst) w t) (THead (Bind b) y1 
z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: 
T).(\lambda (u3: T).(\lambda (y2: T).(pr3 c (THead (Bind b) y2 (THead (Flat 
Appl) (lift (S O) O u3) z2)) u2))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda (_: T).(pr3 c v 
u3))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr3 c y1 y2))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr3 (CHead c (Bind b) y2) z1 z2))))))))).(ex6_6_ind B T T T T T 
(\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(pr3 c 
(THead (Bind Abst) w t) (THead (Bind b) y1 z1)))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u3: T).(\lambda 
(y2: T).(pr3 c (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u3) z2)) 
u2))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u3: T).(\lambda (_: T).(pr3 c v u3))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr3 c y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr3 (CHead c (Bind b) 
y2) z1 z2))))))) (pr3 c (THead (Bind Abbr) v t) u2) (\lambda (x0: B).(\lambda 
(x1: T).(\lambda (x2: T).(\lambda (x3: T).(\lambda (x4: T).(\lambda (x5: 
T).(\lambda (H3: (not (eq B x0 Abst))).(\lambda (H4: (pr3 c (THead (Bind 
Abst) w t) (THead (Bind x0) x1 x2))).(\lambda (H5: (pr3 c (THead (Bind x0) x5 
(THead (Flat Appl) (lift (S O) O x4) x3)) u2)).(\lambda (_: (pr3 c v 
x4)).(\lambda (_: (pr3 c x1 x5)).(\lambda (H8: (pr3 (CHead c (Bind x0) x5) x2 
x3)).(let H9 \def (pr3_gen_abst c w t (THead (Bind x0) x1 x2) H4) in 
(ex3_2_ind T T (\lambda (u3: T).(\lambda (t2: T).(eq T (THead (Bind x0) x1 
x2) (THead (Bind Abst) u3 t2)))) (\lambda (u3: T).(\lambda (_: T).(pr3 c w 
u3))) (\lambda (_: T).(\lambda (t2: T).(\forall (b: B).(\forall (u: T).(pr3 
(CHead c (Bind b) u) t t2))))) (pr3 c (THead (Bind Abbr) v t) u2) (\lambda 
(x6: T).(\lambda (x7: T).(\lambda (H10: (eq T (THead (Bind x0) x1 x2) (THead 
(Bind Abst) x6 x7))).(\lambda (H11: (pr3 c w x6)).(\lambda (H12: ((\forall 
(b: B).(\forall (u: T).(pr3 (CHead c (Bind b) u) t x7))))).(let H13 \def 
(f_equal T B (\lambda (e: T).(match e in T return (\lambda (_: T).B) with 
[(TSort _) \Rightarrow x0 | (TLRef _) \Rightarrow x0 | (THead k _ _) 
\Rightarrow (match k in K return (\lambda (_: K).B) with [(Bind b) 
\Rightarrow b | (Flat _) \Rightarrow x0])])) (THead (Bind x0) x1 x2) (THead 
(Bind Abst) x6 x7) H10) in ((let H14 \def (f_equal T T (\lambda (e: T).(match 
e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow x1 | (TLRef _) 
\Rightarrow x1 | (THead _ t0 _) \Rightarrow t0])) (THead (Bind x0) x1 x2) 
(THead (Bind Abst) x6 x7) H10) in ((let H15 \def (f_equal T T (\lambda (e: 
T).(match e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow x2 | 
(TLRef _) \Rightarrow x2 | (THead _ _ t0) \Rightarrow t0])) (THead (Bind x0) 
x1 x2) (THead (Bind Abst) x6 x7) H10) in (\lambda (H16: (eq T x1 
x6)).(\lambda (H17: (eq B x0 Abst)).(let H18 \def (eq_ind_r T x7 (\lambda 
(t0: T).(\forall (b: B).(\forall (u: T).(pr3 (CHead c (Bind b) u) t t0)))) 
H12 x2 H15) in (let H19 \def (eq_ind_r T x6 (\lambda (t0: T).(pr3 c w t0)) 
H11 x1 H16) in (let H20 \def (eq_ind B x0 (\lambda (b: B).(pr3 (CHead c (Bind 
b) x5) x2 x3)) H8 Abst H17) in (let H21 \def (eq_ind B x0 (\lambda (b: 
B).(pr3 c (THead (Bind b) x5 (THead (Flat Appl) (lift (S O) O x4) x3)) u2)) 
H5 Abst H17) in (let H22 \def (eq_ind B x0 (\lambda (b: B).(not (eq B b 
Abst))) H3 Abst H17) in (let H23 \def (match (H22 (refl_equal B Abst)) in 
False return (\lambda (_: False).(pr3 c (THead (Bind Abbr) v t) u2)) with []) 
in H23))))))))) H14)) H13))))))) H9)))))))))))))) H2)) H1)))))))).

theorem pr3_iso_appls_beta:
 \forall (us: TList).(\forall (v: T).(\forall (w: T).(\forall (t: T).(let u1 
\def (THeads (Flat Appl) us (THead (Flat Appl) v (THead (Bind Abst) w t))) in 
(\forall (c: C).(\forall (u2: T).((pr3 c u1 u2) \to ((((iso u1 u2) \to 
(\forall (P: Prop).P))) \to (pr3 c (THeads (Flat Appl) us (THead (Bind Abbr) 
v t)) u2)))))))))
\def
 \lambda (us: TList).(TList_ind (\lambda (t: TList).(\forall (v: T).(\forall 
(w: T).(\forall (t0: T).(let u1 \def (THeads (Flat Appl) t (THead (Flat Appl) 
v (THead (Bind Abst) w t0))) in (\forall (c: C).(\forall (u2: T).((pr3 c u1 
u2) \to ((((iso u1 u2) \to (\forall (P: Prop).P))) \to (pr3 c (THeads (Flat 
Appl) t (THead (Bind Abbr) v t0)) u2)))))))))) (\lambda (v: T).(\lambda (w: 
T).(\lambda (t: T).(\lambda (c: C).(\lambda (u2: T).(\lambda (H: (pr3 c 
(THead (Flat Appl) v (THead (Bind Abst) w t)) u2)).(\lambda (H0: (((iso 
(THead (Flat Appl) v (THead (Bind Abst) w t)) u2) \to (\forall (P: 
Prop).P)))).(pr3_iso_beta v w t c u2 H H0)))))))) (\lambda (t: T).(\lambda 
(t0: TList).(\lambda (H: ((\forall (v: T).(\forall (w: T).(\forall (t1: 
T).(\forall (c: C).(\forall (u2: T).((pr3 c (THeads (Flat Appl) t0 (THead 
(Flat Appl) v (THead (Bind Abst) w t1))) u2) \to ((((iso (THeads (Flat Appl) 
t0 (THead (Flat Appl) v (THead (Bind Abst) w t1))) u2) \to (\forall (P: 
Prop).P))) \to (pr3 c (THeads (Flat Appl) t0 (THead (Bind Abbr) v t1)) 
u2)))))))))).(\lambda (v: T).(\lambda (w: T).(\lambda (t1: T).(\lambda (c: 
C).(\lambda (u2: T).(\lambda (H0: (pr3 c (THead (Flat Appl) t (THeads (Flat 
Appl) t0 (THead (Flat Appl) v (THead (Bind Abst) w t1)))) u2)).(\lambda (H1: 
(((iso (THead (Flat Appl) t (THeads (Flat Appl) t0 (THead (Flat Appl) v 
(THead (Bind Abst) w t1)))) u2) \to (\forall (P: Prop).P)))).(let H2 \def 
(pr3_gen_appl c t (THeads (Flat Appl) t0 (THead (Flat Appl) v (THead (Bind 
Abst) w t1))) u2 H0) in (or3_ind (ex3_2 T T (\lambda (u3: T).(\lambda (t2: 
T).(eq T u2 (THead (Flat Appl) u3 t2)))) (\lambda (u3: T).(\lambda (_: 
T).(pr3 c t u3))) (\lambda (_: T).(\lambda (t2: T).(pr3 c (THeads (Flat Appl) 
t0 (THead (Flat Appl) v (THead (Bind Abst) w t1))) t2)))) (ex4_4 T T T T 
(\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda (t2: T).(pr3 c 
(THead (Bind Abbr) u3 t2) u2))))) (\lambda (_: T).(\lambda (_: T).(\lambda 
(u3: T).(\lambda (_: T).(pr3 c t u3))))) (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(pr3 c (THeads (Flat Appl) t0 (THead (Flat 
Appl) v (THead (Bind Abst) w t1))) (THead (Bind Abst) y1 z1)))))) (\lambda 
(_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t2: T).(\forall (b: 
B).(\forall (u: T).(pr3 (CHead c (Bind b) u) z1 t2)))))))) (ex6_6 B T T T T T 
(\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(pr3 c 
(THeads (Flat Appl) t0 (THead (Flat Appl) v (THead (Bind Abst) w t1))) (THead 
(Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (z2: T).(\lambda (u3: T).(\lambda (y2: T).(pr3 c (THead (Bind b) 
y2 (THead (Flat Appl) (lift (S O) O u3) z2)) u2))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda 
(_: T).(pr3 c t u3))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr3 c y1 y2))))))) 
(\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda 
(_: T).(\lambda (y2: T).(pr3 (CHead c (Bind b) y2) z1 z2)))))))) (pr3 c 
(THead (Flat Appl) t (THeads (Flat Appl) t0 (THead (Bind Abbr) v t1))) u2) 
(\lambda (H3: (ex3_2 T T (\lambda (u3: T).(\lambda (t2: T).(eq T u2 (THead 
(Flat Appl) u3 t2)))) (\lambda (u3: T).(\lambda (_: T).(pr3 c t u3))) 
(\lambda (_: T).(\lambda (t2: T).(pr3 c (THeads (Flat Appl) t0 (THead (Flat 
Appl) v (THead (Bind Abst) w t1))) t2))))).(ex3_2_ind T T (\lambda (u3: 
T).(\lambda (t2: T).(eq T u2 (THead (Flat Appl) u3 t2)))) (\lambda (u3: 
T).(\lambda (_: T).(pr3 c t u3))) (\lambda (_: T).(\lambda (t2: T).(pr3 c 
(THeads (Flat Appl) t0 (THead (Flat Appl) v (THead (Bind Abst) w t1))) t2))) 
(pr3 c (THead (Flat Appl) t (THeads (Flat Appl) t0 (THead (Bind Abbr) v t1))) 
u2) (\lambda (x0: T).(\lambda (x1: T).(\lambda (H4: (eq T u2 (THead (Flat 
Appl) x0 x1))).(\lambda (_: (pr3 c t x0)).(\lambda (_: (pr3 c (THeads (Flat 
Appl) t0 (THead (Flat Appl) v (THead (Bind Abst) w t1))) x1)).(let H7 \def 
(eq_ind T u2 (\lambda (t2: T).((iso (THead (Flat Appl) t (THeads (Flat Appl) 
t0 (THead (Flat Appl) v (THead (Bind Abst) w t1)))) t2) \to (\forall (P: 
Prop).P))) H1 (THead (Flat Appl) x0 x1) H4) in (eq_ind_r T (THead (Flat Appl) 
x0 x1) (\lambda (t2: T).(pr3 c (THead (Flat Appl) t (THeads (Flat Appl) t0 
(THead (Bind Abbr) v t1))) t2)) (H7 (iso_head t x0 (THeads (Flat Appl) t0 
(THead (Flat Appl) v (THead (Bind Abst) w t1))) x1 (Flat Appl)) (pr3 c (THead 
(Flat Appl) t (THeads (Flat Appl) t0 (THead (Bind Abbr) v t1))) (THead (Flat 
Appl) x0 x1))) u2 H4))))))) H3)) (\lambda (H3: (ex4_4 T T T T (\lambda (_: 
T).(\lambda (_: T).(\lambda (u3: T).(\lambda (t2: T).(pr3 c (THead (Bind 
Abbr) u3 t2) u2))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u3: 
T).(\lambda (_: T).(pr3 c t u3))))) (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(pr3 c (THeads (Flat Appl) t0 (THead (Flat 
Appl) v (THead (Bind Abst) w t1))) (THead (Bind Abst) y1 z1)))))) (\lambda 
(_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t2: T).(\forall (b: 
B).(\forall (u: T).(pr3 (CHead c (Bind b) u) z1 t2))))))))).(ex4_4_ind T T T 
T (\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda (t2: T).(pr3 c 
(THead (Bind Abbr) u3 t2) u2))))) (\lambda (_: T).(\lambda (_: T).(\lambda 
(u3: T).(\lambda (_: T).(pr3 c t u3))))) (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(pr3 c (THeads (Flat Appl) t0 (THead (Flat 
Appl) v (THead (Bind Abst) w t1))) (THead (Bind Abst) y1 z1)))))) (\lambda 
(_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t2: T).(\forall (b: 
B).(\forall (u: T).(pr3 (CHead c (Bind b) u) z1 t2))))))) (pr3 c (THead (Flat 
Appl) t (THeads (Flat Appl) t0 (THead (Bind Abbr) v t1))) u2) (\lambda (x0: 
T).(\lambda (x1: T).(\lambda (x2: T).(\lambda (x3: T).(\lambda (H4: (pr3 c 
(THead (Bind Abbr) x2 x3) u2)).(\lambda (H5: (pr3 c t x2)).(\lambda (H6: (pr3 
c (THeads (Flat Appl) t0 (THead (Flat Appl) v (THead (Bind Abst) w t1))) 
(THead (Bind Abst) x0 x1))).(\lambda (H7: ((\forall (b: B).(\forall (u: 
T).(pr3 (CHead c (Bind b) u) x1 x3))))).(pr3_t (THead (Bind Abbr) t x1) 
(THead (Flat Appl) t (THeads (Flat Appl) t0 (THead (Bind Abbr) v t1))) c 
(pr3_t (THead (Flat Appl) t (THead (Bind Abst) x0 x1)) (THead (Flat Appl) t 
(THeads (Flat Appl) t0 (THead (Bind Abbr) v t1))) c (pr3_thin_dx c (THeads 
(Flat Appl) t0 (THead (Bind Abbr) v t1)) (THead (Bind Abst) x0 x1) (H v w t1 
c (THead (Bind Abst) x0 x1) H6 (\lambda (H8: (iso (THeads (Flat Appl) t0 
(THead (Flat Appl) v (THead (Bind Abst) w t1))) (THead (Bind Abst) x0 
x1))).(\lambda (P: Prop).(iso_flats_flat_bind_false Appl Appl Abst x0 v x1 
(THead (Bind Abst) w t1) t0 H8 P)))) t Appl) (THead (Bind Abbr) t x1) 
(pr3_pr2 c (THead (Flat Appl) t (THead (Bind Abst) x0 x1)) (THead (Bind Abbr) 
t x1) (pr2_free c (THead (Flat Appl) t (THead (Bind Abst) x0 x1)) (THead 
(Bind Abbr) t x1) (pr0_beta x0 t t (pr0_refl t) x1 x1 (pr0_refl x1))))) u2 
(pr3_t (THead (Bind Abbr) x2 x3) (THead (Bind Abbr) t x1) c (pr3_head_12 c t 
x2 H5 (Bind Abbr) x1 x3 (H7 Abbr x2)) u2 H4)))))))))) H3)) (\lambda (H3: 
(ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(pr3 c (THeads (Flat Appl) t0 (THead (Flat Appl) v (THead (Bind Abst) 
w t1))) (THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u3: T).(\lambda (y2: T).(pr3 c 
(THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u3) z2)) u2))))))) 
(\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u3: 
T).(\lambda (_: T).(pr3 c t u3))))))) (\lambda (_: B).(\lambda (y1: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr3 c y1 
y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: 
T).(\lambda (_: T).(\lambda (y2: T).(pr3 (CHead c (Bind b) y2) z1 
z2))))))))).(ex6_6_ind B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b 
Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(pr3 c (THeads (Flat Appl) t0 (THead (Flat 
Appl) v (THead (Bind Abst) w t1))) (THead (Bind b) y1 z1)))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u3: T).(\lambda 
(y2: T).(pr3 c (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u3) z2)) 
u2))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u3: T).(\lambda (_: T).(pr3 c t u3))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr3 c y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr3 (CHead c (Bind b) 
y2) z1 z2))))))) (pr3 c (THead (Flat Appl) t (THeads (Flat Appl) t0 (THead 
(Bind Abbr) v t1))) u2) (\lambda (x0: B).(\lambda (x1: T).(\lambda (x2: 
T).(\lambda (x3: T).(\lambda (x4: T).(\lambda (x5: T).(\lambda (H4: (not (eq 
B x0 Abst))).(\lambda (H5: (pr3 c (THeads (Flat Appl) t0 (THead (Flat Appl) v 
(THead (Bind Abst) w t1))) (THead (Bind x0) x1 x2))).(\lambda (H6: (pr3 c 
(THead (Bind x0) x5 (THead (Flat Appl) (lift (S O) O x4) x3)) u2)).(\lambda 
(H7: (pr3 c t x4)).(\lambda (H8: (pr3 c x1 x5)).(\lambda (H9: (pr3 (CHead c 
(Bind x0) x5) x2 x3)).(pr3_t (THead (Bind x0) x1 (THead (Flat Appl) (lift (S 
O) O x4) x2)) (THead (Flat Appl) t (THeads (Flat Appl) t0 (THead (Bind Abbr) 
v t1))) c (pr3_t (THead (Bind x0) x1 (THead (Flat Appl) (lift (S O) O t) x2)) 
(THead (Flat Appl) t (THeads (Flat Appl) t0 (THead (Bind Abbr) v t1))) c 
(pr3_t (THead (Flat Appl) t (THead (Bind x0) x1 x2)) (THead (Flat Appl) t 
(THeads (Flat Appl) t0 (THead (Bind Abbr) v t1))) c (pr3_thin_dx c (THeads 
(Flat Appl) t0 (THead (Bind Abbr) v t1)) (THead (Bind x0) x1 x2) (H v w t1 c 
(THead (Bind x0) x1 x2) H5 (\lambda (H10: (iso (THeads (Flat Appl) t0 (THead 
(Flat Appl) v (THead (Bind Abst) w t1))) (THead (Bind x0) x1 x2))).(\lambda 
(P: Prop).(iso_flats_flat_bind_false Appl Appl x0 x1 v x2 (THead (Bind Abst) 
w t1) t0 H10 P)))) t Appl) (THead (Bind x0) x1 (THead (Flat Appl) (lift (S O) 
O t) x2)) (pr3_pr2 c (THead (Flat Appl) t (THead (Bind x0) x1 x2)) (THead 
(Bind x0) x1 (THead (Flat Appl) (lift (S O) O t) x2)) (pr2_free c (THead 
(Flat Appl) t (THead (Bind x0) x1 x2)) (THead (Bind x0) x1 (THead (Flat Appl) 
(lift (S O) O t) x2)) (pr0_upsilon x0 H4 t t (pr0_refl t) x1 x1 (pr0_refl x1) 
x2 x2 (pr0_refl x2))))) (THead (Bind x0) x1 (THead (Flat Appl) (lift (S O) O 
x4) x2)) (pr3_head_12 c x1 x1 (pr3_refl c x1) (Bind x0) (THead (Flat Appl) 
(lift (S O) O t) x2) (THead (Flat Appl) (lift (S O) O x4) x2) (pr3_head_12 
(CHead c (Bind x0) x1) (lift (S O) O t) (lift (S O) O x4) (pr3_lift (CHead c 
(Bind x0) x1) c (S O) O (drop_drop (Bind x0) O c c (drop_refl c) x1) t x4 H7) 
(Flat Appl) x2 x2 (pr3_refl (CHead (CHead c (Bind x0) x1) (Flat Appl) (lift 
(S O) O x4)) x2)))) u2 (pr3_t (THead (Bind x0) x5 (THead (Flat Appl) (lift (S 
O) O x4) x3)) (THead (Bind x0) x1 (THead (Flat Appl) (lift (S O) O x4) x2)) c 
(pr3_head_12 c x1 x5 H8 (Bind x0) (THead (Flat Appl) (lift (S O) O x4) x2) 
(THead (Flat Appl) (lift (S O) O x4) x3) (pr3_thin_dx (CHead c (Bind x0) x5) 
x2 x3 H9 (lift (S O) O x4) Appl)) u2 H6)))))))))))))) H3)) H2)))))))))))) us).

theorem csuba_gen_abst_rev:
 \forall (g: G).(\forall (d1: C).(\forall (c: C).(\forall (u: T).((csuba g c 
(CHead d1 (Bind Abst) u)) \to (ex2 C (\lambda (d2: C).(eq C c (CHead d2 (Bind 
Abst) u))) (\lambda (d2: C).(csuba g d2 d1)))))))
\def
 \lambda (g: G).(\lambda (d1: C).(\lambda (c: C).(\lambda (u: T).(\lambda (H: 
(csuba g c (CHead d1 (Bind Abst) u))).(let H0 \def (match H in csuba return 
(\lambda (c0: C).(\lambda (c1: C).(\lambda (_: (csuba ? c0 c1)).((eq C c0 c) 
\to ((eq C c1 (CHead d1 (Bind Abst) u)) \to (ex2 C (\lambda (d2: C).(eq C c 
(CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1)))))))) with 
[(csuba_sort n) \Rightarrow (\lambda (H0: (eq C (CSort n) c)).(\lambda (H1: 
(eq C (CSort n) (CHead d1 (Bind Abst) u))).(eq_ind C (CSort n) (\lambda (c0: 
C).((eq C (CSort n) (CHead d1 (Bind Abst) u)) \to (ex2 C (\lambda (d2: C).(eq 
C c0 (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1))))) (\lambda 
(H2: (eq C (CSort n) (CHead d1 (Bind Abst) u))).(let H3 \def (eq_ind C (CSort 
n) (\lambda (e: C).(match e in C return (\lambda (_: C).Prop) with [(CSort _) 
\Rightarrow True | (CHead _ _ _) \Rightarrow False])) I (CHead d1 (Bind Abst) 
u) H2) in (False_ind (ex2 C (\lambda (d2: C).(eq C (CSort n) (CHead d2 (Bind 
Abst) u))) (\lambda (d2: C).(csuba g d2 d1))) H3))) c H0 H1))) | (csuba_head 
c1 c2 H0 k u0) \Rightarrow (\lambda (H1: (eq C (CHead c1 k u0) c)).(\lambda 
(H2: (eq C (CHead c2 k u0) (CHead d1 (Bind Abst) u))).(eq_ind C (CHead c1 k 
u0) (\lambda (c0: C).((eq C (CHead c2 k u0) (CHead d1 (Bind Abst) u)) \to 
((csuba g c1 c2) \to (ex2 C (\lambda (d2: C).(eq C c0 (CHead d2 (Bind Abst) 
u))) (\lambda (d2: C).(csuba g d2 d1)))))) (\lambda (H3: (eq C (CHead c2 k 
u0) (CHead d1 (Bind Abst) u))).(let H4 \def (f_equal C T (\lambda (e: 
C).(match e in C return (\lambda (_: C).T) with [(CSort _) \Rightarrow u0 | 
(CHead _ _ t) \Rightarrow t])) (CHead c2 k u0) (CHead d1 (Bind Abst) u) H3) 
in ((let H5 \def (f_equal C K (\lambda (e: C).(match e in C return (\lambda 
(_: C).K) with [(CSort _) \Rightarrow k | (CHead _ k0 _) \Rightarrow k0])) 
(CHead c2 k u0) (CHead d1 (Bind Abst) u) H3) in ((let H6 \def (f_equal C C 
(\lambda (e: C).(match e in C return (\lambda (_: C).C) with [(CSort _) 
\Rightarrow c2 | (CHead c0 _ _) \Rightarrow c0])) (CHead c2 k u0) (CHead d1 
(Bind Abst) u) H3) in (eq_ind C d1 (\lambda (c0: C).((eq K k (Bind Abst)) \to 
((eq T u0 u) \to ((csuba g c1 c0) \to (ex2 C (\lambda (d2: C).(eq C (CHead c1 
k u0) (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1))))))) 
(\lambda (H7: (eq K k (Bind Abst))).(eq_ind K (Bind Abst) (\lambda (k0: 
K).((eq T u0 u) \to ((csuba g c1 d1) \to (ex2 C (\lambda (d2: C).(eq C (CHead 
c1 k0 u0) (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1)))))) 
(\lambda (H8: (eq T u0 u)).(eq_ind T u (\lambda (t: T).((csuba g c1 d1) \to 
(ex2 C (\lambda (d2: C).(eq C (CHead c1 (Bind Abst) t) (CHead d2 (Bind Abst) 
u))) (\lambda (d2: C).(csuba g d2 d1))))) (\lambda (H9: (csuba g c1 
d1)).(ex_intro2 C (\lambda (d2: C).(eq C (CHead c1 (Bind Abst) u) (CHead d2 
(Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1)) c1 (refl_equal C (CHead c1 
(Bind Abst) u)) H9)) u0 (sym_eq T u0 u H8))) k (sym_eq K k (Bind Abst) H7))) 
c2 (sym_eq C c2 d1 H6))) H5)) H4))) c H1 H2 H0))) | (csuba_abst c1 c2 H0 t a 
H1 u0 H2) \Rightarrow (\lambda (H3: (eq C (CHead c1 (Bind Abst) t) 
c)).(\lambda (H4: (eq C (CHead c2 (Bind Abbr) u0) (CHead d1 (Bind Abst) 
u))).(eq_ind C (CHead c1 (Bind Abst) t) (\lambda (c0: C).((eq C (CHead c2 
(Bind Abbr) u0) (CHead d1 (Bind Abst) u)) \to ((csuba g c1 c2) \to ((arity g 
c1 t (asucc g a)) \to ((arity g c2 u0 a) \to (ex2 C (\lambda (d2: C).(eq C c0 
(CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1)))))))) (\lambda 
(H5: (eq C (CHead c2 (Bind Abbr) u0) (CHead d1 (Bind Abst) u))).(let H6 \def 
(eq_ind C (CHead c2 (Bind Abbr) u0) (\lambda (e: C).(match e in C return 
(\lambda (_: C).Prop) with [(CSort _) \Rightarrow False | (CHead _ k _) 
\Rightarrow (match k in K return (\lambda (_: K).Prop) with [(Bind b) 
\Rightarrow (match b in B return (\lambda (_: B).Prop) with [Abbr \Rightarrow 
True | Abst \Rightarrow False | Void \Rightarrow False]) | (Flat _) 
\Rightarrow False])])) I (CHead d1 (Bind Abst) u) H5) in (False_ind ((csuba g 
c1 c2) \to ((arity g c1 t (asucc g a)) \to ((arity g c2 u0 a) \to (ex2 C 
(\lambda (d2: C).(eq C (CHead c1 (Bind Abst) t) (CHead d2 (Bind Abst) u))) 
(\lambda (d2: C).(csuba g d2 d1)))))) H6))) c H3 H4 H0 H1 H2)))]) in (H0 
(refl_equal C c) (refl_equal C (CHead d1 (Bind Abst) u)))))))).

theorem csuba_gen_void_rev:
 \forall (g: G).(\forall (d1: C).(\forall (c: C).(\forall (u: T).((csuba g c 
(CHead d1 (Bind Void) u)) \to (ex2 C (\lambda (d2: C).(eq C c (CHead d2 (Bind 
Void) u))) (\lambda (d2: C).(csuba g d2 d1)))))))
\def
 \lambda (g: G).(\lambda (d1: C).(\lambda (c: C).(\lambda (u: T).(\lambda (H: 
(csuba g c (CHead d1 (Bind Void) u))).(let H0 \def (match H in csuba return 
(\lambda (c0: C).(\lambda (c1: C).(\lambda (_: (csuba ? c0 c1)).((eq C c0 c) 
\to ((eq C c1 (CHead d1 (Bind Void) u)) \to (ex2 C (\lambda (d2: C).(eq C c 
(CHead d2 (Bind Void) u))) (\lambda (d2: C).(csuba g d2 d1)))))))) with 
[(csuba_sort n) \Rightarrow (\lambda (H0: (eq C (CSort n) c)).(\lambda (H1: 
(eq C (CSort n) (CHead d1 (Bind Void) u))).(eq_ind C (CSort n) (\lambda (c0: 
C).((eq C (CSort n) (CHead d1 (Bind Void) u)) \to (ex2 C (\lambda (d2: C).(eq 
C c0 (CHead d2 (Bind Void) u))) (\lambda (d2: C).(csuba g d2 d1))))) (\lambda 
(H2: (eq C (CSort n) (CHead d1 (Bind Void) u))).(let H3 \def (eq_ind C (CSort 
n) (\lambda (e: C).(match e in C return (\lambda (_: C).Prop) with [(CSort _) 
\Rightarrow True | (CHead _ _ _) \Rightarrow False])) I (CHead d1 (Bind Void) 
u) H2) in (False_ind (ex2 C (\lambda (d2: C).(eq C (CSort n) (CHead d2 (Bind 
Void) u))) (\lambda (d2: C).(csuba g d2 d1))) H3))) c H0 H1))) | (csuba_head 
c1 c2 H0 k u0) \Rightarrow (\lambda (H1: (eq C (CHead c1 k u0) c)).(\lambda 
(H2: (eq C (CHead c2 k u0) (CHead d1 (Bind Void) u))).(eq_ind C (CHead c1 k 
u0) (\lambda (c0: C).((eq C (CHead c2 k u0) (CHead d1 (Bind Void) u)) \to 
((csuba g c1 c2) \to (ex2 C (\lambda (d2: C).(eq C c0 (CHead d2 (Bind Void) 
u))) (\lambda (d2: C).(csuba g d2 d1)))))) (\lambda (H3: (eq C (CHead c2 k 
u0) (CHead d1 (Bind Void) u))).(let H4 \def (f_equal C T (\lambda (e: 
C).(match e in C return (\lambda (_: C).T) with [(CSort _) \Rightarrow u0 | 
(CHead _ _ t) \Rightarrow t])) (CHead c2 k u0) (CHead d1 (Bind Void) u) H3) 
in ((let H5 \def (f_equal C K (\lambda (e: C).(match e in C return (\lambda 
(_: C).K) with [(CSort _) \Rightarrow k | (CHead _ k0 _) \Rightarrow k0])) 
(CHead c2 k u0) (CHead d1 (Bind Void) u) H3) in ((let H6 \def (f_equal C C 
(\lambda (e: C).(match e in C return (\lambda (_: C).C) with [(CSort _) 
\Rightarrow c2 | (CHead c0 _ _) \Rightarrow c0])) (CHead c2 k u0) (CHead d1 
(Bind Void) u) H3) in (eq_ind C d1 (\lambda (c0: C).((eq K k (Bind Void)) \to 
((eq T u0 u) \to ((csuba g c1 c0) \to (ex2 C (\lambda (d2: C).(eq C (CHead c1 
k u0) (CHead d2 (Bind Void) u))) (\lambda (d2: C).(csuba g d2 d1))))))) 
(\lambda (H7: (eq K k (Bind Void))).(eq_ind K (Bind Void) (\lambda (k0: 
K).((eq T u0 u) \to ((csuba g c1 d1) \to (ex2 C (\lambda (d2: C).(eq C (CHead 
c1 k0 u0) (CHead d2 (Bind Void) u))) (\lambda (d2: C).(csuba g d2 d1)))))) 
(\lambda (H8: (eq T u0 u)).(eq_ind T u (\lambda (t: T).((csuba g c1 d1) \to 
(ex2 C (\lambda (d2: C).(eq C (CHead c1 (Bind Void) t) (CHead d2 (Bind Void) 
u))) (\lambda (d2: C).(csuba g d2 d1))))) (\lambda (H9: (csuba g c1 
d1)).(ex_intro2 C (\lambda (d2: C).(eq C (CHead c1 (Bind Void) u) (CHead d2 
(Bind Void) u))) (\lambda (d2: C).(csuba g d2 d1)) c1 (refl_equal C (CHead c1 
(Bind Void) u)) H9)) u0 (sym_eq T u0 u H8))) k (sym_eq K k (Bind Void) H7))) 
c2 (sym_eq C c2 d1 H6))) H5)) H4))) c H1 H2 H0))) | (csuba_abst c1 c2 H0 t a 
H1 u0 H2) \Rightarrow (\lambda (H3: (eq C (CHead c1 (Bind Abst) t) 
c)).(\lambda (H4: (eq C (CHead c2 (Bind Abbr) u0) (CHead d1 (Bind Void) 
u))).(eq_ind C (CHead c1 (Bind Abst) t) (\lambda (c0: C).((eq C (CHead c2 
(Bind Abbr) u0) (CHead d1 (Bind Void) u)) \to ((csuba g c1 c2) \to ((arity g 
c1 t (asucc g a)) \to ((arity g c2 u0 a) \to (ex2 C (\lambda (d2: C).(eq C c0 
(CHead d2 (Bind Void) u))) (\lambda (d2: C).(csuba g d2 d1)))))))) (\lambda 
(H5: (eq C (CHead c2 (Bind Abbr) u0) (CHead d1 (Bind Void) u))).(let H6 \def 
(eq_ind C (CHead c2 (Bind Abbr) u0) (\lambda (e: C).(match e in C return 
(\lambda (_: C).Prop) with [(CSort _) \Rightarrow False | (CHead _ k _) 
\Rightarrow (match k in K return (\lambda (_: K).Prop) with [(Bind b) 
\Rightarrow (match b in B return (\lambda (_: B).Prop) with [Abbr \Rightarrow 
True | Abst \Rightarrow False | Void \Rightarrow False]) | (Flat _) 
\Rightarrow False])])) I (CHead d1 (Bind Void) u) H5) in (False_ind ((csuba g 
c1 c2) \to ((arity g c1 t (asucc g a)) \to ((arity g c2 u0 a) \to (ex2 C 
(\lambda (d2: C).(eq C (CHead c1 (Bind Abst) t) (CHead d2 (Bind Void) u))) 
(\lambda (d2: C).(csuba g d2 d1)))))) H6))) c H3 H4 H0 H1 H2)))]) in (H0 
(refl_equal C c) (refl_equal C (CHead d1 (Bind Void) u)))))))).

theorem csuba_gen_abbr_rev:
 \forall (g: G).(\forall (d1: C).(\forall (c: C).(\forall (u1: T).((csuba g c 
(CHead d1 (Bind Abbr) u1)) \to (or (ex2 C (\lambda (d2: C).(eq C c (CHead d2 
(Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (_: A).(eq C c (CHead d2 (Bind Abst) 
u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g 
a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 
a))))))))))
\def
 \lambda (g: G).(\lambda (d1: C).(\lambda (c: C).(\lambda (u1: T).(\lambda 
(H: (csuba g c (CHead d1 (Bind Abbr) u1))).(let H0 \def (match H in csuba 
return (\lambda (c0: C).(\lambda (c1: C).(\lambda (_: (csuba ? c0 c1)).((eq C 
c0 c) \to ((eq C c1 (CHead d1 (Bind Abbr) u1)) \to (or (ex2 C (\lambda (d2: 
C).(eq C c (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) 
(ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(eq C c (CHead 
d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: 
A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a))))))))))) with [(csuba_sort n) \Rightarrow (\lambda 
(H0: (eq C (CSort n) c)).(\lambda (H1: (eq C (CSort n) (CHead d1 (Bind Abbr) 
u1))).(eq_ind C (CSort n) (\lambda (c0: C).((eq C (CSort n) (CHead d1 (Bind 
Abbr) u1)) \to (or (ex2 C (\lambda (d2: C).(eq C c0 (CHead d2 (Bind Abbr) 
u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(eq C c0 (CHead d2 (Bind Abst) u2))))) 
(\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a)))))))) 
(\lambda (H2: (eq C (CSort n) (CHead d1 (Bind Abbr) u1))).(let H3 \def 
(eq_ind C (CSort n) (\lambda (e: C).(match e in C return (\lambda (_: 
C).Prop) with [(CSort _) \Rightarrow True | (CHead _ _ _) \Rightarrow 
False])) I (CHead d1 (Bind Abbr) u1) H2) in (False_ind (or (ex2 C (\lambda 
(d2: C).(eq C (CSort n) (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g 
d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(eq C 
(CSort n) (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda 
(_: T).(\lambda (a: A).(arity g d1 u1 a)))))) H3))) c H0 H1))) | (csuba_head 
c1 c2 H0 k u) \Rightarrow (\lambda (H1: (eq C (CHead c1 k u) c)).(\lambda 
(H2: (eq C (CHead c2 k u) (CHead d1 (Bind Abbr) u1))).(eq_ind C (CHead c1 k 
u) (\lambda (c0: C).((eq C (CHead c2 k u) (CHead d1 (Bind Abbr) u1)) \to 
((csuba g c1 c2) \to (or (ex2 C (\lambda (d2: C).(eq C c0 (CHead d2 (Bind 
Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(eq C c0 (CHead d2 (Bind Abst) u2))))) 
(\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a))))))))) 
(\lambda (H3: (eq C (CHead c2 k u) (CHead d1 (Bind Abbr) u1))).(let H4 \def 
(f_equal C T (\lambda (e: C).(match e in C return (\lambda (_: C).T) with 
[(CSort _) \Rightarrow u | (CHead _ _ t) \Rightarrow t])) (CHead c2 k u) 
(CHead d1 (Bind Abbr) u1) H3) in ((let H5 \def (f_equal C K (\lambda (e: 
C).(match e in C return (\lambda (_: C).K) with [(CSort _) \Rightarrow k | 
(CHead _ k0 _) \Rightarrow k0])) (CHead c2 k u) (CHead d1 (Bind Abbr) u1) H3) 
in ((let H6 \def (f_equal C C (\lambda (e: C).(match e in C return (\lambda 
(_: C).C) with [(CSort _) \Rightarrow c2 | (CHead c0 _ _) \Rightarrow c0])) 
(CHead c2 k u) (CHead d1 (Bind Abbr) u1) H3) in (eq_ind C d1 (\lambda (c0: 
C).((eq K k (Bind Abbr)) \to ((eq T u u1) \to ((csuba g c1 c0) \to (or (ex2 C 
(\lambda (d2: C).(eq C (CHead c1 k u) (CHead d2 (Bind Abbr) u1))) (\lambda 
(d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (_: A).(eq C (CHead c1 k u) (CHead d2 (Bind Abst) u2))))) 
(\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a)))))))))) 
(\lambda (H7: (eq K k (Bind Abbr))).(eq_ind K (Bind Abbr) (\lambda (k0: 
K).((eq T u u1) \to ((csuba g c1 d1) \to (or (ex2 C (\lambda (d2: C).(eq C 
(CHead c1 k0 u) (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 
d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(eq C 
(CHead c1 k0 u) (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda 
(_: T).(\lambda (a: A).(arity g d1 u1 a))))))))) (\lambda (H8: (eq T u 
u1)).(eq_ind T u1 (\lambda (t: T).((csuba g c1 d1) \to (or (ex2 C (\lambda 
(d2: C).(eq C (CHead c1 (Bind Abbr) t) (CHead d2 (Bind Abbr) u1))) (\lambda 
(d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (_: A).(eq C (CHead c1 (Bind Abbr) t) (CHead d2 (Bind Abst) 
u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g 
a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 
a)))))))) (\lambda (H9: (csuba g c1 d1)).(or_introl (ex2 C (\lambda (d2: 
C).(eq C (CHead c1 (Bind Abbr) u1) (CHead d2 (Bind Abbr) u1))) (\lambda (d2: 
C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda 
(_: A).(eq C (CHead c1 (Bind Abbr) u1) (CHead d2 (Bind Abst) u2))))) (\lambda 
(d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a))))) (ex_intro2 C 
(\lambda (d2: C).(eq C (CHead c1 (Bind Abbr) u1) (CHead d2 (Bind Abbr) u1))) 
(\lambda (d2: C).(csuba g d2 d1)) c1 (refl_equal C (CHead c1 (Bind Abbr) u1)) 
H9))) u (sym_eq T u u1 H8))) k (sym_eq K k (Bind Abbr) H7))) c2 (sym_eq C c2 
d1 H6))) H5)) H4))) c H1 H2 H0))) | (csuba_abst c1 c2 H0 t a H1 u H2) 
\Rightarrow (\lambda (H3: (eq C (CHead c1 (Bind Abst) t) c)).(\lambda (H4: 
(eq C (CHead c2 (Bind Abbr) u) (CHead d1 (Bind Abbr) u1))).(eq_ind C (CHead 
c1 (Bind Abst) t) (\lambda (c0: C).((eq C (CHead c2 (Bind Abbr) u) (CHead d1 
(Bind Abbr) u1)) \to ((csuba g c1 c2) \to ((arity g c1 t (asucc g a)) \to 
((arity g c2 u a) \to (or (ex2 C (\lambda (d2: C).(eq C c0 (CHead d2 (Bind 
Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(eq C c0 (CHead d2 (Bind Abst) u2))))) 
(\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a0: A).(arity g d2 u2 (asucc g a0))))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (a0: A).(arity g d1 u1 a0))))))))))) 
(\lambda (H5: (eq C (CHead c2 (Bind Abbr) u) (CHead d1 (Bind Abbr) u1))).(let 
H6 \def (f_equal C T (\lambda (e: C).(match e in C return (\lambda (_: C).T) 
with [(CSort _) \Rightarrow u | (CHead _ _ t0) \Rightarrow t0])) (CHead c2 
(Bind Abbr) u) (CHead d1 (Bind Abbr) u1) H5) in ((let H7 \def (f_equal C C 
(\lambda (e: C).(match e in C return (\lambda (_: C).C) with [(CSort _) 
\Rightarrow c2 | (CHead c0 _ _) \Rightarrow c0])) (CHead c2 (Bind Abbr) u) 
(CHead d1 (Bind Abbr) u1) H5) in (eq_ind C d1 (\lambda (c0: C).((eq T u u1) 
\to ((csuba g c1 c0) \to ((arity g c1 t (asucc g a)) \to ((arity g c0 u a) 
\to (or (ex2 C (\lambda (d2: C).(eq C (CHead c1 (Bind Abst) t) (CHead d2 
(Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (_: A).(eq C (CHead c1 (Bind Abst) t) 
(CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: 
A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a0: 
A).(arity g d2 u2 (asucc g a0))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a0: A).(arity g d1 u1 a0))))))))))) (\lambda (H8: (eq T u u1)).(eq_ind T u1 
(\lambda (t0: T).((csuba g c1 d1) \to ((arity g c1 t (asucc g a)) \to ((arity 
g d1 t0 a) \to (or (ex2 C (\lambda (d2: C).(eq C (CHead c1 (Bind Abst) t) 
(CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(eq C (CHead c1 (Bind Abst) 
t) (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda 
(_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a0: 
A).(arity g d2 u2 (asucc g a0))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a0: A).(arity g d1 u1 a0)))))))))) (\lambda (H9: (csuba g c1 d1)).(\lambda 
(H10: (arity g c1 t (asucc g a))).(\lambda (H11: (arity g d1 u1 
a)).(or_intror (ex2 C (\lambda (d2: C).(eq C (CHead c1 (Bind Abst) t) (CHead 
d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (_: A).(eq C (CHead c1 (Bind Abst) t) 
(CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: 
A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a0: 
A).(arity g d2 u2 (asucc g a0))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a0: A).(arity g d1 u1 a0))))) (ex4_3_intro C T A (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (_: A).(eq C (CHead c1 (Bind Abst) t) (CHead d2 (Bind Abst) 
u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (a0: A).(arity g d2 u2 (asucc g 
a0))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a0: A).(arity g d1 u1 
a0)))) c1 t a (refl_equal C (CHead c1 (Bind Abst) t)) H9 H10 H11))))) u 
(sym_eq T u u1 H8))) c2 (sym_eq C c2 d1 H7))) H6))) c H3 H4 H0 H1 H2)))]) in 
(H0 (refl_equal C c) (refl_equal C (CHead d1 (Bind Abbr) u1)))))))).

theorem csuba_gen_flat_rev:
 \forall (g: G).(\forall (d1: C).(\forall (c: C).(\forall (u1: T).(\forall 
(f: F).((csuba g c (CHead d1 (Flat f) u1)) \to (ex2_2 C T (\lambda (d2: 
C).(\lambda (u2: T).(eq C c (CHead d2 (Flat f) u2)))) (\lambda (d2: 
C).(\lambda (_: T).(csuba g d2 d1)))))))))
\def
 \lambda (g: G).(\lambda (d1: C).(\lambda (c: C).(\lambda (u1: T).(\lambda 
(f: F).(\lambda (H: (csuba g c (CHead d1 (Flat f) u1))).(let H0 \def (match H 
in csuba return (\lambda (c0: C).(\lambda (c1: C).(\lambda (_: (csuba ? c0 
c1)).((eq C c0 c) \to ((eq C c1 (CHead d1 (Flat f) u1)) \to (ex2_2 C T 
(\lambda (d2: C).(\lambda (u2: T).(eq C c (CHead d2 (Flat f) u2)))) (\lambda 
(d2: C).(\lambda (_: T).(csuba g d2 d1))))))))) with [(csuba_sort n) 
\Rightarrow (\lambda (H0: (eq C (CSort n) c)).(\lambda (H1: (eq C (CSort n) 
(CHead d1 (Flat f) u1))).(eq_ind C (CSort n) (\lambda (c0: C).((eq C (CSort 
n) (CHead d1 (Flat f) u1)) \to (ex2_2 C T (\lambda (d2: C).(\lambda (u2: 
T).(eq C c0 (CHead d2 (Flat f) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba 
g d2 d1)))))) (\lambda (H2: (eq C (CSort n) (CHead d1 (Flat f) u1))).(let H3 
\def (eq_ind C (CSort n) (\lambda (e: C).(match e in C return (\lambda (_: 
C).Prop) with [(CSort _) \Rightarrow True | (CHead _ _ _) \Rightarrow 
False])) I (CHead d1 (Flat f) u1) H2) in (False_ind (ex2_2 C T (\lambda (d2: 
C).(\lambda (u2: T).(eq C (CSort n) (CHead d2 (Flat f) u2)))) (\lambda (d2: 
C).(\lambda (_: T).(csuba g d2 d1)))) H3))) c H0 H1))) | (csuba_head c1 c2 H0 
k u) \Rightarrow (\lambda (H1: (eq C (CHead c1 k u) c)).(\lambda (H2: (eq C 
(CHead c2 k u) (CHead d1 (Flat f) u1))).(eq_ind C (CHead c1 k u) (\lambda 
(c0: C).((eq C (CHead c2 k u) (CHead d1 (Flat f) u1)) \to ((csuba g c1 c2) 
\to (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(eq C c0 (CHead d2 (Flat f) 
u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))))) (\lambda (H3: 
(eq C (CHead c2 k u) (CHead d1 (Flat f) u1))).(let H4 \def (f_equal C T 
(\lambda (e: C).(match e in C return (\lambda (_: C).T) with [(CSort _) 
\Rightarrow u | (CHead _ _ t) \Rightarrow t])) (CHead c2 k u) (CHead d1 (Flat 
f) u1) H3) in ((let H5 \def (f_equal C K (\lambda (e: C).(match e in C return 
(\lambda (_: C).K) with [(CSort _) \Rightarrow k | (CHead _ k0 _) \Rightarrow 
k0])) (CHead c2 k u) (CHead d1 (Flat f) u1) H3) in ((let H6 \def (f_equal C C 
(\lambda (e: C).(match e in C return (\lambda (_: C).C) with [(CSort _) 
\Rightarrow c2 | (CHead c0 _ _) \Rightarrow c0])) (CHead c2 k u) (CHead d1 
(Flat f) u1) H3) in (eq_ind C d1 (\lambda (c0: C).((eq K k (Flat f)) \to ((eq 
T u u1) \to ((csuba g c1 c0) \to (ex2_2 C T (\lambda (d2: C).(\lambda (u2: 
T).(eq C (CHead c1 k u) (CHead d2 (Flat f) u2)))) (\lambda (d2: C).(\lambda 
(_: T).(csuba g d2 d1)))))))) (\lambda (H7: (eq K k (Flat f))).(eq_ind K 
(Flat f) (\lambda (k0: K).((eq T u u1) \to ((csuba g c1 d1) \to (ex2_2 C T 
(\lambda (d2: C).(\lambda (u2: T).(eq C (CHead c1 k0 u) (CHead d2 (Flat f) 
u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))))) (\lambda (H8: 
(eq T u u1)).(eq_ind T u1 (\lambda (t: T).((csuba g c1 d1) \to (ex2_2 C T 
(\lambda (d2: C).(\lambda (u2: T).(eq C (CHead c1 (Flat f) t) (CHead d2 (Flat 
f) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1)))))) (\lambda (H9: 
(csuba g c1 d1)).(ex2_2_intro C T (\lambda (d2: C).(\lambda (u2: T).(eq C 
(CHead c1 (Flat f) u1) (CHead d2 (Flat f) u2)))) (\lambda (d2: C).(\lambda 
(_: T).(csuba g d2 d1))) c1 u1 (refl_equal C (CHead c1 (Flat f) u1)) H9)) u 
(sym_eq T u u1 H8))) k (sym_eq K k (Flat f) H7))) c2 (sym_eq C c2 d1 H6))) 
H5)) H4))) c H1 H2 H0))) | (csuba_abst c1 c2 H0 t a H1 u H2) \Rightarrow 
(\lambda (H3: (eq C (CHead c1 (Bind Abst) t) c)).(\lambda (H4: (eq C (CHead 
c2 (Bind Abbr) u) (CHead d1 (Flat f) u1))).(eq_ind C (CHead c1 (Bind Abst) t) 
(\lambda (c0: C).((eq C (CHead c2 (Bind Abbr) u) (CHead d1 (Flat f) u1)) \to 
((csuba g c1 c2) \to ((arity g c1 t (asucc g a)) \to ((arity g c2 u a) \to 
(ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(eq C c0 (CHead d2 (Flat f) 
u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))))))) (\lambda (H5: 
(eq C (CHead c2 (Bind Abbr) u) (CHead d1 (Flat f) u1))).(let H6 \def (eq_ind 
C (CHead c2 (Bind Abbr) u) (\lambda (e: C).(match e in C return (\lambda (_: 
C).Prop) with [(CSort _) \Rightarrow False | (CHead _ k _) \Rightarrow (match 
k in K return (\lambda (_: K).Prop) with [(Bind _) \Rightarrow True | (Flat 
_) \Rightarrow False])])) I (CHead d1 (Flat f) u1) H5) in (False_ind ((csuba 
g c1 c2) \to ((arity g c1 t (asucc g a)) \to ((arity g c2 u a) \to (ex2_2 C T 
(\lambda (d2: C).(\lambda (u2: T).(eq C (CHead c1 (Bind Abst) t) (CHead d2 
(Flat f) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))))) H6))) 
c H3 H4 H0 H1 H2)))]) in (H0 (refl_equal C c) (refl_equal C (CHead d1 (Flat 
f) u1))))))))).

theorem csuba_gen_bind_rev:
 \forall (g: G).(\forall (b1: B).(\forall (e1: C).(\forall (c2: C).(\forall 
(v1: T).((csuba g c2 (CHead e1 (Bind b1) v1)) \to (ex2_3 B C T (\lambda (b2: 
B).(\lambda (e2: C).(\lambda (v2: T).(eq C c2 (CHead e2 (Bind b2) v2))))) 
(\lambda (_: B).(\lambda (e2: C).(\lambda (_: T).(csuba g e2 e1))))))))))
\def
 \lambda (g: G).(\lambda (b1: B).(\lambda (e1: C).(\lambda (c2: C).(\lambda 
(v1: T).(\lambda (H: (csuba g c2 (CHead e1 (Bind b1) v1))).(let H0 \def 
(match H in csuba return (\lambda (c: C).(\lambda (c0: C).(\lambda (_: (csuba 
? c c0)).((eq C c c2) \to ((eq C c0 (CHead e1 (Bind b1) v1)) \to (ex2_3 B C T 
(\lambda (b2: B).(\lambda (e2: C).(\lambda (v2: T).(eq C c2 (CHead e2 (Bind 
b2) v2))))) (\lambda (_: B).(\lambda (e2: C).(\lambda (_: T).(csuba g e2 
e1)))))))))) with [(csuba_sort n) \Rightarrow (\lambda (H0: (eq C (CSort n) 
c2)).(\lambda (H1: (eq C (CSort n) (CHead e1 (Bind b1) v1))).(eq_ind C (CSort 
n) (\lambda (c: C).((eq C (CSort n) (CHead e1 (Bind b1) v1)) \to (ex2_3 B C T 
(\lambda (b2: B).(\lambda (e2: C).(\lambda (v2: T).(eq C c (CHead e2 (Bind 
b2) v2))))) (\lambda (_: B).(\lambda (e2: C).(\lambda (_: T).(csuba g e2 
e1))))))) (\lambda (H2: (eq C (CSort n) (CHead e1 (Bind b1) v1))).(let H3 
\def (eq_ind C (CSort n) (\lambda (e: C).(match e in C return (\lambda (_: 
C).Prop) with [(CSort _) \Rightarrow True | (CHead _ _ _) \Rightarrow 
False])) I (CHead e1 (Bind b1) v1) H2) in (False_ind (ex2_3 B C T (\lambda 
(b2: B).(\lambda (e2: C).(\lambda (v2: T).(eq C (CSort n) (CHead e2 (Bind b2) 
v2))))) (\lambda (_: B).(\lambda (e2: C).(\lambda (_: T).(csuba g e2 e1))))) 
H3))) c2 H0 H1))) | (csuba_head c1 c0 H0 k u) \Rightarrow (\lambda (H1: (eq C 
(CHead c1 k u) c2)).(\lambda (H2: (eq C (CHead c0 k u) (CHead e1 (Bind b1) 
v1))).(eq_ind C (CHead c1 k u) (\lambda (c: C).((eq C (CHead c0 k u) (CHead 
e1 (Bind b1) v1)) \to ((csuba g c1 c0) \to (ex2_3 B C T (\lambda (b2: 
B).(\lambda (e2: C).(\lambda (v2: T).(eq C c (CHead e2 (Bind b2) v2))))) 
(\lambda (_: B).(\lambda (e2: C).(\lambda (_: T).(csuba g e2 e1)))))))) 
(\lambda (H3: (eq C (CHead c0 k u) (CHead e1 (Bind b1) v1))).(let H4 \def 
(f_equal C T (\lambda (e: C).(match e in C return (\lambda (_: C).T) with 
[(CSort _) \Rightarrow u | (CHead _ _ t) \Rightarrow t])) (CHead c0 k u) 
(CHead e1 (Bind b1) v1) H3) in ((let H5 \def (f_equal C K (\lambda (e: 
C).(match e in C return (\lambda (_: C).K) with [(CSort _) \Rightarrow k | 
(CHead _ k0 _) \Rightarrow k0])) (CHead c0 k u) (CHead e1 (Bind b1) v1) H3) 
in ((let H6 \def (f_equal C C (\lambda (e: C).(match e in C return (\lambda 
(_: C).C) with [(CSort _) \Rightarrow c0 | (CHead c _ _) \Rightarrow c])) 
(CHead c0 k u) (CHead e1 (Bind b1) v1) H3) in (eq_ind C e1 (\lambda (c: 
C).((eq K k (Bind b1)) \to ((eq T u v1) \to ((csuba g c1 c) \to (ex2_3 B C T 
(\lambda (b2: B).(\lambda (e2: C).(\lambda (v2: T).(eq C (CHead c1 k u) 
(CHead e2 (Bind b2) v2))))) (\lambda (_: B).(\lambda (e2: C).(\lambda (_: 
T).(csuba g e2 e1))))))))) (\lambda (H7: (eq K k (Bind b1))).(eq_ind K (Bind 
b1) (\lambda (k0: K).((eq T u v1) \to ((csuba g c1 e1) \to (ex2_3 B C T 
(\lambda (b2: B).(\lambda (e2: C).(\lambda (v2: T).(eq C (CHead c1 k0 u) 
(CHead e2 (Bind b2) v2))))) (\lambda (_: B).(\lambda (e2: C).(\lambda (_: 
T).(csuba g e2 e1)))))))) (\lambda (H8: (eq T u v1)).(eq_ind T v1 (\lambda 
(t: T).((csuba g c1 e1) \to (ex2_3 B C T (\lambda (b2: B).(\lambda (e2: 
C).(\lambda (v2: T).(eq C (CHead c1 (Bind b1) t) (CHead e2 (Bind b2) v2))))) 
(\lambda (_: B).(\lambda (e2: C).(\lambda (_: T).(csuba g e2 e1))))))) 
(\lambda (H9: (csuba g c1 e1)).(let H10 \def (eq_ind T u (\lambda (t: T).(eq 
C (CHead c1 k t) c2)) H1 v1 H8) in (let H11 \def (eq_ind K k (\lambda (k0: 
K).(eq C (CHead c1 k0 v1) c2)) H10 (Bind b1) H7) in (let H12 \def (eq_ind_r C 
c2 (\lambda (c: C).(csuba g c (CHead e1 (Bind b1) v1))) H (CHead c1 (Bind b1) 
v1) H11) in (ex2_3_intro B C T (\lambda (b2: B).(\lambda (e2: C).(\lambda 
(v2: T).(eq C (CHead c1 (Bind b1) v1) (CHead e2 (Bind b2) v2))))) (\lambda 
(_: B).(\lambda (e2: C).(\lambda (_: T).(csuba g e2 e1)))) b1 c1 v1 
(refl_equal C (CHead c1 (Bind b1) v1)) H9))))) u (sym_eq T u v1 H8))) k 
(sym_eq K k (Bind b1) H7))) c0 (sym_eq C c0 e1 H6))) H5)) H4))) c2 H1 H2 
H0))) | (csuba_abst c1 c0 H0 t a H1 u H2) \Rightarrow (\lambda (H3: (eq C 
(CHead c1 (Bind Abst) t) c2)).(\lambda (H4: (eq C (CHead c0 (Bind Abbr) u) 
(CHead e1 (Bind b1) v1))).(eq_ind C (CHead c1 (Bind Abst) t) (\lambda (c: 
C).((eq C (CHead c0 (Bind Abbr) u) (CHead e1 (Bind b1) v1)) \to ((csuba g c1 
c0) \to ((arity g c1 t (asucc g a)) \to ((arity g c0 u a) \to (ex2_3 B C T 
(\lambda (b2: B).(\lambda (e2: C).(\lambda (v2: T).(eq C c (CHead e2 (Bind 
b2) v2))))) (\lambda (_: B).(\lambda (e2: C).(\lambda (_: T).(csuba g e2 
e1)))))))))) (\lambda (H5: (eq C (CHead c0 (Bind Abbr) u) (CHead e1 (Bind b1) 
v1))).(let H6 \def (f_equal C T (\lambda (e: C).(match e in C return (\lambda 
(_: C).T) with [(CSort _) \Rightarrow u | (CHead _ _ t0) \Rightarrow t0])) 
(CHead c0 (Bind Abbr) u) (CHead e1 (Bind b1) v1) H5) in ((let H7 \def 
(f_equal C B (\lambda (e: C).(match e in C return (\lambda (_: C).B) with 
[(CSort _) \Rightarrow Abbr | (CHead _ k _) \Rightarrow (match k in K return 
(\lambda (_: K).B) with [(Bind b) \Rightarrow b | (Flat _) \Rightarrow 
Abbr])])) (CHead c0 (Bind Abbr) u) (CHead e1 (Bind b1) v1) H5) in ((let H8 
\def (f_equal C C (\lambda (e: C).(match e in C return (\lambda (_: C).C) 
with [(CSort _) \Rightarrow c0 | (CHead c _ _) \Rightarrow c])) (CHead c0 
(Bind Abbr) u) (CHead e1 (Bind b1) v1) H5) in (eq_ind C e1 (\lambda (c: 
C).((eq B Abbr b1) \to ((eq T u v1) \to ((csuba g c1 c) \to ((arity g c1 t 
(asucc g a)) \to ((arity g c u a) \to (ex2_3 B C T (\lambda (b2: B).(\lambda 
(e2: C).(\lambda (v2: T).(eq C (CHead c1 (Bind Abst) t) (CHead e2 (Bind b2) 
v2))))) (\lambda (_: B).(\lambda (e2: C).(\lambda (_: T).(csuba g e2 
e1))))))))))) (\lambda (H9: (eq B Abbr b1)).(eq_ind B Abbr (\lambda (_: 
B).((eq T u v1) \to ((csuba g c1 e1) \to ((arity g c1 t (asucc g a)) \to 
((arity g e1 u a) \to (ex2_3 B C T (\lambda (b2: B).(\lambda (e2: C).(\lambda 
(v2: T).(eq C (CHead c1 (Bind Abst) t) (CHead e2 (Bind b2) v2))))) (\lambda 
(_: B).(\lambda (e2: C).(\lambda (_: T).(csuba g e2 e1)))))))))) (\lambda 
(H10: (eq T u v1)).(eq_ind T v1 (\lambda (t0: T).((csuba g c1 e1) \to ((arity 
g c1 t (asucc g a)) \to ((arity g e1 t0 a) \to (ex2_3 B C T (\lambda (b2: 
B).(\lambda (e2: C).(\lambda (v2: T).(eq C (CHead c1 (Bind Abst) t) (CHead e2 
(Bind b2) v2))))) (\lambda (_: B).(\lambda (e2: C).(\lambda (_: T).(csuba g 
e2 e1))))))))) (\lambda (H11: (csuba g c1 e1)).(\lambda (_: (arity g c1 t 
(asucc g a))).(\lambda (_: (arity g e1 v1 a)).(let H14 \def (eq_ind_r C c2 
(\lambda (c: C).(csuba g c (CHead e1 (Bind b1) v1))) H (CHead c1 (Bind Abst) 
t) H3) in (let H15 \def (eq_ind_r B b1 (\lambda (b: B).(csuba g (CHead c1 
(Bind Abst) t) (CHead e1 (Bind b) v1))) H14 Abbr H9) in (ex2_3_intro B C T 
(\lambda (b2: B).(\lambda (e2: C).(\lambda (v2: T).(eq C (CHead c1 (Bind 
Abst) t) (CHead e2 (Bind b2) v2))))) (\lambda (_: B).(\lambda (e2: 
C).(\lambda (_: T).(csuba g e2 e1)))) Abst c1 t (refl_equal C (CHead c1 (Bind 
Abst) t)) H11)))))) u (sym_eq T u v1 H10))) b1 H9)) c0 (sym_eq C c0 e1 H8))) 
H7)) H6))) c2 H3 H4 H0 H1 H2)))]) in (H0 (refl_equal C c2) (refl_equal C 
(CHead e1 (Bind b1) v1))))))))).

theorem csuba_clear_trans:
 \forall (g: G).(\forall (c1: C).(\forall (c2: C).((csuba g c2 c1) \to 
(\forall (e1: C).((clear c1 e1) \to (ex2 C (\lambda (e2: C).(csuba g e2 e1)) 
(\lambda (e2: C).(clear c2 e2))))))))
\def
 \lambda (g: G).(\lambda (c1: C).(\lambda (c2: C).(\lambda (H: (csuba g c2 
c1)).(csuba_ind g (\lambda (c: C).(\lambda (c0: C).(\forall (e1: C).((clear 
c0 e1) \to (ex2 C (\lambda (e2: C).(csuba g e2 e1)) (\lambda (e2: C).(clear c 
e2))))))) (\lambda (n: nat).(\lambda (e1: C).(\lambda (H0: (clear (CSort n) 
e1)).(clear_gen_sort e1 n H0 (ex2 C (\lambda (e2: C).(csuba g e2 e1)) 
(\lambda (e2: C).(clear (CSort n) e2))))))) (\lambda (c3: C).(\lambda (c4: 
C).(\lambda (H0: (csuba g c3 c4)).(\lambda (H1: ((\forall (e1: C).((clear c4 
e1) \to (ex2 C (\lambda (e2: C).(csuba g e2 e1)) (\lambda (e2: C).(clear c3 
e2))))))).(\lambda (k: K).(\lambda (u: T).(\lambda (e1: C).(\lambda (H2: 
(clear (CHead c4 k u) e1)).((match k in K return (\lambda (k0: K).((clear 
(CHead c4 k0 u) e1) \to (ex2 C (\lambda (e2: C).(csuba g e2 e1)) (\lambda 
(e2: C).(clear (CHead c3 k0 u) e2))))) with [(Bind b) \Rightarrow (\lambda 
(H3: (clear (CHead c4 (Bind b) u) e1)).(eq_ind_r C (CHead c4 (Bind b) u) 
(\lambda (c: C).(ex2 C (\lambda (e2: C).(csuba g e2 c)) (\lambda (e2: 
C).(clear (CHead c3 (Bind b) u) e2)))) (ex_intro2 C (\lambda (e2: C).(csuba g 
e2 (CHead c4 (Bind b) u))) (\lambda (e2: C).(clear (CHead c3 (Bind b) u) e2)) 
(CHead c3 (Bind b) u) (csuba_head g c3 c4 H0 (Bind b) u) (clear_bind b c3 u)) 
e1 (clear_gen_bind b c4 e1 u H3))) | (Flat f) \Rightarrow (\lambda (H3: 
(clear (CHead c4 (Flat f) u) e1)).(let H4 \def (H1 e1 (clear_gen_flat f c4 e1 
u H3)) in (ex2_ind C (\lambda (e2: C).(csuba g e2 e1)) (\lambda (e2: 
C).(clear c3 e2)) (ex2 C (\lambda (e2: C).(csuba g e2 e1)) (\lambda (e2: 
C).(clear (CHead c3 (Flat f) u) e2))) (\lambda (x: C).(\lambda (H5: (csuba g 
x e1)).(\lambda (H6: (clear c3 x)).(ex_intro2 C (\lambda (e2: C).(csuba g e2 
e1)) (\lambda (e2: C).(clear (CHead c3 (Flat f) u) e2)) x H5 (clear_flat c3 x 
H6 f u))))) H4)))]) H2))))))))) (\lambda (c3: C).(\lambda (c4: C).(\lambda 
(H0: (csuba g c3 c4)).(\lambda (_: ((\forall (e1: C).((clear c4 e1) \to (ex2 
C (\lambda (e2: C).(csuba g e2 e1)) (\lambda (e2: C).(clear c3 
e2))))))).(\lambda (t: T).(\lambda (a: A).(\lambda (H2: (arity g c3 t (asucc 
g a))).(\lambda (u: T).(\lambda (H3: (arity g c4 u a)).(\lambda (e1: 
C).(\lambda (H4: (clear (CHead c4 (Bind Abbr) u) e1)).(eq_ind_r C (CHead c4 
(Bind Abbr) u) (\lambda (c: C).(ex2 C (\lambda (e2: C).(csuba g e2 c)) 
(\lambda (e2: C).(clear (CHead c3 (Bind Abst) t) e2)))) (ex_intro2 C (\lambda 
(e2: C).(csuba g e2 (CHead c4 (Bind Abbr) u))) (\lambda (e2: C).(clear (CHead 
c3 (Bind Abst) t) e2)) (CHead c3 (Bind Abst) t) (csuba_abst g c3 c4 H0 t a H2 
u H3) (clear_bind Abst c3 t)) e1 (clear_gen_bind Abbr c4 e1 u H4))))))))))))) 
c2 c1 H)))).

theorem csuba_drop_abst_rev:
 \forall (i: nat).(\forall (c1: C).(\forall (d1: C).(\forall (u: T).((drop i 
O c1 (CHead d1 (Bind Abst) u)) \to (\forall (g: G).(\forall (c2: C).((csuba g 
c2 c1) \to (ex2 C (\lambda (d2: C).(drop i O c2 (CHead d2 (Bind Abst) u))) 
(\lambda (d2: C).(csuba g d2 d1))))))))))
\def
 \lambda (i: nat).(nat_ind (\lambda (n: nat).(\forall (c1: C).(\forall (d1: 
C).(\forall (u: T).((drop n O c1 (CHead d1 (Bind Abst) u)) \to (\forall (g: 
G).(\forall (c2: C).((csuba g c2 c1) \to (ex2 C (\lambda (d2: C).(drop n O c2 
(CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1))))))))))) 
(\lambda (c1: C).(\lambda (d1: C).(\lambda (u: T).(\lambda (H: (drop O O c1 
(CHead d1 (Bind Abst) u))).(\lambda (g: G).(\lambda (c2: C).(\lambda (H0: 
(csuba g c2 c1)).(let H1 \def (eq_ind C c1 (\lambda (c: C).(csuba g c2 c)) H0 
(CHead d1 (Bind Abst) u) (drop_gen_refl c1 (CHead d1 (Bind Abst) u) H)) in 
(let H_x \def (csuba_gen_abst_rev g d1 c2 u H1) in (let H2 \def H_x in 
(ex2_ind C (\lambda (d2: C).(eq C c2 (CHead d2 (Bind Abst) u))) (\lambda (d2: 
C).(csuba g d2 d1)) (ex2 C (\lambda (d2: C).(drop O O c2 (CHead d2 (Bind 
Abst) u))) (\lambda (d2: C).(csuba g d2 d1))) (\lambda (x: C).(\lambda (H3: 
(eq C c2 (CHead x (Bind Abst) u))).(\lambda (H4: (csuba g x d1)).(eq_ind_r C 
(CHead x (Bind Abst) u) (\lambda (c: C).(ex2 C (\lambda (d2: C).(drop O O c 
(CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1)))) (ex_intro2 C 
(\lambda (d2: C).(drop O O (CHead x (Bind Abst) u) (CHead d2 (Bind Abst) u))) 
(\lambda (d2: C).(csuba g d2 d1)) x (drop_refl (CHead x (Bind Abst) u)) H4) 
c2 H3)))) H2))))))))))) (\lambda (n: nat).(\lambda (H: ((\forall (c1: 
C).(\forall (d1: C).(\forall (u: T).((drop n O c1 (CHead d1 (Bind Abst) u)) 
\to (\forall (g: G).(\forall (c2: C).((csuba g c2 c1) \to (ex2 C (\lambda 
(d2: C).(drop n O c2 (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 
d1)))))))))))).(\lambda (c1: C).(C_ind (\lambda (c: C).(\forall (d1: 
C).(\forall (u: T).((drop (S n) O c (CHead d1 (Bind Abst) u)) \to (\forall 
(g: G).(\forall (c2: C).((csuba g c2 c) \to (ex2 C (\lambda (d2: C).(drop (S 
n) O c2 (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1)))))))))) 
(\lambda (n0: nat).(\lambda (d1: C).(\lambda (u: T).(\lambda (H0: (drop (S n) 
O (CSort n0) (CHead d1 (Bind Abst) u))).(\lambda (g: G).(\lambda (c2: 
C).(\lambda (_: (csuba g c2 (CSort n0))).(and3_ind (eq C (CHead d1 (Bind 
Abst) u) (CSort n0)) (eq nat (S n) O) (eq nat O O) (ex2 C (\lambda (d2: 
C).(drop (S n) O c2 (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 
d1))) (\lambda (H2: (eq C (CHead d1 (Bind Abst) u) (CSort n0))).(\lambda (_: 
(eq nat (S n) O)).(\lambda (_: (eq nat O O)).(let H5 \def (match H2 in eq 
return (\lambda (c: C).(\lambda (_: (eq ? ? c)).((eq C c (CSort n0)) \to (ex2 
C (\lambda (d2: C).(drop (S n) O c2 (CHead d2 (Bind Abst) u))) (\lambda (d2: 
C).(csuba g d2 d1)))))) with [refl_equal \Rightarrow (\lambda (H5: (eq C 
(CHead d1 (Bind Abst) u) (CSort n0))).(let H6 \def (eq_ind C (CHead d1 (Bind 
Abst) u) (\lambda (e: C).(match e in C return (\lambda (_: C).Prop) with 
[(CSort _) \Rightarrow False | (CHead _ _ _) \Rightarrow True])) I (CSort n0) 
H5) in (False_ind (ex2 C (\lambda (d2: C).(drop (S n) O c2 (CHead d2 (Bind 
Abst) u))) (\lambda (d2: C).(csuba g d2 d1))) H6)))]) in (H5 (refl_equal C 
(CSort n0))))))) (drop_gen_sort n0 (S n) O (CHead d1 (Bind Abst) u) 
H0))))))))) (\lambda (c: C).(\lambda (H0: ((\forall (d1: C).(\forall (u: 
T).((drop (S n) O c (CHead d1 (Bind Abst) u)) \to (\forall (g: G).(\forall 
(c2: C).((csuba g c2 c) \to (ex2 C (\lambda (d2: C).(drop (S n) O c2 (CHead 
d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1))))))))))).(\lambda (k: 
K).(\lambda (t: T).(\lambda (d1: C).(\lambda (u: T).(\lambda (H1: (drop (S n) 
O (CHead c k t) (CHead d1 (Bind Abst) u))).(\lambda (g: G).(\lambda (c2: 
C).(\lambda (H2: (csuba g c2 (CHead c k t))).(K_ind (\lambda (k0: K).((csuba 
g c2 (CHead c k0 t)) \to ((drop (r k0 n) O c (CHead d1 (Bind Abst) u)) \to 
(ex2 C (\lambda (d2: C).(drop (S n) O c2 (CHead d2 (Bind Abst) u))) (\lambda 
(d2: C).(csuba g d2 d1)))))) (\lambda (b: B).(\lambda (H3: (csuba g c2 (CHead 
c (Bind b) t))).(\lambda (H4: (drop (r (Bind b) n) O c (CHead d1 (Bind Abst) 
u))).(B_ind (\lambda (b0: B).((csuba g c2 (CHead c (Bind b0) t)) \to ((drop 
(r (Bind b0) n) O c (CHead d1 (Bind Abst) u)) \to (ex2 C (\lambda (d2: 
C).(drop (S n) O c2 (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 
d1)))))) (\lambda (H5: (csuba g c2 (CHead c (Bind Abbr) t))).(\lambda (H6: 
(drop (r (Bind Abbr) n) O c (CHead d1 (Bind Abst) u))).(let H_x \def 
(csuba_gen_abbr_rev g c c2 t H5) in (let H7 \def H_x in (or_ind (ex2 C 
(\lambda (d2: C).(eq C c2 (CHead d2 (Bind Abbr) t))) (\lambda (d2: C).(csuba 
g d2 c))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(eq 
C c2 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda 
(_: A).(csuba g d2 c)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g c t a))))) (ex2 C (\lambda (d2: C).(drop (S n) O c2 (CHead d2 
(Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1))) (\lambda (H8: (ex2 C 
(\lambda (d2: C).(eq C c2 (CHead d2 (Bind Abbr) t))) (\lambda (d2: C).(csuba 
g d2 c)))).(ex2_ind C (\lambda (d2: C).(eq C c2 (CHead d2 (Bind Abbr) t))) 
(\lambda (d2: C).(csuba g d2 c)) (ex2 C (\lambda (d2: C).(drop (S n) O c2 
(CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1))) (\lambda (x: 
C).(\lambda (H9: (eq C c2 (CHead x (Bind Abbr) t))).(\lambda (H10: (csuba g x 
c)).(eq_ind_r C (CHead x (Bind Abbr) t) (\lambda (c0: C).(ex2 C (\lambda (d2: 
C).(drop (S n) O c0 (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 
d1)))) (let H11 \def (H c d1 u H6 g x H10) in (ex2_ind C (\lambda (d2: 
C).(drop n O x (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1)) 
(ex2 C (\lambda (d2: C).(drop (S n) O (CHead x (Bind Abbr) t) (CHead d2 (Bind 
Abst) u))) (\lambda (d2: C).(csuba g d2 d1))) (\lambda (x0: C).(\lambda (H12: 
(drop n O x (CHead x0 (Bind Abst) u))).(\lambda (H13: (csuba g x0 d1)).(let 
H14 \def (refl_equal nat (r (Bind Abst) n)) in (let H15 \def (eq_ind nat n 
(\lambda (n0: nat).(drop n0 O x (CHead x0 (Bind Abst) u))) H12 (r (Bind Abst) 
n) H14) in (ex_intro2 C (\lambda (d2: C).(drop (S n) O (CHead x (Bind Abbr) 
t) (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1)) x0 (drop_drop 
(Bind Abbr) n x (CHead x0 (Bind Abst) u) H15 t) H13)))))) H11)) c2 H9)))) 
H8)) (\lambda (H8: (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda 
(_: A).(eq C c2 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d2 c)))) (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda 
(_: T).(\lambda (a: A).(arity g c t a)))))).(ex4_3_ind C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(eq C c2 (CHead d2 (Bind Abst) u2))))) 
(\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 c)))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g c t a)))) (ex2 C 
(\lambda (d2: C).(drop (S n) O c2 (CHead d2 (Bind Abst) u))) (\lambda (d2: 
C).(csuba g d2 d1))) (\lambda (x0: C).(\lambda (x1: T).(\lambda (x2: 
A).(\lambda (H9: (eq C c2 (CHead x0 (Bind Abst) x1))).(\lambda (H10: (csuba g 
x0 c)).(\lambda (_: (arity g x0 x1 (asucc g x2))).(\lambda (_: (arity g c t 
x2)).(eq_ind_r C (CHead x0 (Bind Abst) x1) (\lambda (c0: C).(ex2 C (\lambda 
(d2: C).(drop (S n) O c0 (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g 
d2 d1)))) (let H13 \def (H c d1 u H6 g x0 H10) in (ex2_ind C (\lambda (d2: 
C).(drop n O x0 (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1)) 
(ex2 C (\lambda (d2: C).(drop (S n) O (CHead x0 (Bind Abst) x1) (CHead d2 
(Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1))) (\lambda (x: C).(\lambda 
(H14: (drop n O x0 (CHead x (Bind Abst) u))).(\lambda (H15: (csuba g x 
d1)).(let H16 \def (refl_equal nat (r (Bind Abst) n)) in (let H17 \def 
(eq_ind nat n (\lambda (n0: nat).(drop n0 O x0 (CHead x (Bind Abst) u))) H14 
(r (Bind Abst) n) H16) in (ex_intro2 C (\lambda (d2: C).(drop (S n) O (CHead 
x0 (Bind Abst) x1) (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 
d1)) x (drop_drop (Bind Abst) n x0 (CHead x (Bind Abst) u) H17 x1) H15)))))) 
H13)) c2 H9)))))))) H8)) H7))))) (\lambda (H5: (csuba g c2 (CHead c (Bind 
Abst) t))).(\lambda (H6: (drop (r (Bind Abst) n) O c (CHead d1 (Bind Abst) 
u))).(let H_x \def (csuba_gen_abst_rev g c c2 t H5) in (let H7 \def H_x in 
(ex2_ind C (\lambda (d2: C).(eq C c2 (CHead d2 (Bind Abst) t))) (\lambda (d2: 
C).(csuba g d2 c)) (ex2 C (\lambda (d2: C).(drop (S n) O c2 (CHead d2 (Bind 
Abst) u))) (\lambda (d2: C).(csuba g d2 d1))) (\lambda (x: C).(\lambda (H8: 
(eq C c2 (CHead x (Bind Abst) t))).(\lambda (H9: (csuba g x c)).(eq_ind_r C 
(CHead x (Bind Abst) t) (\lambda (c0: C).(ex2 C (\lambda (d2: C).(drop (S n) 
O c0 (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1)))) (let H10 
\def (H c d1 u H6 g x H9) in (ex2_ind C (\lambda (d2: C).(drop n O x (CHead 
d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1)) (ex2 C (\lambda (d2: 
C).(drop (S n) O (CHead x (Bind Abst) t) (CHead d2 (Bind Abst) u))) (\lambda 
(d2: C).(csuba g d2 d1))) (\lambda (x0: C).(\lambda (H11: (drop n O x (CHead 
x0 (Bind Abst) u))).(\lambda (H12: (csuba g x0 d1)).(let H13 \def (refl_equal 
nat (r (Bind Abst) n)) in (let H14 \def (eq_ind nat n (\lambda (n0: 
nat).(drop n0 O x (CHead x0 (Bind Abst) u))) H11 (r (Bind Abst) n) H13) in 
(ex_intro2 C (\lambda (d2: C).(drop (S n) O (CHead x (Bind Abst) t) (CHead d2 
(Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1)) x0 (drop_drop (Bind Abst) 
n x (CHead x0 (Bind Abst) u) H14 t) H12)))))) H10)) c2 H8)))) H7))))) 
(\lambda (H5: (csuba g c2 (CHead c (Bind Void) t))).(\lambda (H6: (drop (r 
(Bind Void) n) O c (CHead d1 (Bind Abst) u))).(let H_x \def 
(csuba_gen_void_rev g c c2 t H5) in (let H7 \def H_x in (ex2_ind C (\lambda 
(d2: C).(eq C c2 (CHead d2 (Bind Void) t))) (\lambda (d2: C).(csuba g d2 c)) 
(ex2 C (\lambda (d2: C).(drop (S n) O c2 (CHead d2 (Bind Abst) u))) (\lambda 
(d2: C).(csuba g d2 d1))) (\lambda (x: C).(\lambda (H8: (eq C c2 (CHead x 
(Bind Void) t))).(\lambda (H9: (csuba g x c)).(eq_ind_r C (CHead x (Bind 
Void) t) (\lambda (c0: C).(ex2 C (\lambda (d2: C).(drop (S n) O c0 (CHead d2 
(Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1)))) (let H10 \def (H c d1 u 
H6 g x H9) in (ex2_ind C (\lambda (d2: C).(drop n O x (CHead d2 (Bind Abst) 
u))) (\lambda (d2: C).(csuba g d2 d1)) (ex2 C (\lambda (d2: C).(drop (S n) O 
(CHead x (Bind Void) t) (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g 
d2 d1))) (\lambda (x0: C).(\lambda (H11: (drop n O x (CHead x0 (Bind Abst) 
u))).(\lambda (H12: (csuba g x0 d1)).(let H13 \def (refl_equal nat (r (Bind 
Abst) n)) in (let H14 \def (eq_ind nat n (\lambda (n0: nat).(drop n0 O x 
(CHead x0 (Bind Abst) u))) H11 (r (Bind Abst) n) H13) in (ex_intro2 C 
(\lambda (d2: C).(drop (S n) O (CHead x (Bind Void) t) (CHead d2 (Bind Abst) 
u))) (\lambda (d2: C).(csuba g d2 d1)) x0 (drop_drop (Bind Void) n x (CHead 
x0 (Bind Abst) u) H14 t) H12)))))) H10)) c2 H8)))) H7))))) b H3 H4)))) 
(\lambda (f: F).(\lambda (H3: (csuba g c2 (CHead c (Flat f) t))).(\lambda 
(H4: (drop (r (Flat f) n) O c (CHead d1 (Bind Abst) u))).(let H_x \def 
(csuba_gen_flat_rev g c c2 t f H3) in (let H5 \def H_x in (ex2_2_ind C T 
(\lambda (d2: C).(\lambda (u2: T).(eq C c2 (CHead d2 (Flat f) u2)))) (\lambda 
(d2: C).(\lambda (_: T).(csuba g d2 c))) (ex2 C (\lambda (d2: C).(drop (S n) 
O c2 (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1))) (\lambda 
(x0: C).(\lambda (x1: T).(\lambda (H6: (eq C c2 (CHead x0 (Flat f) 
x1))).(\lambda (H7: (csuba g x0 c)).(eq_ind_r C (CHead x0 (Flat f) x1) 
(\lambda (c0: C).(ex2 C (\lambda (d2: C).(drop (S n) O c0 (CHead d2 (Bind 
Abst) u))) (\lambda (d2: C).(csuba g d2 d1)))) (let H8 \def (H0 d1 u H4 g x0 
H7) in (ex2_ind C (\lambda (d2: C).(drop (S n) O x0 (CHead d2 (Bind Abst) 
u))) (\lambda (d2: C).(csuba g d2 d1)) (ex2 C (\lambda (d2: C).(drop (S n) O 
(CHead x0 (Flat f) x1) (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g 
d2 d1))) (\lambda (x: C).(\lambda (H9: (drop (S n) O x0 (CHead x (Bind Abst) 
u))).(\lambda (H10: (csuba g x d1)).(ex_intro2 C (\lambda (d2: C).(drop (S n) 
O (CHead x0 (Flat f) x1) (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g 
d2 d1)) x (drop_drop (Flat f) n x0 (CHead x (Bind Abst) u) H9 x1) H10)))) 
H8)) c2 H6))))) H5)))))) k H2 (drop_gen_drop k c (CHead d1 (Bind Abst) u) t n 
H1)))))))))))) c1)))) i).

theorem csuba_drop_abbr_rev:
 \forall (i: nat).(\forall (c1: C).(\forall (d1: C).(\forall (u1: T).((drop i 
O c1 (CHead d1 (Bind Abbr) u1)) \to (\forall (g: G).(\forall (c2: C).((csuba 
g c2 c1) \to (or (ex2 C (\lambda (d2: C).(drop i O c2 (CHead d2 (Bind Abbr) 
u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(drop i O c2 (CHead d2 (Bind Abst) 
u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g 
a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 
a)))))))))))))
\def
 \lambda (i: nat).(nat_ind (\lambda (n: nat).(\forall (c1: C).(\forall (d1: 
C).(\forall (u1: T).((drop n O c1 (CHead d1 (Bind Abbr) u1)) \to (\forall (g: 
G).(\forall (c2: C).((csuba g c2 c1) \to (or (ex2 C (\lambda (d2: C).(drop n 
O c2 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C 
T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop n O c2 (CHead d2 
(Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g 
d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
(asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 
u1 a)))))))))))))) (\lambda (c1: C).(\lambda (d1: C).(\lambda (u1: 
T).(\lambda (H: (drop O O c1 (CHead d1 (Bind Abbr) u1))).(\lambda (g: 
G).(\lambda (c2: C).(\lambda (H0: (csuba g c2 c1)).(let H1 \def (eq_ind C c1 
(\lambda (c: C).(csuba g c2 c)) H0 (CHead d1 (Bind Abbr) u1) (drop_gen_refl 
c1 (CHead d1 (Bind Abbr) u1) H)) in (let H_x \def (csuba_gen_abbr_rev g d1 c2 
u1 H1) in (let H2 \def H_x in (or_ind (ex2 C (\lambda (d2: C).(eq C c2 (CHead 
d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (_: A).(eq C c2 (CHead d2 (Bind Abst) 
u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g 
a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a))))) 
(or (ex2 C (\lambda (d2: C).(drop O O c2 (CHead d2 (Bind Abbr) u1))) (\lambda 
(d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (_: A).(drop O O c2 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: 
C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a)))))) (\lambda (H3: 
(ex2 C (\lambda (d2: C).(eq C c2 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: 
C).(csuba g d2 d1)))).(ex2_ind C (\lambda (d2: C).(eq C c2 (CHead d2 (Bind 
Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1)) (or (ex2 C (\lambda (d2: 
C).(drop O O c2 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 
d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop O 
O c2 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda 
(_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a)))))) (\lambda (x: C).(\lambda (H4: (eq C c2 (CHead x 
(Bind Abbr) u1))).(\lambda (H5: (csuba g x d1)).(eq_ind_r C (CHead x (Bind 
Abbr) u1) (\lambda (c: C).(or (ex2 C (\lambda (d2: C).(drop O O c (CHead d2 
(Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (_: A).(drop O O c (CHead d2 (Bind Abst) 
u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g 
a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 
a))))))) (or_introl (ex2 C (\lambda (d2: C).(drop O O (CHead x (Bind Abbr) 
u1) (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T 
A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop O O (CHead x (Bind 
Abbr) u1) (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda 
(_: T).(\lambda (a: A).(arity g d1 u1 a))))) (ex_intro2 C (\lambda (d2: 
C).(drop O O (CHead x (Bind Abbr) u1) (CHead d2 (Bind Abbr) u1))) (\lambda 
(d2: C).(csuba g d2 d1)) x (drop_refl (CHead x (Bind Abbr) u1)) H5)) c2 
H4)))) H3)) (\lambda (H3: (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (_: A).(eq C c2 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: 
C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a)))))).(ex4_3_ind C T 
A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(eq C c2 (CHead d2 (Bind 
Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 
d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
(asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 
u1 a)))) (or (ex2 C (\lambda (d2: C).(drop O O c2 (CHead d2 (Bind Abbr) u1))) 
(\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (_: A).(drop O O c2 (CHead d2 (Bind Abst) u2))))) (\lambda 
(d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a)))))) (\lambda (x0: 
C).(\lambda (x1: T).(\lambda (x2: A).(\lambda (H4: (eq C c2 (CHead x0 (Bind 
Abst) x1))).(\lambda (H5: (csuba g x0 d1)).(\lambda (H6: (arity g x0 x1 
(asucc g x2))).(\lambda (H7: (arity g d1 u1 x2)).(eq_ind_r C (CHead x0 (Bind 
Abst) x1) (\lambda (c: C).(or (ex2 C (\lambda (d2: C).(drop O O c (CHead d2 
(Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (_: A).(drop O O c (CHead d2 (Bind Abst) 
u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g 
a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 
a))))))) (or_intror (ex2 C (\lambda (d2: C).(drop O O (CHead x0 (Bind Abst) 
x1) (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T 
A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop O O (CHead x0 (Bind 
Abst) x1) (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda 
(_: T).(\lambda (a: A).(arity g d1 u1 a))))) (ex4_3_intro C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(drop O O (CHead x0 (Bind Abst) x1) 
(CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: 
A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a)))) x0 x1 x2 (drop_refl (CHead x0 (Bind Abst) x1)) H5 
H6 H7)) c2 H4)))))))) H3)) H2))))))))))) (\lambda (n: nat).(\lambda (H: 
((\forall (c1: C).(\forall (d1: C).(\forall (u1: T).((drop n O c1 (CHead d1 
(Bind Abbr) u1)) \to (\forall (g: G).(\forall (c2: C).((csuba g c2 c1) \to 
(or (ex2 C (\lambda (d2: C).(drop n O c2 (CHead d2 (Bind Abbr) u1))) (\lambda 
(d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (_: A).(drop n O c2 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: 
C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 
a))))))))))))))).(\lambda (c1: C).(C_ind (\lambda (c: C).(\forall (d1: 
C).(\forall (u1: T).((drop (S n) O c (CHead d1 (Bind Abbr) u1)) \to (\forall 
(g: G).(\forall (c2: C).((csuba g c2 c) \to (or (ex2 C (\lambda (d2: C).(drop 
(S n) O c2 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) 
(ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O 
c2 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda 
(_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a))))))))))))) (\lambda (n0: nat).(\lambda (d1: 
C).(\lambda (u1: T).(\lambda (H0: (drop (S n) O (CSort n0) (CHead d1 (Bind 
Abbr) u1))).(\lambda (g: G).(\lambda (c2: C).(\lambda (_: (csuba g c2 (CSort 
n0))).(and3_ind (eq C (CHead d1 (Bind Abbr) u1) (CSort n0)) (eq nat (S n) O) 
(eq nat O O) (or (ex2 C (\lambda (d2: C).(drop (S n) O c2 (CHead d2 (Bind 
Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O c2 (CHead d2 (Bind Abst) 
u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g 
a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a)))))) 
(\lambda (H2: (eq C (CHead d1 (Bind Abbr) u1) (CSort n0))).(\lambda (_: (eq 
nat (S n) O)).(\lambda (_: (eq nat O O)).(let H5 \def (match H2 in eq return 
(\lambda (c: C).(\lambda (_: (eq ? ? c)).((eq C c (CSort n0)) \to (or (ex2 C 
(\lambda (d2: C).(drop (S n) O c2 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: 
C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda 
(_: A).(drop (S n) O c2 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: 
C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a))))))))) with 
[refl_equal \Rightarrow (\lambda (H5: (eq C (CHead d1 (Bind Abbr) u1) (CSort 
n0))).(let H6 \def (eq_ind C (CHead d1 (Bind Abbr) u1) (\lambda (e: C).(match 
e in C return (\lambda (_: C).Prop) with [(CSort _) \Rightarrow False | 
(CHead _ _ _) \Rightarrow True])) I (CSort n0) H5) in (False_ind (or (ex2 C 
(\lambda (d2: C).(drop (S n) O c2 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: 
C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda 
(_: A).(drop (S n) O c2 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: 
C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a)))))) H6)))]) in (H5 
(refl_equal C (CSort n0))))))) (drop_gen_sort n0 (S n) O (CHead d1 (Bind 
Abbr) u1) H0))))))))) (\lambda (c: C).(\lambda (H0: ((\forall (d1: 
C).(\forall (u1: T).((drop (S n) O c (CHead d1 (Bind Abbr) u1)) \to (\forall 
(g: G).(\forall (c2: C).((csuba g c2 c) \to (or (ex2 C (\lambda (d2: C).(drop 
(S n) O c2 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) 
(ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O 
c2 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda 
(_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a)))))))))))))).(\lambda (k: K).(\lambda (t: 
T).(\lambda (d1: C).(\lambda (u1: T).(\lambda (H1: (drop (S n) O (CHead c k 
t) (CHead d1 (Bind Abbr) u1))).(\lambda (g: G).(\lambda (c2: C).(\lambda (H2: 
(csuba g c2 (CHead c k t))).(K_ind (\lambda (k0: K).((csuba g c2 (CHead c k0 
t)) \to ((drop (r k0 n) O c (CHead d1 (Bind Abbr) u1)) \to (or (ex2 C 
(\lambda (d2: C).(drop (S n) O c2 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: 
C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda 
(_: A).(drop (S n) O c2 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: 
C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a))))))))) (\lambda (b: 
B).(\lambda (H3: (csuba g c2 (CHead c (Bind b) t))).(\lambda (H4: (drop (r 
(Bind b) n) O c (CHead d1 (Bind Abbr) u1))).(B_ind (\lambda (b0: B).((csuba g 
c2 (CHead c (Bind b0) t)) \to ((drop (r (Bind b0) n) O c (CHead d1 (Bind 
Abbr) u1)) \to (or (ex2 C (\lambda (d2: C).(drop (S n) O c2 (CHead d2 (Bind 
Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O c2 (CHead d2 (Bind Abst) 
u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g 
a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 
a))))))))) (\lambda (H5: (csuba g c2 (CHead c (Bind Abbr) t))).(\lambda (H6: 
(drop (r (Bind Abbr) n) O c (CHead d1 (Bind Abbr) u1))).(let H_x \def 
(csuba_gen_abbr_rev g c c2 t H5) in (let H7 \def H_x in (or_ind (ex2 C 
(\lambda (d2: C).(eq C c2 (CHead d2 (Bind Abbr) t))) (\lambda (d2: C).(csuba 
g d2 c))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(eq 
C c2 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda 
(_: A).(csuba g d2 c)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g c t a))))) (or (ex2 C (\lambda (d2: C).(drop (S n) O c2 
(CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O c2 (CHead d2 
(Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g 
d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
(asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 
u1 a)))))) (\lambda (H8: (ex2 C (\lambda (d2: C).(eq C c2 (CHead d2 (Bind 
Abbr) t))) (\lambda (d2: C).(csuba g d2 c)))).(ex2_ind C (\lambda (d2: C).(eq 
C c2 (CHead d2 (Bind Abbr) t))) (\lambda (d2: C).(csuba g d2 c)) (or (ex2 C 
(\lambda (d2: C).(drop (S n) O c2 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: 
C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda 
(_: A).(drop (S n) O c2 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: 
C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a)))))) (\lambda (x: 
C).(\lambda (H9: (eq C c2 (CHead x (Bind Abbr) t))).(\lambda (H10: (csuba g x 
c)).(eq_ind_r C (CHead x (Bind Abbr) t) (\lambda (c0: C).(or (ex2 C (\lambda 
(d2: C).(drop (S n) O c0 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba 
g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: 
A).(drop (S n) O c0 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda 
(_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda 
(_: T).(\lambda (a: A).(arity g d1 u1 a))))))) (let H11 \def (H c d1 u1 H6 g 
x H10) in (or_ind (ex2 C (\lambda (d2: C).(drop n O x (CHead d2 (Bind Abbr) 
u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(drop n O x (CHead d2 (Bind Abst) u2))))) 
(\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a))))) (or 
(ex2 C (\lambda (d2: C).(drop (S n) O (CHead x (Bind Abbr) t) (CHead d2 (Bind 
Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O (CHead x (Bind Abbr) t) 
(CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: 
A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a)))))) (\lambda (H12: (ex2 C (\lambda (d2: C).(drop n 
O x (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1)))).(ex2_ind 
C (\lambda (d2: C).(drop n O x (CHead d2 (Bind Abbr) u1))) (\lambda (d2: 
C).(csuba g d2 d1)) (or (ex2 C (\lambda (d2: C).(drop (S n) O (CHead x (Bind 
Abbr) t) (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) 
(ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O 
(CHead x (Bind Abbr) t) (CHead d2 (Bind Abst) u2))))) (\lambda (d2: 
C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a)))))) (\lambda (x0: 
C).(\lambda (H13: (drop n O x (CHead x0 (Bind Abbr) u1))).(\lambda (H14: 
(csuba g x0 d1)).(let H15 \def (refl_equal nat (r (Bind Abst) n)) in (let H16 
\def (eq_ind nat n (\lambda (n0: nat).(drop n0 O x (CHead x0 (Bind Abbr) 
u1))) H13 (r (Bind Abst) n) H15) in (or_introl (ex2 C (\lambda (d2: C).(drop 
(S n) O (CHead x (Bind Abbr) t) (CHead d2 (Bind Abbr) u1))) (\lambda (d2: 
C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda 
(_: A).(drop (S n) O (CHead x (Bind Abbr) t) (CHead d2 (Bind Abst) u2))))) 
(\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a))))) 
(ex_intro2 C (\lambda (d2: C).(drop (S n) O (CHead x (Bind Abbr) t) (CHead d2 
(Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1)) x0 (drop_drop (Bind Abbr) 
n x (CHead x0 (Bind Abbr) u1) H16 t) H14))))))) H12)) (\lambda (H12: (ex4_3 C 
T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop n O x (CHead d2 
(Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g 
d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
(asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 
u1 a)))))).(ex4_3_ind C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: 
A).(drop n O x (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda 
(_: T).(\lambda (a: A).(arity g d1 u1 a)))) (or (ex2 C (\lambda (d2: C).(drop 
(S n) O (CHead x (Bind Abbr) t) (CHead d2 (Bind Abbr) u1))) (\lambda (d2: 
C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda 
(_: A).(drop (S n) O (CHead x (Bind Abbr) t) (CHead d2 (Bind Abst) u2))))) 
(\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a)))))) 
(\lambda (x0: C).(\lambda (x1: T).(\lambda (x2: A).(\lambda (H13: (drop n O x 
(CHead x0 (Bind Abst) x1))).(\lambda (H14: (csuba g x0 d1)).(\lambda (H15: 
(arity g x0 x1 (asucc g x2))).(\lambda (H16: (arity g d1 u1 x2)).(let H17 
\def (refl_equal nat (r (Bind Abst) n)) in (let H18 \def (eq_ind nat n 
(\lambda (n0: nat).(drop n0 O x (CHead x0 (Bind Abst) x1))) H13 (r (Bind 
Abst) n) H17) in (or_intror (ex2 C (\lambda (d2: C).(drop (S n) O (CHead x 
(Bind Abbr) t) (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) 
(ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O 
(CHead x (Bind Abbr) t) (CHead d2 (Bind Abst) u2))))) (\lambda (d2: 
C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a))))) (ex4_3_intro C T 
A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O (CHead x 
(Bind Abbr) t) (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda 
(_: T).(\lambda (a: A).(arity g d1 u1 a)))) x0 x1 x2 (drop_drop (Bind Abbr) n 
x (CHead x0 (Bind Abst) x1) H18 t) H14 H15 H16))))))))))) H12)) H11)) c2 
H9)))) H8)) (\lambda (H8: (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (_: A).(eq C c2 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: 
C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 c)))) (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(arity g c t a)))))).(ex4_3_ind C T A 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(eq C c2 (CHead d2 (Bind 
Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 
c)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc 
g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g c t a)))) 
(or (ex2 C (\lambda (d2: C).(drop (S n) O c2 (CHead d2 (Bind Abbr) u1))) 
(\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (_: A).(drop (S n) O c2 (CHead d2 (Bind Abst) u2))))) 
(\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a)))))) 
(\lambda (x0: C).(\lambda (x1: T).(\lambda (x2: A).(\lambda (H9: (eq C c2 
(CHead x0 (Bind Abst) x1))).(\lambda (H10: (csuba g x0 c)).(\lambda (_: 
(arity g x0 x1 (asucc g x2))).(\lambda (_: (arity g c t x2)).(eq_ind_r C 
(CHead x0 (Bind Abst) x1) (\lambda (c0: C).(or (ex2 C (\lambda (d2: C).(drop 
(S n) O c0 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) 
(ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O 
c0 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda 
(_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a))))))) (let H13 \def (H c d1 u1 H6 g x0 H10) in 
(or_ind (ex2 C (\lambda (d2: C).(drop n O x0 (CHead d2 (Bind Abbr) u1))) 
(\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (_: A).(drop n O x0 (CHead d2 (Bind Abst) u2))))) (\lambda 
(d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a))))) (or (ex2 C 
(\lambda (d2: C).(drop (S n) O (CHead x0 (Bind Abst) x1) (CHead d2 (Bind 
Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O (CHead x0 (Bind Abst) x1) 
(CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: 
A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a)))))) (\lambda (H14: (ex2 C (\lambda (d2: C).(drop n 
O x0 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1)))).(ex2_ind 
C (\lambda (d2: C).(drop n O x0 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: 
C).(csuba g d2 d1)) (or (ex2 C (\lambda (d2: C).(drop (S n) O (CHead x0 (Bind 
Abst) x1) (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) 
(ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O 
(CHead x0 (Bind Abst) x1) (CHead d2 (Bind Abst) u2))))) (\lambda (d2: 
C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a)))))) (\lambda (x: 
C).(\lambda (H15: (drop n O x0 (CHead x (Bind Abbr) u1))).(\lambda (H16: 
(csuba g x d1)).(let H17 \def (refl_equal nat (r (Bind Abst) n)) in (let H18 
\def (eq_ind nat n (\lambda (n0: nat).(drop n0 O x0 (CHead x (Bind Abbr) 
u1))) H15 (r (Bind Abst) n) H17) in (or_introl (ex2 C (\lambda (d2: C).(drop 
(S n) O (CHead x0 (Bind Abst) x1) (CHead d2 (Bind Abbr) u1))) (\lambda (d2: 
C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda 
(_: A).(drop (S n) O (CHead x0 (Bind Abst) x1) (CHead d2 (Bind Abst) u2))))) 
(\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a))))) 
(ex_intro2 C (\lambda (d2: C).(drop (S n) O (CHead x0 (Bind Abst) x1) (CHead 
d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1)) x (drop_drop (Bind 
Abst) n x0 (CHead x (Bind Abbr) u1) H18 x1) H16))))))) H14)) (\lambda (H14: 
(ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop n O x0 
(CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: 
A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a)))))).(ex4_3_ind C T A (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (_: A).(drop n O x0 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: 
C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a)))) (or (ex2 C 
(\lambda (d2: C).(drop (S n) O (CHead x0 (Bind Abst) x1) (CHead d2 (Bind 
Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O (CHead x0 (Bind Abst) x1) 
(CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: 
A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a)))))) (\lambda (x3: C).(\lambda (x4: T).(\lambda (x5: 
A).(\lambda (H15: (drop n O x0 (CHead x3 (Bind Abst) x4))).(\lambda (H16: 
(csuba g x3 d1)).(\lambda (H17: (arity g x3 x4 (asucc g x5))).(\lambda (H18: 
(arity g d1 u1 x5)).(let H19 \def (refl_equal nat (r (Bind Abst) n)) in (let 
H20 \def (eq_ind nat n (\lambda (n0: nat).(drop n0 O x0 (CHead x3 (Bind Abst) 
x4))) H15 (r (Bind Abst) n) H19) in (or_intror (ex2 C (\lambda (d2: C).(drop 
(S n) O (CHead x0 (Bind Abst) x1) (CHead d2 (Bind Abbr) u1))) (\lambda (d2: 
C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda 
(_: A).(drop (S n) O (CHead x0 (Bind Abst) x1) (CHead d2 (Bind Abst) u2))))) 
(\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a))))) 
(ex4_3_intro C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S 
n) O (CHead x0 (Bind Abst) x1) (CHead d2 (Bind Abst) u2))))) (\lambda (d2: 
C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a)))) x3 x4 x5 
(drop_drop (Bind Abst) n x0 (CHead x3 (Bind Abst) x4) H20 x1) H16 H17 
H18))))))))))) H14)) H13)) c2 H9)))))))) H8)) H7))))) (\lambda (H5: (csuba g 
c2 (CHead c (Bind Abst) t))).(\lambda (H6: (drop (r (Bind Abst) n) O c (CHead 
d1 (Bind Abbr) u1))).(let H_x \def (csuba_gen_abst_rev g c c2 t H5) in (let 
H7 \def H_x in (ex2_ind C (\lambda (d2: C).(eq C c2 (CHead d2 (Bind Abst) 
t))) (\lambda (d2: C).(csuba g d2 c)) (or (ex2 C (\lambda (d2: C).(drop (S n) 
O c2 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C 
T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O c2 (CHead 
d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: 
A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a)))))) (\lambda (x: C).(\lambda (H8: (eq C c2 (CHead x 
(Bind Abst) t))).(\lambda (H9: (csuba g x c)).(eq_ind_r C (CHead x (Bind 
Abst) t) (\lambda (c0: C).(or (ex2 C (\lambda (d2: C).(drop (S n) O c0 (CHead 
d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O c0 (CHead d2 (Bind 
Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 
d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
(asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 
u1 a))))))) (let H10 \def (H c d1 u1 H6 g x H9) in (or_ind (ex2 C (\lambda 
(d2: C).(drop n O x (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 
d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop n 
O x (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda 
(_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a))))) (or (ex2 C (\lambda (d2: C).(drop (S n) O (CHead 
x (Bind Abst) t) (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 
d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S 
n) O (CHead x (Bind Abst) t) (CHead d2 (Bind Abst) u2))))) (\lambda (d2: 
C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a)))))) (\lambda (H11: 
(ex2 C (\lambda (d2: C).(drop n O x (CHead d2 (Bind Abbr) u1))) (\lambda (d2: 
C).(csuba g d2 d1)))).(ex2_ind C (\lambda (d2: C).(drop n O x (CHead d2 (Bind 
Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1)) (or (ex2 C (\lambda (d2: 
C).(drop (S n) O (CHead x (Bind Abst) t) (CHead d2 (Bind Abbr) u1))) (\lambda 
(d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (_: A).(drop (S n) O (CHead x (Bind Abst) t) (CHead d2 (Bind 
Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 
d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
(asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 
u1 a)))))) (\lambda (x0: C).(\lambda (H12: (drop n O x (CHead x0 (Bind Abbr) 
u1))).(\lambda (H13: (csuba g x0 d1)).(let H14 \def (refl_equal nat (r (Bind 
Abst) n)) in (let H15 \def (eq_ind nat n (\lambda (n0: nat).(drop n0 O x 
(CHead x0 (Bind Abbr) u1))) H12 (r (Bind Abst) n) H14) in (or_introl (ex2 C 
(\lambda (d2: C).(drop (S n) O (CHead x (Bind Abst) t) (CHead d2 (Bind Abbr) 
u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O (CHead x (Bind Abst) t) 
(CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: 
A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a))))) (ex_intro2 C (\lambda (d2: C).(drop (S n) O 
(CHead x (Bind Abst) t) (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g 
d2 d1)) x0 (drop_drop (Bind Abst) n x (CHead x0 (Bind Abbr) u1) H15 t) 
H13))))))) H11)) (\lambda (H11: (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (_: A).(drop n O x (CHead d2 (Bind Abst) u2))))) (\lambda (d2: 
C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a)))))).(ex4_3_ind C T 
A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop n O x (CHead d2 
(Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g 
d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
(asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 
u1 a)))) (or (ex2 C (\lambda (d2: C).(drop (S n) O (CHead x (Bind Abst) t) 
(CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O (CHead x 
(Bind Abst) t) (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda 
(_: T).(\lambda (a: A).(arity g d1 u1 a)))))) (\lambda (x0: C).(\lambda (x1: 
T).(\lambda (x2: A).(\lambda (H12: (drop n O x (CHead x0 (Bind Abst) 
x1))).(\lambda (H13: (csuba g x0 d1)).(\lambda (H14: (arity g x0 x1 (asucc g 
x2))).(\lambda (H15: (arity g d1 u1 x2)).(let H16 \def (refl_equal nat (r 
(Bind Abst) n)) in (let H17 \def (eq_ind nat n (\lambda (n0: nat).(drop n0 O 
x (CHead x0 (Bind Abst) x1))) H12 (r (Bind Abst) n) H16) in (or_intror (ex2 C 
(\lambda (d2: C).(drop (S n) O (CHead x (Bind Abst) t) (CHead d2 (Bind Abbr) 
u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O (CHead x (Bind Abst) t) 
(CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: 
A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a))))) (ex4_3_intro C T A (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (_: A).(drop (S n) O (CHead x (Bind Abst) t) (CHead d2 (Bind 
Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 
d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
(asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 
u1 a)))) x0 x1 x2 (drop_drop (Bind Abst) n x (CHead x0 (Bind Abst) x1) H17 t) 
H13 H14 H15))))))))))) H11)) H10)) c2 H8)))) H7))))) (\lambda (H5: (csuba g 
c2 (CHead c (Bind Void) t))).(\lambda (H6: (drop (r (Bind Void) n) O c (CHead 
d1 (Bind Abbr) u1))).(let H_x \def (csuba_gen_void_rev g c c2 t H5) in (let 
H7 \def H_x in (ex2_ind C (\lambda (d2: C).(eq C c2 (CHead d2 (Bind Void) 
t))) (\lambda (d2: C).(csuba g d2 c)) (or (ex2 C (\lambda (d2: C).(drop (S n) 
O c2 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C 
T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O c2 (CHead 
d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: 
A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a)))))) (\lambda (x: C).(\lambda (H8: (eq C c2 (CHead x 
(Bind Void) t))).(\lambda (H9: (csuba g x c)).(eq_ind_r C (CHead x (Bind 
Void) t) (\lambda (c0: C).(or (ex2 C (\lambda (d2: C).(drop (S n) O c0 (CHead 
d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O c0 (CHead d2 (Bind 
Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 
d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
(asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 
u1 a))))))) (let H10 \def (H c d1 u1 H6 g x H9) in (or_ind (ex2 C (\lambda 
(d2: C).(drop n O x (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 
d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop n 
O x (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda 
(_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a))))) (or (ex2 C (\lambda (d2: C).(drop (S n) O (CHead 
x (Bind Void) t) (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 
d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S 
n) O (CHead x (Bind Void) t) (CHead d2 (Bind Abst) u2))))) (\lambda (d2: 
C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a)))))) (\lambda (H11: 
(ex2 C (\lambda (d2: C).(drop n O x (CHead d2 (Bind Abbr) u1))) (\lambda (d2: 
C).(csuba g d2 d1)))).(ex2_ind C (\lambda (d2: C).(drop n O x (CHead d2 (Bind 
Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1)) (or (ex2 C (\lambda (d2: 
C).(drop (S n) O (CHead x (Bind Void) t) (CHead d2 (Bind Abbr) u1))) (\lambda 
(d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (_: A).(drop (S n) O (CHead x (Bind Void) t) (CHead d2 (Bind 
Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 
d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
(asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 
u1 a)))))) (\lambda (x0: C).(\lambda (H12: (drop n O x (CHead x0 (Bind Abbr) 
u1))).(\lambda (H13: (csuba g x0 d1)).(let H14 \def (refl_equal nat (r (Bind 
Abst) n)) in (let H15 \def (eq_ind nat n (\lambda (n0: nat).(drop n0 O x 
(CHead x0 (Bind Abbr) u1))) H12 (r (Bind Abst) n) H14) in (or_introl (ex2 C 
(\lambda (d2: C).(drop (S n) O (CHead x (Bind Void) t) (CHead d2 (Bind Abbr) 
u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O (CHead x (Bind Void) t) 
(CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: 
A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a))))) (ex_intro2 C (\lambda (d2: C).(drop (S n) O 
(CHead x (Bind Void) t) (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g 
d2 d1)) x0 (drop_drop (Bind Void) n x (CHead x0 (Bind Abbr) u1) H15 t) 
H13))))))) H11)) (\lambda (H11: (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (_: A).(drop n O x (CHead d2 (Bind Abst) u2))))) (\lambda (d2: 
C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a)))))).(ex4_3_ind C T 
A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop n O x (CHead d2 
(Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g 
d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
(asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 
u1 a)))) (or (ex2 C (\lambda (d2: C).(drop (S n) O (CHead x (Bind Void) t) 
(CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O (CHead x 
(Bind Void) t) (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda 
(_: T).(\lambda (a: A).(arity g d1 u1 a)))))) (\lambda (x0: C).(\lambda (x1: 
T).(\lambda (x2: A).(\lambda (H12: (drop n O x (CHead x0 (Bind Abst) 
x1))).(\lambda (H13: (csuba g x0 d1)).(\lambda (H14: (arity g x0 x1 (asucc g 
x2))).(\lambda (H15: (arity g d1 u1 x2)).(let H16 \def (refl_equal nat (r 
(Bind Abst) n)) in (let H17 \def (eq_ind nat n (\lambda (n0: nat).(drop n0 O 
x (CHead x0 (Bind Abst) x1))) H12 (r (Bind Abst) n) H16) in (or_intror (ex2 C 
(\lambda (d2: C).(drop (S n) O (CHead x (Bind Void) t) (CHead d2 (Bind Abbr) 
u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O (CHead x (Bind Void) t) 
(CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: 
A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a))))) (ex4_3_intro C T A (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (_: A).(drop (S n) O (CHead x (Bind Void) t) (CHead d2 (Bind 
Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 
d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
(asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 
u1 a)))) x0 x1 x2 (drop_drop (Bind Void) n x (CHead x0 (Bind Abst) x1) H17 t) 
H13 H14 H15))))))))))) H11)) H10)) c2 H8)))) H7))))) b H3 H4)))) (\lambda (f: 
F).(\lambda (H3: (csuba g c2 (CHead c (Flat f) t))).(\lambda (H4: (drop (r 
(Flat f) n) O c (CHead d1 (Bind Abbr) u1))).(let H_x \def (csuba_gen_flat_rev 
g c c2 t f H3) in (let H5 \def H_x in (ex2_2_ind C T (\lambda (d2: 
C).(\lambda (u2: T).(eq C c2 (CHead d2 (Flat f) u2)))) (\lambda (d2: 
C).(\lambda (_: T).(csuba g d2 c))) (or (ex2 C (\lambda (d2: C).(drop (S n) O 
c2 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T 
A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O c2 (CHead 
d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: 
A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a)))))) (\lambda (x0: C).(\lambda (x1: T).(\lambda (H6: 
(eq C c2 (CHead x0 (Flat f) x1))).(\lambda (H7: (csuba g x0 c)).(eq_ind_r C 
(CHead x0 (Flat f) x1) (\lambda (c0: C).(or (ex2 C (\lambda (d2: C).(drop (S 
n) O c0 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 
C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O c0 
(CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: 
A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a))))))) (let H8 \def (H0 d1 u1 H4 g x0 H7) in (or_ind 
(ex2 C (\lambda (d2: C).(drop (S n) O x0 (CHead d2 (Bind Abbr) u1))) (\lambda 
(d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (_: A).(drop (S n) O x0 (CHead d2 (Bind Abst) u2))))) (\lambda 
(d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a))))) (or (ex2 C 
(\lambda (d2: C).(drop (S n) O (CHead x0 (Flat f) x1) (CHead d2 (Bind Abbr) 
u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O (CHead x0 (Flat f) x1) 
(CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: 
A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a)))))) (\lambda (H9: (ex2 C (\lambda (d2: C).(drop (S 
n) O x0 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 
d1)))).(ex2_ind C (\lambda (d2: C).(drop (S n) O x0 (CHead d2 (Bind Abbr) 
u1))) (\lambda (d2: C).(csuba g d2 d1)) (or (ex2 C (\lambda (d2: C).(drop (S 
n) O (CHead x0 (Flat f) x1) (CHead d2 (Bind Abbr) u1))) (\lambda (d2: 
C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda 
(_: A).(drop (S n) O (CHead x0 (Flat f) x1) (CHead d2 (Bind Abst) u2))))) 
(\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a)))))) 
(\lambda (x: C).(\lambda (H10: (drop (S n) O x0 (CHead x (Bind Abbr) 
u1))).(\lambda (H11: (csuba g x d1)).(or_introl (ex2 C (\lambda (d2: C).(drop 
(S n) O (CHead x0 (Flat f) x1) (CHead d2 (Bind Abbr) u1))) (\lambda (d2: 
C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda 
(_: A).(drop (S n) O (CHead x0 (Flat f) x1) (CHead d2 (Bind Abst) u2))))) 
(\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a))))) 
(ex_intro2 C (\lambda (d2: C).(drop (S n) O (CHead x0 (Flat f) x1) (CHead d2 
(Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1)) x (drop_drop (Flat f) n 
x0 (CHead x (Bind Abbr) u1) H10 x1) H11))))) H9)) (\lambda (H9: (ex4_3 C T A 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O x0 (CHead d2 
(Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g 
d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
(asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 
u1 a)))))).(ex4_3_ind C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: 
A).(drop (S n) O x0 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda 
(_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda 
(_: T).(\lambda (a: A).(arity g d1 u1 a)))) (or (ex2 C (\lambda (d2: C).(drop 
(S n) O (CHead x0 (Flat f) x1) (CHead d2 (Bind Abbr) u1))) (\lambda (d2: 
C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda 
(_: A).(drop (S n) O (CHead x0 (Flat f) x1) (CHead d2 (Bind Abst) u2))))) 
(\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a)))))) 
(\lambda (x2: C).(\lambda (x3: T).(\lambda (x4: A).(\lambda (H10: (drop (S n) 
O x0 (CHead x2 (Bind Abst) x3))).(\lambda (H11: (csuba g x2 d1)).(\lambda 
(H12: (arity g x2 x3 (asucc g x4))).(\lambda (H13: (arity g d1 u1 
x4)).(or_intror (ex2 C (\lambda (d2: C).(drop (S n) O (CHead x0 (Flat f) x1) 
(CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O (CHead x0 
(Flat f) x1) (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda 
(_: T).(\lambda (a: A).(arity g d1 u1 a))))) (ex4_3_intro C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O (CHead x0 (Flat f) x1) 
(CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: 
A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a)))) x2 x3 x4 (drop_drop (Flat f) n x0 (CHead x2 (Bind 
Abst) x3) H10 x1) H11 H12 H13))))))))) H9)) H8)) c2 H6))))) H5)))))) k H2 
(drop_gen_drop k c (CHead d1 (Bind Abbr) u1) t n H1)))))))))))) c1)))) i).

theorem csuba_getl_abst_rev:
 \forall (g: G).(\forall (c1: C).(\forall (d1: C).(\forall (u: T).(\forall 
(i: nat).((getl i c1 (CHead d1 (Bind Abst) u)) \to (\forall (c2: C).((csuba g 
c2 c1) \to (ex2 C (\lambda (d2: C).(getl i c2 (CHead d2 (Bind Abst) u))) 
(\lambda (d2: C).(csuba g d2 d1))))))))))
\def
 \lambda (g: G).(\lambda (c1: C).(\lambda (d1: C).(\lambda (u: T).(\lambda 
(i: nat).(\lambda (H: (getl i c1 (CHead d1 (Bind Abst) u))).(let H0 \def 
(getl_gen_all c1 (CHead d1 (Bind Abst) u) i H) in (ex2_ind C (\lambda (e: 
C).(drop i O c1 e)) (\lambda (e: C).(clear e (CHead d1 (Bind Abst) u))) 
(\forall (c2: C).((csuba g c2 c1) \to (ex2 C (\lambda (d2: C).(getl i c2 
(CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1))))) (\lambda (x: 
C).(\lambda (H1: (drop i O c1 x)).(\lambda (H2: (clear x (CHead d1 (Bind 
Abst) u))).((match x in C return (\lambda (c: C).((drop i O c1 c) \to ((clear 
c (CHead d1 (Bind Abst) u)) \to (\forall (c2: C).((csuba g c2 c1) \to (ex2 C 
(\lambda (d2: C).(getl i c2 (CHead d2 (Bind Abst) u))) (\lambda (d2: 
C).(csuba g d2 d1)))))))) with [(CSort n) \Rightarrow (\lambda (_: (drop i O 
c1 (CSort n))).(\lambda (H4: (clear (CSort n) (CHead d1 (Bind Abst) 
u))).(clear_gen_sort (CHead d1 (Bind Abst) u) n H4 (\forall (c2: C).((csuba g 
c2 c1) \to (ex2 C (\lambda (d2: C).(getl i c2 (CHead d2 (Bind Abst) u))) 
(\lambda (d2: C).(csuba g d2 d1)))))))) | (CHead c k t) \Rightarrow (\lambda 
(H3: (drop i O c1 (CHead c k t))).(\lambda (H4: (clear (CHead c k t) (CHead 
d1 (Bind Abst) u))).((match k in K return (\lambda (k0: K).((drop i O c1 
(CHead c k0 t)) \to ((clear (CHead c k0 t) (CHead d1 (Bind Abst) u)) \to 
(\forall (c2: C).((csuba g c2 c1) \to (ex2 C (\lambda (d2: C).(getl i c2 
(CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1)))))))) with 
[(Bind b) \Rightarrow (\lambda (H5: (drop i O c1 (CHead c (Bind b) 
t))).(\lambda (H6: (clear (CHead c (Bind b) t) (CHead d1 (Bind Abst) 
u))).(let H7 \def (f_equal C C (\lambda (e: C).(match e in C return (\lambda 
(_: C).C) with [(CSort _) \Rightarrow d1 | (CHead c0 _ _) \Rightarrow c0])) 
(CHead d1 (Bind Abst) u) (CHead c (Bind b) t) (clear_gen_bind b c (CHead d1 
(Bind Abst) u) t H6)) in ((let H8 \def (f_equal C B (\lambda (e: C).(match e 
in C return (\lambda (_: C).B) with [(CSort _) \Rightarrow Abst | (CHead _ k0 
_) \Rightarrow (match k0 in K return (\lambda (_: K).B) with [(Bind b0) 
\Rightarrow b0 | (Flat _) \Rightarrow Abst])])) (CHead d1 (Bind Abst) u) 
(CHead c (Bind b) t) (clear_gen_bind b c (CHead d1 (Bind Abst) u) t H6)) in 
((let H9 \def (f_equal C T (\lambda (e: C).(match e in C return (\lambda (_: 
C).T) with [(CSort _) \Rightarrow u | (CHead _ _ t0) \Rightarrow t0])) (CHead 
d1 (Bind Abst) u) (CHead c (Bind b) t) (clear_gen_bind b c (CHead d1 (Bind 
Abst) u) t H6)) in (\lambda (H10: (eq B Abst b)).(\lambda (H11: (eq C d1 
c)).(\lambda (c2: C).(\lambda (H12: (csuba g c2 c1)).(let H13 \def (eq_ind_r 
T t (\lambda (t0: T).(drop i O c1 (CHead c (Bind b) t0))) H5 u H9) in (let 
H14 \def (eq_ind_r B b (\lambda (b0: B).(drop i O c1 (CHead c (Bind b0) u))) 
H13 Abst H10) in (let H15 \def (eq_ind_r C c (\lambda (c0: C).(drop i O c1 
(CHead c0 (Bind Abst) u))) H14 d1 H11) in (let H16 \def (csuba_drop_abst_rev 
i c1 d1 u H15 g c2 H12) in (ex2_ind C (\lambda (d2: C).(drop i O c2 (CHead d2 
(Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1)) (ex2 C (\lambda (d2: 
C).(getl i c2 (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1))) 
(\lambda (x0: C).(\lambda (H17: (drop i O c2 (CHead x0 (Bind Abst) 
u))).(\lambda (H18: (csuba g x0 d1)).(ex_intro2 C (\lambda (d2: C).(getl i c2 
(CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1)) x0 (getl_intro i 
c2 (CHead x0 (Bind Abst) u) (CHead x0 (Bind Abst) u) H17 (clear_bind Abst x0 
u)) H18)))) H16)))))))))) H8)) H7)))) | (Flat f) \Rightarrow (\lambda (H5: 
(drop i O c1 (CHead c (Flat f) t))).(\lambda (H6: (clear (CHead c (Flat f) t) 
(CHead d1 (Bind Abst) u))).(let H7 \def H5 in (unintro C c1 (\lambda (c0: 
C).((drop i O c0 (CHead c (Flat f) t)) \to (\forall (c2: C).((csuba g c2 c0) 
\to (ex2 C (\lambda (d2: C).(getl i c2 (CHead d2 (Bind Abst) u))) (\lambda 
(d2: C).(csuba g d2 d1))))))) (nat_ind (\lambda (n: nat).(\forall (x0: 
C).((drop n O x0 (CHead c (Flat f) t)) \to (\forall (c2: C).((csuba g c2 x0) 
\to (ex2 C (\lambda (d2: C).(getl n c2 (CHead d2 (Bind Abst) u))) (\lambda 
(d2: C).(csuba g d2 d1)))))))) (\lambda (x0: C).(\lambda (H8: (drop O O x0 
(CHead c (Flat f) t))).(\lambda (c2: C).(\lambda (H9: (csuba g c2 x0)).(let 
H10 \def (eq_ind C x0 (\lambda (c0: C).(csuba g c2 c0)) H9 (CHead c (Flat f) 
t) (drop_gen_refl x0 (CHead c (Flat f) t) H8)) in (let H_y \def (clear_flat c 
(CHead d1 (Bind Abst) u) (clear_gen_flat f c (CHead d1 (Bind Abst) u) t H6) f 
t) in (let H11 \def (csuba_clear_trans g (CHead c (Flat f) t) c2 H10 (CHead 
d1 (Bind Abst) u) H_y) in (ex2_ind C (\lambda (e2: C).(csuba g e2 (CHead d1 
(Bind Abst) u))) (\lambda (e2: C).(clear c2 e2)) (ex2 C (\lambda (d2: 
C).(getl O c2 (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1))) 
(\lambda (x1: C).(\lambda (H12: (csuba g x1 (CHead d1 (Bind Abst) 
u))).(\lambda (H13: (clear c2 x1)).(let H_x \def (csuba_gen_abst_rev g d1 x1 
u H12) in (let H14 \def H_x in (ex2_ind C (\lambda (d2: C).(eq C x1 (CHead d2 
(Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1)) (ex2 C (\lambda (d2: 
C).(getl O c2 (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1))) 
(\lambda (x2: C).(\lambda (H15: (eq C x1 (CHead x2 (Bind Abst) u))).(\lambda 
(H16: (csuba g x2 d1)).(let H17 \def (eq_ind C x1 (\lambda (c0: C).(clear c2 
c0)) H13 (CHead x2 (Bind Abst) u) H15) in (ex_intro2 C (\lambda (d2: C).(getl 
O c2 (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1)) x2 
(getl_intro O c2 (CHead x2 (Bind Abst) u) c2 (drop_refl c2) H17) H16))))) 
H14)))))) H11)))))))) (\lambda (n: nat).(\lambda (H8: ((\forall (x0: 
C).((drop n O x0 (CHead c (Flat f) t)) \to (\forall (c2: C).((csuba g c2 x0) 
\to (ex2 C (\lambda (d2: C).(getl n c2 (CHead d2 (Bind Abst) u))) (\lambda 
(d2: C).(csuba g d2 d1))))))))).(\lambda (x0: C).(\lambda (H9: (drop (S n) O 
x0 (CHead c (Flat f) t))).(\lambda (c2: C).(\lambda (H10: (csuba g c2 
x0)).(let H11 \def (drop_clear x0 (CHead c (Flat f) t) n H9) in (ex2_3_ind B 
C T (\lambda (b: B).(\lambda (e: C).(\lambda (v: T).(clear x0 (CHead e (Bind 
b) v))))) (\lambda (_: B).(\lambda (e: C).(\lambda (_: T).(drop n O e (CHead 
c (Flat f) t))))) (ex2 C (\lambda (d2: C).(getl (S n) c2 (CHead d2 (Bind 
Abst) u))) (\lambda (d2: C).(csuba g d2 d1))) (\lambda (x1: B).(\lambda (x2: 
C).(\lambda (x3: T).(\lambda (H12: (clear x0 (CHead x2 (Bind x1) 
x3))).(\lambda (H13: (drop n O x2 (CHead c (Flat f) t))).(let H14 \def 
(csuba_clear_trans g x0 c2 H10 (CHead x2 (Bind x1) x3) H12) in (ex2_ind C 
(\lambda (e2: C).(csuba g e2 (CHead x2 (Bind x1) x3))) (\lambda (e2: 
C).(clear c2 e2)) (ex2 C (\lambda (d2: C).(getl (S n) c2 (CHead d2 (Bind 
Abst) u))) (\lambda (d2: C).(csuba g d2 d1))) (\lambda (x4: C).(\lambda (H15: 
(csuba g x4 (CHead x2 (Bind x1) x3))).(\lambda (H16: (clear c2 x4)).(let H_x 
\def (csuba_gen_bind_rev g x1 x2 x4 x3 H15) in (let H17 \def H_x in 
(ex2_3_ind B C T (\lambda (b2: B).(\lambda (e2: C).(\lambda (v2: T).(eq C x4 
(CHead e2 (Bind b2) v2))))) (\lambda (_: B).(\lambda (e2: C).(\lambda (_: 
T).(csuba g e2 x2)))) (ex2 C (\lambda (d2: C).(getl (S n) c2 (CHead d2 (Bind 
Abst) u))) (\lambda (d2: C).(csuba g d2 d1))) (\lambda (x5: B).(\lambda (x6: 
C).(\lambda (x7: T).(\lambda (H18: (eq C x4 (CHead x6 (Bind x5) 
x7))).(\lambda (H19: (csuba g x6 x2)).(let H20 \def (eq_ind C x4 (\lambda 
(c0: C).(clear c2 c0)) H16 (CHead x6 (Bind x5) x7) H18) in (let H21 \def (H8 
x2 H13 x6 H19) in (ex2_ind C (\lambda (d2: C).(getl n x6 (CHead d2 (Bind 
Abst) u))) (\lambda (d2: C).(csuba g d2 d1)) (ex2 C (\lambda (d2: C).(getl (S 
n) c2 (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1))) (\lambda 
(x8: C).(\lambda (H22: (getl n x6 (CHead x8 (Bind Abst) u))).(\lambda (H23: 
(csuba g x8 d1)).(ex_intro2 C (\lambda (d2: C).(getl (S n) c2 (CHead d2 (Bind 
Abst) u))) (\lambda (d2: C).(csuba g d2 d1)) x8 (getl_clear_bind x5 c2 x6 x7 
H20 (CHead x8 (Bind Abst) u) n H22) H23)))) H21)))))))) H17)))))) H14))))))) 
H11)))))))) i) H7))))]) H3 H4)))]) H1 H2)))) H0))))))).

theorem csuba_getl_abbr_rev:
 \forall (g: G).(\forall (c1: C).(\forall (d1: C).(\forall (u1: T).(\forall 
(i: nat).((getl i c1 (CHead d1 (Bind Abbr) u1)) \to (\forall (c2: C).((csuba 
g c2 c1) \to (or (ex2 C (\lambda (d2: C).(getl i c2 (CHead d2 (Bind Abbr) 
u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(getl i c2 (CHead d2 (Bind Abst) u2))))) 
(\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a)))))))))))))
\def
 \lambda (g: G).(\lambda (c1: C).(\lambda (d1: C).(\lambda (u1: T).(\lambda 
(i: nat).(\lambda (H: (getl i c1 (CHead d1 (Bind Abbr) u1))).(let H0 \def 
(getl_gen_all c1 (CHead d1 (Bind Abbr) u1) i H) in (ex2_ind C (\lambda (e: 
C).(drop i O c1 e)) (\lambda (e: C).(clear e (CHead d1 (Bind Abbr) u1))) 
(\forall (c2: C).((csuba g c2 c1) \to (or (ex2 C (\lambda (d2: C).(getl i c2 
(CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(getl i c2 (CHead d2 (Bind 
Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 
d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
(asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 
u1 a)))))))) (\lambda (x: C).(\lambda (H1: (drop i O c1 x)).(\lambda (H2: 
(clear x (CHead d1 (Bind Abbr) u1))).((match x in C return (\lambda (c: 
C).((drop i O c1 c) \to ((clear c (CHead d1 (Bind Abbr) u1)) \to (\forall 
(c2: C).((csuba g c2 c1) \to (or (ex2 C (\lambda (d2: C).(getl i c2 (CHead d2 
(Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (_: A).(getl i c2 (CHead d2 (Bind Abst) 
u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g 
a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 
a))))))))))) with [(CSort n) \Rightarrow (\lambda (_: (drop i O c1 (CSort 
n))).(\lambda (H4: (clear (CSort n) (CHead d1 (Bind Abbr) 
u1))).(clear_gen_sort (CHead d1 (Bind Abbr) u1) n H4 (\forall (c2: C).((csuba 
g c2 c1) \to (or (ex2 C (\lambda (d2: C).(getl i c2 (CHead d2 (Bind Abbr) 
u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(getl i c2 (CHead d2 (Bind Abst) u2))))) 
(\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a))))))))))) | 
(CHead c k t) \Rightarrow (\lambda (H3: (drop i O c1 (CHead c k t))).(\lambda 
(H4: (clear (CHead c k t) (CHead d1 (Bind Abbr) u1))).((match k in K return 
(\lambda (k0: K).((drop i O c1 (CHead c k0 t)) \to ((clear (CHead c k0 t) 
(CHead d1 (Bind Abbr) u1)) \to (\forall (c2: C).((csuba g c2 c1) \to (or (ex2 
C (\lambda (d2: C).(getl i c2 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: 
C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda 
(_: A).(getl i c2 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda 
(_: T).(\lambda (a: A).(arity g d1 u1 a))))))))))) with [(Bind b) \Rightarrow 
(\lambda (H5: (drop i O c1 (CHead c (Bind b) t))).(\lambda (H6: (clear (CHead 
c (Bind b) t) (CHead d1 (Bind Abbr) u1))).(let H7 \def (f_equal C C (\lambda 
(e: C).(match e in C return (\lambda (_: C).C) with [(CSort _) \Rightarrow d1 
| (CHead c0 _ _) \Rightarrow c0])) (CHead d1 (Bind Abbr) u1) (CHead c (Bind 
b) t) (clear_gen_bind b c (CHead d1 (Bind Abbr) u1) t H6)) in ((let H8 \def 
(f_equal C B (\lambda (e: C).(match e in C return (\lambda (_: C).B) with 
[(CSort _) \Rightarrow Abbr | (CHead _ k0 _) \Rightarrow (match k0 in K 
return (\lambda (_: K).B) with [(Bind b0) \Rightarrow b0 | (Flat _) 
\Rightarrow Abbr])])) (CHead d1 (Bind Abbr) u1) (CHead c (Bind b) t) 
(clear_gen_bind b c (CHead d1 (Bind Abbr) u1) t H6)) in ((let H9 \def 
(f_equal C T (\lambda (e: C).(match e in C return (\lambda (_: C).T) with 
[(CSort _) \Rightarrow u1 | (CHead _ _ t0) \Rightarrow t0])) (CHead d1 (Bind 
Abbr) u1) (CHead c (Bind b) t) (clear_gen_bind b c (CHead d1 (Bind Abbr) u1) 
t H6)) in (\lambda (H10: (eq B Abbr b)).(\lambda (H11: (eq C d1 c)).(\lambda 
(c2: C).(\lambda (H12: (csuba g c2 c1)).(let H13 \def (eq_ind_r T t (\lambda 
(t0: T).(drop i O c1 (CHead c (Bind b) t0))) H5 u1 H9) in (let H14 \def 
(eq_ind_r B b (\lambda (b0: B).(drop i O c1 (CHead c (Bind b0) u1))) H13 Abbr 
H10) in (let H15 \def (eq_ind_r C c (\lambda (c0: C).(drop i O c1 (CHead c0 
(Bind Abbr) u1))) H14 d1 H11) in (let H16 \def (csuba_drop_abbr_rev i c1 d1 
u1 H15 g c2 H12) in (or_ind (ex2 C (\lambda (d2: C).(drop i O c2 (CHead d2 
(Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (_: A).(drop i O c2 (CHead d2 (Bind Abst) 
u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g 
a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a))))) 
(or (ex2 C (\lambda (d2: C).(getl i c2 (CHead d2 (Bind Abbr) u1))) (\lambda 
(d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (_: A).(getl i c2 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: 
C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a)))))) (\lambda (H17: 
(ex2 C (\lambda (d2: C).(drop i O c2 (CHead d2 (Bind Abbr) u1))) (\lambda 
(d2: C).(csuba g d2 d1)))).(ex2_ind C (\lambda (d2: C).(drop i O c2 (CHead d2 
(Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1)) (or (ex2 C (\lambda (d2: 
C).(getl i c2 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) 
(ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(getl i c2 
(CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: 
A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a)))))) (\lambda (x0: C).(\lambda (H18: (drop i O c2 
(CHead x0 (Bind Abbr) u1))).(\lambda (H19: (csuba g x0 d1)).(or_introl (ex2 C 
(\lambda (d2: C).(getl i c2 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: 
C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda 
(_: A).(getl i c2 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda 
(_: T).(\lambda (a: A).(arity g d1 u1 a))))) (ex_intro2 C (\lambda (d2: 
C).(getl i c2 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1)) 
x0 (getl_intro i c2 (CHead x0 (Bind Abbr) u1) (CHead x0 (Bind Abbr) u1) H18 
(clear_bind Abbr x0 u1)) H19))))) H17)) (\lambda (H17: (ex4_3 C T A (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (_: A).(drop i O c2 (CHead d2 (Bind Abst) 
u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g 
a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 
a)))))).(ex4_3_ind C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: 
A).(drop i O c2 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda 
(_: T).(\lambda (a: A).(arity g d1 u1 a)))) (or (ex2 C (\lambda (d2: C).(getl 
i c2 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C 
T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(getl i c2 (CHead d2 
(Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g 
d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
(asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 
u1 a)))))) (\lambda (x0: C).(\lambda (x1: T).(\lambda (x2: A).(\lambda (H18: 
(drop i O c2 (CHead x0 (Bind Abst) x1))).(\lambda (H19: (csuba g x0 
d1)).(\lambda (H20: (arity g x0 x1 (asucc g x2))).(\lambda (H21: (arity g d1 
u1 x2)).(or_intror (ex2 C (\lambda (d2: C).(getl i c2 (CHead d2 (Bind Abbr) 
u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(getl i c2 (CHead d2 (Bind Abst) u2))))) 
(\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a))))) 
(ex4_3_intro C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(getl i 
c2 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda 
(_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a)))) x0 x1 x2 (getl_intro i c2 (CHead x0 (Bind Abst) 
x1) (CHead x0 (Bind Abst) x1) H18 (clear_bind Abst x0 x1)) H19 H20 
H21))))))))) H17)) H16)))))))))) H8)) H7)))) | (Flat f) \Rightarrow (\lambda 
(H5: (drop i O c1 (CHead c (Flat f) t))).(\lambda (H6: (clear (CHead c (Flat 
f) t) (CHead d1 (Bind Abbr) u1))).(let H7 \def H5 in (unintro C c1 (\lambda 
(c0: C).((drop i O c0 (CHead c (Flat f) t)) \to (\forall (c2: C).((csuba g c2 
c0) \to (or (ex2 C (\lambda (d2: C).(getl i c2 (CHead d2 (Bind Abbr) u1))) 
(\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (_: A).(getl i c2 (CHead d2 (Bind Abst) u2))))) (\lambda 
(d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a)))))))))) (nat_ind 
(\lambda (n: nat).(\forall (x0: C).((drop n O x0 (CHead c (Flat f) t)) \to 
(\forall (c2: C).((csuba g c2 x0) \to (or (ex2 C (\lambda (d2: C).(getl n c2 
(CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(getl n c2 (CHead d2 (Bind 
Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 
d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
(asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 
u1 a))))))))))) (\lambda (x0: C).(\lambda (H8: (drop O O x0 (CHead c (Flat f) 
t))).(\lambda (c2: C).(\lambda (H9: (csuba g c2 x0)).(let H10 \def (eq_ind C 
x0 (\lambda (c0: C).(csuba g c2 c0)) H9 (CHead c (Flat f) t) (drop_gen_refl 
x0 (CHead c (Flat f) t) H8)) in (let H_y \def (clear_flat c (CHead d1 (Bind 
Abbr) u1) (clear_gen_flat f c (CHead d1 (Bind Abbr) u1) t H6) f t) in (let 
H11 \def (csuba_clear_trans g (CHead c (Flat f) t) c2 H10 (CHead d1 (Bind 
Abbr) u1) H_y) in (ex2_ind C (\lambda (e2: C).(csuba g e2 (CHead d1 (Bind 
Abbr) u1))) (\lambda (e2: C).(clear c2 e2)) (or (ex2 C (\lambda (d2: C).(getl 
O c2 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C 
T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(getl O c2 (CHead d2 
(Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g 
d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
(asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 
u1 a)))))) (\lambda (x1: C).(\lambda (H12: (csuba g x1 (CHead d1 (Bind Abbr) 
u1))).(\lambda (H13: (clear c2 x1)).(let H_x \def (csuba_gen_abbr_rev g d1 x1 
u1 H12) in (let H14 \def H_x in (or_ind (ex2 C (\lambda (d2: C).(eq C x1 
(CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(eq C x1 (CHead d2 (Bind 
Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 
d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
(asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 
u1 a))))) (or (ex2 C (\lambda (d2: C).(getl O c2 (CHead d2 (Bind Abbr) u1))) 
(\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (_: A).(getl O c2 (CHead d2 (Bind Abst) u2))))) (\lambda 
(d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a)))))) (\lambda (H15: 
(ex2 C (\lambda (d2: C).(eq C x1 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: 
C).(csuba g d2 d1)))).(ex2_ind C (\lambda (d2: C).(eq C x1 (CHead d2 (Bind 
Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1)) (or (ex2 C (\lambda (d2: 
C).(getl O c2 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) 
(ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(getl O c2 
(CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: 
A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a)))))) (\lambda (x2: C).(\lambda (H16: (eq C x1 (CHead 
x2 (Bind Abbr) u1))).(\lambda (H17: (csuba g x2 d1)).(let H18 \def (eq_ind C 
x1 (\lambda (c0: C).(clear c2 c0)) H13 (CHead x2 (Bind Abbr) u1) H16) in 
(or_introl (ex2 C (\lambda (d2: C).(getl O c2 (CHead d2 (Bind Abbr) u1))) 
(\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (_: A).(getl O c2 (CHead d2 (Bind Abst) u2))))) (\lambda 
(d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a))))) (ex_intro2 C 
(\lambda (d2: C).(getl O c2 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: 
C).(csuba g d2 d1)) x2 (getl_intro O c2 (CHead x2 (Bind Abbr) u1) c2 
(drop_refl c2) H18) H17)))))) H15)) (\lambda (H15: (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(eq C x1 (CHead d2 (Bind Abst) u2))))) 
(\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 
a)))))).(ex4_3_ind C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: 
A).(eq C x1 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda 
(_: T).(\lambda (a: A).(arity g d1 u1 a)))) (or (ex2 C (\lambda (d2: C).(getl 
O c2 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C 
T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(getl O c2 (CHead d2 
(Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g 
d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
(asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 
u1 a)))))) (\lambda (x2: C).(\lambda (x3: T).(\lambda (x4: A).(\lambda (H16: 
(eq C x1 (CHead x2 (Bind Abst) x3))).(\lambda (H17: (csuba g x2 d1)).(\lambda 
(H18: (arity g x2 x3 (asucc g x4))).(\lambda (H19: (arity g d1 u1 x4)).(let 
H20 \def (eq_ind C x1 (\lambda (c0: C).(clear c2 c0)) H13 (CHead x2 (Bind 
Abst) x3) H16) in (or_intror (ex2 C (\lambda (d2: C).(getl O c2 (CHead d2 
(Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (_: A).(getl O c2 (CHead d2 (Bind Abst) 
u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g 
a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a))))) 
(ex4_3_intro C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(getl O 
c2 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda 
(_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a)))) x2 x3 x4 (getl_intro O c2 (CHead x2 (Bind Abst) 
x3) c2 (drop_refl c2) H20) H17 H18 H19)))))))))) H15)) H14)))))) H11)))))))) 
(\lambda (n: nat).(\lambda (H8: ((\forall (x0: C).((drop n O x0 (CHead c 
(Flat f) t)) \to (\forall (c2: C).((csuba g c2 x0) \to (or (ex2 C (\lambda 
(d2: C).(getl n c2 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 
d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(getl n 
c2 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda 
(_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a)))))))))))).(\lambda (x0: C).(\lambda (H9: (drop (S 
n) O x0 (CHead c (Flat f) t))).(\lambda (c2: C).(\lambda (H10: (csuba g c2 
x0)).(let H11 \def (drop_clear x0 (CHead c (Flat f) t) n H9) in (ex2_3_ind B 
C T (\lambda (b: B).(\lambda (e: C).(\lambda (v: T).(clear x0 (CHead e (Bind 
b) v))))) (\lambda (_: B).(\lambda (e: C).(\lambda (_: T).(drop n O e (CHead 
c (Flat f) t))))) (or (ex2 C (\lambda (d2: C).(getl (S n) c2 (CHead d2 (Bind 
Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(getl (S n) c2 (CHead d2 (Bind Abst) 
u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g 
a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a)))))) 
(\lambda (x1: B).(\lambda (x2: C).(\lambda (x3: T).(\lambda (H12: (clear x0 
(CHead x2 (Bind x1) x3))).(\lambda (H13: (drop n O x2 (CHead c (Flat f) 
t))).(let H14 \def (csuba_clear_trans g x0 c2 H10 (CHead x2 (Bind x1) x3) 
H12) in (ex2_ind C (\lambda (e2: C).(csuba g e2 (CHead x2 (Bind x1) x3))) 
(\lambda (e2: C).(clear c2 e2)) (or (ex2 C (\lambda (d2: C).(getl (S n) c2 
(CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(getl (S n) c2 (CHead d2 
(Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g 
d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
(asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 
u1 a)))))) (\lambda (x4: C).(\lambda (H15: (csuba g x4 (CHead x2 (Bind x1) 
x3))).(\lambda (H16: (clear c2 x4)).(let H_x \def (csuba_gen_bind_rev g x1 x2 
x4 x3 H15) in (let H17 \def H_x in (ex2_3_ind B C T (\lambda (b2: B).(\lambda 
(e2: C).(\lambda (v2: T).(eq C x4 (CHead e2 (Bind b2) v2))))) (\lambda (_: 
B).(\lambda (e2: C).(\lambda (_: T).(csuba g e2 x2)))) (or (ex2 C (\lambda 
(d2: C).(getl (S n) c2 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g 
d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(getl 
(S n) c2 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda 
(_: T).(\lambda (a: A).(arity g d1 u1 a)))))) (\lambda (x5: B).(\lambda (x6: 
C).(\lambda (x7: T).(\lambda (H18: (eq C x4 (CHead x6 (Bind x5) 
x7))).(\lambda (H19: (csuba g x6 x2)).(let H20 \def (eq_ind C x4 (\lambda 
(c0: C).(clear c2 c0)) H16 (CHead x6 (Bind x5) x7) H18) in (let H21 \def (H8 
x2 H13 x6 H19) in (or_ind (ex2 C (\lambda (d2: C).(getl n x6 (CHead d2 (Bind 
Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(getl n x6 (CHead d2 (Bind Abst) u2))))) 
(\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a))))) (or 
(ex2 C (\lambda (d2: C).(getl (S n) c2 (CHead d2 (Bind Abbr) u1))) (\lambda 
(d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (_: A).(getl (S n) c2 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: 
C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a)))))) (\lambda (H22: 
(ex2 C (\lambda (d2: C).(getl n x6 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: 
C).(csuba g d2 d1)))).(ex2_ind C (\lambda (d2: C).(getl n x6 (CHead d2 (Bind 
Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1)) (or (ex2 C (\lambda (d2: 
C).(getl (S n) c2 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 
d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(getl (S 
n) c2 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda 
(_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a)))))) (\lambda (x8: C).(\lambda (H23: (getl n x6 
(CHead x8 (Bind Abbr) u1))).(\lambda (H24: (csuba g x8 d1)).(or_introl (ex2 C 
(\lambda (d2: C).(getl (S n) c2 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: 
C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda 
(_: A).(getl (S n) c2 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda 
(_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda 
(_: T).(\lambda (a: A).(arity g d1 u1 a))))) (ex_intro2 C (\lambda (d2: 
C).(getl (S n) c2 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 
d1)) x8 (getl_clear_bind x5 c2 x6 x7 H20 (CHead x8 (Bind Abbr) u1) n H23) 
H24))))) H22)) (\lambda (H22: (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (_: A).(getl n x6 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: 
C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a)))))).(ex4_3_ind C T 
A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(getl n x6 (CHead d2 
(Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g 
d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
(asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 
u1 a)))) (or (ex2 C (\lambda (d2: C).(getl (S n) c2 (CHead d2 (Bind Abbr) 
u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(getl (S n) c2 (CHead d2 (Bind Abst) 
u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g 
a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a)))))) 
(\lambda (x8: C).(\lambda (x9: T).(\lambda (x10: A).(\lambda (H23: (getl n x6 
(CHead x8 (Bind Abst) x9))).(\lambda (H24: (csuba g x8 d1)).(\lambda (H25: 
(arity g x8 x9 (asucc g x10))).(\lambda (H26: (arity g d1 u1 x10)).(or_intror 
(ex2 C (\lambda (d2: C).(getl (S n) c2 (CHead d2 (Bind Abbr) u1))) (\lambda 
(d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (_: A).(getl (S n) c2 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: 
C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a))))) (ex4_3_intro C T 
A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(getl (S n) c2 (CHead d2 
(Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g 
d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
(asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 
u1 a)))) x8 x9 x10 (getl_clear_bind x5 c2 x6 x7 H20 (CHead x8 (Bind Abst) x9) 
n H23) H24 H25 H26))))))))) H22)) H21)))))))) H17)))))) H14))))))) 
H11)))))))) i) H7))))]) H3 H4)))]) H1 H2)))) H0))))))).

theorem sn3_cpr3_trans:
 \forall (c: C).(\forall (u1: T).(\forall (u2: T).((pr3 c u1 u2) \to (\forall 
(k: K).(\forall (t: T).((sn3 (CHead c k u1) t) \to (sn3 (CHead c k u2) 
t)))))))
\def
 \lambda (c: C).(\lambda (u1: T).(\lambda (u2: T).(\lambda (H: (pr3 c u1 
u2)).(\lambda (k: K).(\lambda (t: T).(\lambda (H0: (sn3 (CHead c k u1) 
t)).(sn3_ind (CHead c k u1) (\lambda (t0: T).(sn3 (CHead c k u2) t0)) 
(\lambda (t1: T).(\lambda (_: ((\forall (t2: T).((((eq T t1 t2) \to (\forall 
(P: Prop).P))) \to ((pr3 (CHead c k u1) t1 t2) \to (sn3 (CHead c k u1) 
t2)))))).(\lambda (H2: ((\forall (t2: T).((((eq T t1 t2) \to (\forall (P: 
Prop).P))) \to ((pr3 (CHead c k u1) t1 t2) \to (sn3 (CHead c k u2) 
t2)))))).(sn3_sing (CHead c k u2) t1 (\lambda (t2: T).(\lambda (H3: (((eq T 
t1 t2) \to (\forall (P: Prop).P)))).(\lambda (H4: (pr3 (CHead c k u2) t1 
t2)).(H2 t2 H3 (pr3_pr3_pr3_t c u1 u2 H t1 t2 k H4))))))))) t H0))))))).

theorem sn3_bind:
 \forall (b: B).((not (eq B b Abst)) \to (\forall (c: C).(\forall (u: 
T).((sn3 c u) \to (\forall (t: T).((sn3 (CHead c (Bind b) u) t) \to (sn3 c 
(THead (Bind b) u t))))))))
\def
 \lambda (b: B).(\lambda (H: (not (eq B b Abst))).(\lambda (c: C).(\lambda 
(u: T).(\lambda (H0: (sn3 c u)).(sn3_ind c (\lambda (t: T).(\forall (t0: 
T).((sn3 (CHead c (Bind b) t) t0) \to (sn3 c (THead (Bind b) t t0))))) 
(\lambda (t1: T).(\lambda (_: ((\forall (t2: T).((((eq T t1 t2) \to (\forall 
(P: Prop).P))) \to ((pr3 c t1 t2) \to (sn3 c t2)))))).(\lambda (H2: ((\forall 
(t2: T).((((eq T t1 t2) \to (\forall (P: Prop).P))) \to ((pr3 c t1 t2) \to 
(\forall (t: T).((sn3 (CHead c (Bind b) t2) t) \to (sn3 c (THead (Bind b) t2 
t))))))))).(\lambda (t: T).(\lambda (H3: (sn3 (CHead c (Bind b) t1) 
t)).(sn3_ind (CHead c (Bind b) t1) (\lambda (t0: T).(sn3 c (THead (Bind b) t1 
t0))) (\lambda (t2: T).(\lambda (H4: ((\forall (t3: T).((((eq T t2 t3) \to 
(\forall (P: Prop).P))) \to ((pr3 (CHead c (Bind b) t1) t2 t3) \to (sn3 
(CHead c (Bind b) t1) t3)))))).(\lambda (H5: ((\forall (t3: T).((((eq T t2 
t3) \to (\forall (P: Prop).P))) \to ((pr3 (CHead c (Bind b) t1) t2 t3) \to 
(sn3 c (THead (Bind b) t1 t3))))))).(sn3_sing c (THead (Bind b) t1 t2) 
(\lambda (t3: T).(\lambda (H6: (((eq T (THead (Bind b) t1 t2) t3) \to 
(\forall (P: Prop).P)))).(\lambda (H7: (pr3 c (THead (Bind b) t1 t2) 
t3)).(let H_x \def (pr3_gen_bind b H c t1 t2 t3 H7) in (let H8 \def H_x in 
(or_ind (ex3_2 T T (\lambda (u2: T).(\lambda (t4: T).(eq T t3 (THead (Bind b) 
u2 t4)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c t1 u2))) (\lambda (_: 
T).(\lambda (t4: T).(pr3 (CHead c (Bind b) t1) t2 t4)))) (pr3 (CHead c (Bind 
b) t1) t2 (lift (S O) O t3)) (sn3 c t3) (\lambda (H9: (ex3_2 T T (\lambda 
(u2: T).(\lambda (t4: T).(eq T t3 (THead (Bind b) u2 t4)))) (\lambda (u2: 
T).(\lambda (_: T).(pr3 c t1 u2))) (\lambda (_: T).(\lambda (t4: T).(pr3 
(CHead c (Bind b) t1) t2 t4))))).(ex3_2_ind T T (\lambda (u2: T).(\lambda 
(t4: T).(eq T t3 (THead (Bind b) u2 t4)))) (\lambda (u2: T).(\lambda (_: 
T).(pr3 c t1 u2))) (\lambda (_: T).(\lambda (t4: T).(pr3 (CHead c (Bind b) 
t1) t2 t4))) (sn3 c t3) (\lambda (x0: T).(\lambda (x1: T).(\lambda (H10: (eq 
T t3 (THead (Bind b) x0 x1))).(\lambda (H11: (pr3 c t1 x0)).(\lambda (H12: 
(pr3 (CHead c (Bind b) t1) t2 x1)).(let H13 \def (eq_ind T t3 (\lambda (t0: 
T).((eq T (THead (Bind b) t1 t2) t0) \to (\forall (P: Prop).P))) H6 (THead 
(Bind b) x0 x1) H10) in (eq_ind_r T (THead (Bind b) x0 x1) (\lambda (t0: 
T).(sn3 c t0)) (let H_x0 \def (term_dec t1 x0) in (let H14 \def H_x0 in 
(or_ind (eq T t1 x0) ((eq T t1 x0) \to (\forall (P: Prop).P)) (sn3 c (THead 
(Bind b) x0 x1)) (\lambda (H15: (eq T t1 x0)).(let H16 \def (eq_ind_r T x0 
(\lambda (t0: T).((eq T (THead (Bind b) t1 t2) (THead (Bind b) t0 x1)) \to 
(\forall (P: Prop).P))) H13 t1 H15) in (let H17 \def (eq_ind_r T x0 (\lambda 
(t0: T).(pr3 c t1 t0)) H11 t1 H15) in (eq_ind T t1 (\lambda (t0: T).(sn3 c 
(THead (Bind b) t0 x1))) (let H_x1 \def (term_dec t2 x1) in (let H18 \def 
H_x1 in (or_ind (eq T t2 x1) ((eq T t2 x1) \to (\forall (P: Prop).P)) (sn3 c 
(THead (Bind b) t1 x1)) (\lambda (H19: (eq T t2 x1)).(let H20 \def (eq_ind_r 
T x1 (\lambda (t0: T).((eq T (THead (Bind b) t1 t2) (THead (Bind b) t1 t0)) 
\to (\forall (P: Prop).P))) H16 t2 H19) in (let H21 \def (eq_ind_r T x1 
(\lambda (t0: T).(pr3 (CHead c (Bind b) t1) t2 t0)) H12 t2 H19) in (eq_ind T 
t2 (\lambda (t0: T).(sn3 c (THead (Bind b) t1 t0))) (H20 (refl_equal T (THead 
(Bind b) t1 t2)) (sn3 c (THead (Bind b) t1 t2))) x1 H19)))) (\lambda (H19: 
(((eq T t2 x1) \to (\forall (P: Prop).P)))).(H5 x1 H19 H12)) H18))) x0 
H15)))) (\lambda (H15: (((eq T t1 x0) \to (\forall (P: Prop).P)))).(let H_x1 
\def (term_dec t2 x1) in (let H16 \def H_x1 in (or_ind (eq T t2 x1) ((eq T t2 
x1) \to (\forall (P: Prop).P)) (sn3 c (THead (Bind b) x0 x1)) (\lambda (H17: 
(eq T t2 x1)).(let H18 \def (eq_ind_r T x1 (\lambda (t0: T).(pr3 (CHead c 
(Bind b) t1) t2 t0)) H12 t2 H17) in (eq_ind T t2 (\lambda (t0: T).(sn3 c 
(THead (Bind b) x0 t0))) (H2 x0 H15 H11 t2 (sn3_cpr3_trans c t1 x0 H11 (Bind 
b) t2 (sn3_sing (CHead c (Bind b) t1) t2 H4))) x1 H17))) (\lambda (H17: (((eq 
T t2 x1) \to (\forall (P: Prop).P)))).(H2 x0 H15 H11 x1 (sn3_cpr3_trans c t1 
x0 H11 (Bind b) x1 (H4 x1 H17 H12)))) H16)))) H14))) t3 H10))))))) H9)) 
(\lambda (H9: (pr3 (CHead c (Bind b) t1) t2 (lift (S O) O t3))).(sn3_gen_lift 
(CHead c (Bind b) t1) t3 (S O) O (sn3_pr3_trans (CHead c (Bind b) t1) t2 
(sn3_pr2_intro (CHead c (Bind b) t1) t2 (\lambda (t0: T).(\lambda (H10: (((eq 
T t2 t0) \to (\forall (P: Prop).P)))).(\lambda (H11: (pr2 (CHead c (Bind b) 
t1) t2 t0)).(H4 t0 H10 (pr3_pr2 (CHead c (Bind b) t1) t2 t0 H11)))))) (lift 
(S O) O t3) H9) c (drop_drop (Bind b) O c c (drop_refl c) t1))) H8)))))))))) 
t H3)))))) u H0))))).

theorem sn3_beta:
 \forall (c: C).(\forall (v: T).(\forall (t: T).((sn3 c (THead (Bind Abbr) v 
t)) \to (\forall (w: T).((sn3 c w) \to (sn3 c (THead (Flat Appl) v (THead 
(Bind Abst) w t))))))))
\def
 \lambda (c: C).(\lambda (v: T).(\lambda (t: T).(\lambda (H: (sn3 c (THead 
(Bind Abbr) v t))).(insert_eq T (THead (Bind Abbr) v t) (\lambda (t0: T).(sn3 
c t0)) (\forall (w: T).((sn3 c w) \to (sn3 c (THead (Flat Appl) v (THead 
(Bind Abst) w t))))) (\lambda (y: T).(\lambda (H0: (sn3 c y)).(unintro T t 
(\lambda (t0: T).((eq T y (THead (Bind Abbr) v t0)) \to (\forall (w: T).((sn3 
c w) \to (sn3 c (THead (Flat Appl) v (THead (Bind Abst) w t0))))))) (unintro 
T v (\lambda (t0: T).(\forall (x: T).((eq T y (THead (Bind Abbr) t0 x)) \to 
(\forall (w: T).((sn3 c w) \to (sn3 c (THead (Flat Appl) t0 (THead (Bind 
Abst) w x)))))))) (sn3_ind c (\lambda (t0: T).(\forall (x: T).(\forall (x0: 
T).((eq T t0 (THead (Bind Abbr) x x0)) \to (\forall (w: T).((sn3 c w) \to 
(sn3 c (THead (Flat Appl) x (THead (Bind Abst) w x0))))))))) (\lambda (t1: 
T).(\lambda (H1: ((\forall (t2: T).((((eq T t1 t2) \to (\forall (P: 
Prop).P))) \to ((pr3 c t1 t2) \to (sn3 c t2)))))).(\lambda (H2: ((\forall 
(t2: T).((((eq T t1 t2) \to (\forall (P: Prop).P))) \to ((pr3 c t1 t2) \to 
(\forall (x: T).(\forall (x0: T).((eq T t2 (THead (Bind Abbr) x x0)) \to 
(\forall (w: T).((sn3 c w) \to (sn3 c (THead (Flat Appl) x (THead (Bind Abst) 
w x0))))))))))))).(\lambda (x: T).(\lambda (x0: T).(\lambda (H3: (eq T t1 
(THead (Bind Abbr) x x0))).(\lambda (w: T).(\lambda (H4: (sn3 c w)).(let H5 
\def (eq_ind T t1 (\lambda (t0: T).(\forall (t2: T).((((eq T t0 t2) \to 
(\forall (P: Prop).P))) \to ((pr3 c t0 t2) \to (\forall (x1: T).(\forall (x2: 
T).((eq T t2 (THead (Bind Abbr) x1 x2)) \to (\forall (w0: T).((sn3 c w0) \to 
(sn3 c (THead (Flat Appl) x1 (THead (Bind Abst) w0 x2)))))))))))) H2 (THead 
(Bind Abbr) x x0) H3) in (let H6 \def (eq_ind T t1 (\lambda (t0: T).(\forall 
(t2: T).((((eq T t0 t2) \to (\forall (P: Prop).P))) \to ((pr3 c t0 t2) \to 
(sn3 c t2))))) H1 (THead (Bind Abbr) x x0) H3) in (sn3_ind c (\lambda (t0: 
T).(sn3 c (THead (Flat Appl) x (THead (Bind Abst) t0 x0)))) (\lambda (t2: 
T).(\lambda (H7: ((\forall (t3: T).((((eq T t2 t3) \to (\forall (P: 
Prop).P))) \to ((pr3 c t2 t3) \to (sn3 c t3)))))).(\lambda (H8: ((\forall 
(t3: T).((((eq T t2 t3) \to (\forall (P: Prop).P))) \to ((pr3 c t2 t3) \to 
(sn3 c (THead (Flat Appl) x (THead (Bind Abst) t3 x0)))))))).(sn3_pr2_intro c 
(THead (Flat Appl) x (THead (Bind Abst) t2 x0)) (\lambda (t3: T).(\lambda 
(H9: (((eq T (THead (Flat Appl) x (THead (Bind Abst) t2 x0)) t3) \to (\forall 
(P: Prop).P)))).(\lambda (H10: (pr2 c (THead (Flat Appl) x (THead (Bind Abst) 
t2 x0)) t3)).(let H11 \def (pr2_gen_appl c x (THead (Bind Abst) t2 x0) t3 
H10) in (or3_ind (ex3_2 T T (\lambda (u2: T).(\lambda (t4: T).(eq T t3 (THead 
(Flat Appl) u2 t4)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c x u2))) 
(\lambda (_: T).(\lambda (t4: T).(pr2 c (THead (Bind Abst) t2 x0) t4)))) 
(ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: 
T).(eq T (THead (Bind Abst) t2 x0) (THead (Bind Abst) y1 z1)))))) (\lambda 
(_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t4: T).(eq T t3 (THead 
(Bind Abbr) u2 t4)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr2 c x u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda 
(_: T).(\lambda (t4: T).(\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind 
b) u) z1 t4)))))))) (ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B 
b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind Abst) t2 x0) (THead 
(Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T t3 (THead (Bind 
b) y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr2 c x u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 y2))))))) 
(\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda 
(_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b) y2) z1 z2)))))))) (sn3 c t3) 
(\lambda (H12: (ex3_2 T T (\lambda (u2: T).(\lambda (t4: T).(eq T t3 (THead 
(Flat Appl) u2 t4)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c x u2))) 
(\lambda (_: T).(\lambda (t4: T).(pr2 c (THead (Bind Abst) t2 x0) 
t4))))).(ex3_2_ind T T (\lambda (u2: T).(\lambda (t4: T).(eq T t3 (THead 
(Flat Appl) u2 t4)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c x u2))) 
(\lambda (_: T).(\lambda (t4: T).(pr2 c (THead (Bind Abst) t2 x0) t4))) (sn3 
c t3) (\lambda (x1: T).(\lambda (x2: T).(\lambda (H13: (eq T t3 (THead (Flat 
Appl) x1 x2))).(\lambda (H14: (pr2 c x x1)).(\lambda (H15: (pr2 c (THead 
(Bind Abst) t2 x0) x2)).(let H16 \def (eq_ind T t3 (\lambda (t0: T).((eq T 
(THead (Flat Appl) x (THead (Bind Abst) t2 x0)) t0) \to (\forall (P: 
Prop).P))) H9 (THead (Flat Appl) x1 x2) H13) in (eq_ind_r T (THead (Flat 
Appl) x1 x2) (\lambda (t0: T).(sn3 c t0)) (let H17 \def (pr2_gen_abst c t2 x0 
x2 H15) in (ex3_2_ind T T (\lambda (u2: T).(\lambda (t4: T).(eq T x2 (THead 
(Bind Abst) u2 t4)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c t2 u2))) 
(\lambda (_: T).(\lambda (t4: T).(\forall (b: B).(\forall (u: T).(pr2 (CHead 
c (Bind b) u) x0 t4))))) (sn3 c (THead (Flat Appl) x1 x2)) (\lambda (x3: 
T).(\lambda (x4: T).(\lambda (H18: (eq T x2 (THead (Bind Abst) x3 
x4))).(\lambda (H19: (pr2 c t2 x3)).(\lambda (H20: ((\forall (b: B).(\forall 
(u: T).(pr2 (CHead c (Bind b) u) x0 x4))))).(let H21 \def (eq_ind T x2 
(\lambda (t0: T).((eq T (THead (Flat Appl) x (THead (Bind Abst) t2 x0)) 
(THead (Flat Appl) x1 t0)) \to (\forall (P: Prop).P))) H16 (THead (Bind Abst) 
x3 x4) H18) in (eq_ind_r T (THead (Bind Abst) x3 x4) (\lambda (t0: T).(sn3 c 
(THead (Flat Appl) x1 t0))) (let H_x \def (term_dec t2 x3) in (let H22 \def 
H_x in (or_ind (eq T t2 x3) ((eq T t2 x3) \to (\forall (P: Prop).P)) (sn3 c 
(THead (Flat Appl) x1 (THead (Bind Abst) x3 x4))) (\lambda (H23: (eq T t2 
x3)).(let H24 \def (eq_ind_r T x3 (\lambda (t0: T).((eq T (THead (Flat Appl) 
x (THead (Bind Abst) t2 x0)) (THead (Flat Appl) x1 (THead (Bind Abst) t0 
x4))) \to (\forall (P: Prop).P))) H21 t2 H23) in (let H25 \def (eq_ind_r T x3 
(\lambda (t0: T).(pr2 c t2 t0)) H19 t2 H23) in (eq_ind T t2 (\lambda (t0: 
T).(sn3 c (THead (Flat Appl) x1 (THead (Bind Abst) t0 x4)))) (let H_x0 \def 
(term_dec x x1) in (let H26 \def H_x0 in (or_ind (eq T x x1) ((eq T x x1) \to 
(\forall (P: Prop).P)) (sn3 c (THead (Flat Appl) x1 (THead (Bind Abst) t2 
x4))) (\lambda (H27: (eq T x x1)).(let H28 \def (eq_ind_r T x1 (\lambda (t0: 
T).((eq T (THead (Flat Appl) x (THead (Bind Abst) t2 x0)) (THead (Flat Appl) 
t0 (THead (Bind Abst) t2 x4))) \to (\forall (P: Prop).P))) H24 x H27) in (let 
H29 \def (eq_ind_r T x1 (\lambda (t0: T).(pr2 c x t0)) H14 x H27) in (eq_ind 
T x (\lambda (t0: T).(sn3 c (THead (Flat Appl) t0 (THead (Bind Abst) t2 
x4)))) (let H_x1 \def (term_dec x0 x4) in (let H30 \def H_x1 in (or_ind (eq T 
x0 x4) ((eq T x0 x4) \to (\forall (P: Prop).P)) (sn3 c (THead (Flat Appl) x 
(THead (Bind Abst) t2 x4))) (\lambda (H31: (eq T x0 x4)).(let H32 \def 
(eq_ind_r T x4 (\lambda (t0: T).((eq T (THead (Flat Appl) x (THead (Bind 
Abst) t2 x0)) (THead (Flat Appl) x (THead (Bind Abst) t2 t0))) \to (\forall 
(P: Prop).P))) H28 x0 H31) in (let H33 \def (eq_ind_r T x4 (\lambda (t0: 
T).(\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) x0 t0)))) H20 x0 
H31) in (eq_ind T x0 (\lambda (t0: T).(sn3 c (THead (Flat Appl) x (THead 
(Bind Abst) t2 t0)))) (H32 (refl_equal T (THead (Flat Appl) x (THead (Bind 
Abst) t2 x0))) (sn3 c (THead (Flat Appl) x (THead (Bind Abst) t2 x0)))) x4 
H31)))) (\lambda (H31: (((eq T x0 x4) \to (\forall (P: Prop).P)))).(H5 (THead 
(Bind Abbr) x x4) (\lambda (H32: (eq T (THead (Bind Abbr) x x0) (THead (Bind 
Abbr) x x4))).(\lambda (P: Prop).(let H33 \def (f_equal T T (\lambda (e: 
T).(match e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow x0 | 
(TLRef _) \Rightarrow x0 | (THead _ _ t0) \Rightarrow t0])) (THead (Bind 
Abbr) x x0) (THead (Bind Abbr) x x4) H32) in (let H34 \def (eq_ind_r T x4 
(\lambda (t0: T).((eq T x0 t0) \to (\forall (P0: Prop).P0))) H31 x0 H33) in 
(let H35 \def (eq_ind_r T x4 (\lambda (t0: T).(\forall (b: B).(\forall (u: 
T).(pr2 (CHead c (Bind b) u) x0 t0)))) H20 x0 H33) in (H34 (refl_equal T x0) 
P)))))) (pr3_pr2 c (THead (Bind Abbr) x x0) (THead (Bind Abbr) x x4) 
(pr2_head_2 c x x0 x4 (Bind Abbr) (H20 Abbr x))) x x4 (refl_equal T (THead 
(Bind Abbr) x x4)) t2 (sn3_sing c t2 H7))) H30))) x1 H27)))) (\lambda (H27: 
(((eq T x x1) \to (\forall (P: Prop).P)))).(H5 (THead (Bind Abbr) x1 x4) 
(\lambda (H28: (eq T (THead (Bind Abbr) x x0) (THead (Bind Abbr) x1 
x4))).(\lambda (P: Prop).(let H29 \def (f_equal T T (\lambda (e: T).(match e 
in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow x | (TLRef _) 
\Rightarrow x | (THead _ t0 _) \Rightarrow t0])) (THead (Bind Abbr) x x0) 
(THead (Bind Abbr) x1 x4) H28) in ((let H30 \def (f_equal T T (\lambda (e: 
T).(match e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow x0 | 
(TLRef _) \Rightarrow x0 | (THead _ _ t0) \Rightarrow t0])) (THead (Bind 
Abbr) x x0) (THead (Bind Abbr) x1 x4) H28) in (\lambda (H31: (eq T x 
x1)).(let H32 \def (eq_ind_r T x4 (\lambda (t0: T).(\forall (b: B).(\forall 
(u: T).(pr2 (CHead c (Bind b) u) x0 t0)))) H20 x0 H30) in (let H33 \def 
(eq_ind_r T x1 (\lambda (t0: T).((eq T x t0) \to (\forall (P0: Prop).P0))) 
H27 x H31) in (let H34 \def (eq_ind_r T x1 (\lambda (t0: T).(pr2 c x t0)) H14 
x H31) in (H33 (refl_equal T x) P)))))) H29)))) (pr3_head_12 c x x1 (pr3_pr2 
c x x1 H14) (Bind Abbr) x0 x4 (pr3_pr2 (CHead c (Bind Abbr) x1) x0 x4 (H20 
Abbr x1))) x1 x4 (refl_equal T (THead (Bind Abbr) x1 x4)) t2 (sn3_sing c t2 
H7))) H26))) x3 H23)))) (\lambda (H23: (((eq T t2 x3) \to (\forall (P: 
Prop).P)))).(let H_x0 \def (term_dec x x1) in (let H24 \def H_x0 in (or_ind 
(eq T x x1) ((eq T x x1) \to (\forall (P: Prop).P)) (sn3 c (THead (Flat Appl) 
x1 (THead (Bind Abst) x3 x4))) (\lambda (H25: (eq T x x1)).(let H26 \def 
(eq_ind_r T x1 (\lambda (t0: T).(pr2 c x t0)) H14 x H25) in (eq_ind T x 
(\lambda (t0: T).(sn3 c (THead (Flat Appl) t0 (THead (Bind Abst) x3 x4)))) 
(let H_x1 \def (term_dec x0 x4) in (let H27 \def H_x1 in (or_ind (eq T x0 x4) 
((eq T x0 x4) \to (\forall (P: Prop).P)) (sn3 c (THead (Flat Appl) x (THead 
(Bind Abst) x3 x4))) (\lambda (H28: (eq T x0 x4)).(let H29 \def (eq_ind_r T 
x4 (\lambda (t0: T).(\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) 
x0 t0)))) H20 x0 H28) in (eq_ind T x0 (\lambda (t0: T).(sn3 c (THead (Flat 
Appl) x (THead (Bind Abst) x3 t0)))) (H8 x3 H23 (pr3_pr2 c t2 x3 H19)) x4 
H28))) (\lambda (H28: (((eq T x0 x4) \to (\forall (P: Prop).P)))).(H5 (THead 
(Bind Abbr) x x4) (\lambda (H29: (eq T (THead (Bind Abbr) x x0) (THead (Bind 
Abbr) x x4))).(\lambda (P: Prop).(let H30 \def (f_equal T T (\lambda (e: 
T).(match e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow x0 | 
(TLRef _) \Rightarrow x0 | (THead _ _ t0) \Rightarrow t0])) (THead (Bind 
Abbr) x x0) (THead (Bind Abbr) x x4) H29) in (let H31 \def (eq_ind_r T x4 
(\lambda (t0: T).((eq T x0 t0) \to (\forall (P0: Prop).P0))) H28 x0 H30) in 
(let H32 \def (eq_ind_r T x4 (\lambda (t0: T).(\forall (b: B).(\forall (u: 
T).(pr2 (CHead c (Bind b) u) x0 t0)))) H20 x0 H30) in (H31 (refl_equal T x0) 
P)))))) (pr3_pr2 c (THead (Bind Abbr) x x0) (THead (Bind Abbr) x x4) 
(pr2_head_2 c x x0 x4 (Bind Abbr) (H20 Abbr x))) x x4 (refl_equal T (THead 
(Bind Abbr) x x4)) x3 (H7 x3 H23 (pr3_pr2 c t2 x3 H19)))) H27))) x1 H25))) 
(\lambda (H25: (((eq T x x1) \to (\forall (P: Prop).P)))).(H5 (THead (Bind 
Abbr) x1 x4) (\lambda (H26: (eq T (THead (Bind Abbr) x x0) (THead (Bind Abbr) 
x1 x4))).(\lambda (P: Prop).(let H27 \def (f_equal T T (\lambda (e: T).(match 
e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow x | (TLRef _) 
\Rightarrow x | (THead _ t0 _) \Rightarrow t0])) (THead (Bind Abbr) x x0) 
(THead (Bind Abbr) x1 x4) H26) in ((let H28 \def (f_equal T T (\lambda (e: 
T).(match e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow x0 | 
(TLRef _) \Rightarrow x0 | (THead _ _ t0) \Rightarrow t0])) (THead (Bind 
Abbr) x x0) (THead (Bind Abbr) x1 x4) H26) in (\lambda (H29: (eq T x 
x1)).(let H30 \def (eq_ind_r T x4 (\lambda (t0: T).(\forall (b: B).(\forall 
(u: T).(pr2 (CHead c (Bind b) u) x0 t0)))) H20 x0 H28) in (let H31 \def 
(eq_ind_r T x1 (\lambda (t0: T).((eq T x t0) \to (\forall (P0: Prop).P0))) 
H25 x H29) in (let H32 \def (eq_ind_r T x1 (\lambda (t0: T).(pr2 c x t0)) H14 
x H29) in (H31 (refl_equal T x) P)))))) H27)))) (pr3_head_12 c x x1 (pr3_pr2 
c x x1 H14) (Bind Abbr) x0 x4 (pr3_pr2 (CHead c (Bind Abbr) x1) x0 x4 (H20 
Abbr x1))) x1 x4 (refl_equal T (THead (Bind Abbr) x1 x4)) x3 (H7 x3 H23 
(pr3_pr2 c t2 x3 H19)))) H24)))) H22))) x2 H18))))))) H17)) t3 H13))))))) 
H12)) (\lambda (H12: (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind Abst) t2 x0) (THead 
(Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (t4: T).(eq T t3 (THead (Bind Abbr) u2 t4)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c x u2))))) (\lambda 
(_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t4: T).(\forall (b: 
B).(\forall (u: T).(pr2 (CHead c (Bind b) u) z1 t4))))))))).(ex4_4_ind T T T 
T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T 
(THead (Bind Abst) t2 x0) (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t4: T).(eq T t3 (THead (Bind 
Abbr) u2 t4)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr2 c x u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t4: T).(\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) 
z1 t4))))))) (sn3 c t3) (\lambda (x1: T).(\lambda (x2: T).(\lambda (x3: 
T).(\lambda (x4: T).(\lambda (H13: (eq T (THead (Bind Abst) t2 x0) (THead 
(Bind Abst) x1 x2))).(\lambda (H14: (eq T t3 (THead (Bind Abbr) x3 
x4))).(\lambda (H15: (pr2 c x x3)).(\lambda (H16: ((\forall (b: B).(\forall 
(u: T).(pr2 (CHead c (Bind b) u) x2 x4))))).(let H17 \def (eq_ind T t3 
(\lambda (t0: T).((eq T (THead (Flat Appl) x (THead (Bind Abst) t2 x0)) t0) 
\to (\forall (P: Prop).P))) H9 (THead (Bind Abbr) x3 x4) H14) in (eq_ind_r T 
(THead (Bind Abbr) x3 x4) (\lambda (t0: T).(sn3 c t0)) (let H18 \def (f_equal 
T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) with [(TSort _) 
\Rightarrow t2 | (TLRef _) \Rightarrow t2 | (THead _ t0 _) \Rightarrow t0])) 
(THead (Bind Abst) t2 x0) (THead (Bind Abst) x1 x2) H13) in ((let H19 \def 
(f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) with 
[(TSort _) \Rightarrow x0 | (TLRef _) \Rightarrow x0 | (THead _ _ t0) 
\Rightarrow t0])) (THead (Bind Abst) t2 x0) (THead (Bind Abst) x1 x2) H13) in 
(\lambda (_: (eq T t2 x1)).(let H21 \def (eq_ind_r T x2 (\lambda (t0: 
T).(\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) t0 x4)))) H16 x0 
H19) in (let H_x \def (term_dec x x3) in (let H22 \def H_x in (or_ind (eq T x 
x3) ((eq T x x3) \to (\forall (P: Prop).P)) (sn3 c (THead (Bind Abbr) x3 x4)) 
(\lambda (H23: (eq T x x3)).(let H24 \def (eq_ind_r T x3 (\lambda (t0: 
T).(pr2 c x t0)) H15 x H23) in (eq_ind T x (\lambda (t0: T).(sn3 c (THead 
(Bind Abbr) t0 x4))) (let H_x0 \def (term_dec x0 x4) in (let H25 \def H_x0 in 
(or_ind (eq T x0 x4) ((eq T x0 x4) \to (\forall (P: Prop).P)) (sn3 c (THead 
(Bind Abbr) x x4)) (\lambda (H26: (eq T x0 x4)).(let H27 \def (eq_ind_r T x4 
(\lambda (t0: T).(\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) x0 
t0)))) H21 x0 H26) in (eq_ind T x0 (\lambda (t0: T).(sn3 c (THead (Bind Abbr) 
x t0))) (sn3_sing c (THead (Bind Abbr) x x0) H6) x4 H26))) (\lambda (H26: 
(((eq T x0 x4) \to (\forall (P: Prop).P)))).(H6 (THead (Bind Abbr) x x4) 
(\lambda (H27: (eq T (THead (Bind Abbr) x x0) (THead (Bind Abbr) x 
x4))).(\lambda (P: Prop).(let H28 \def (f_equal T T (\lambda (e: T).(match e 
in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow x0 | (TLRef _) 
\Rightarrow x0 | (THead _ _ t0) \Rightarrow t0])) (THead (Bind Abbr) x x0) 
(THead (Bind Abbr) x x4) H27) in (let H29 \def (eq_ind_r T x4 (\lambda (t0: 
T).((eq T x0 t0) \to (\forall (P0: Prop).P0))) H26 x0 H28) in (let H30 \def 
(eq_ind_r T x4 (\lambda (t0: T).(\forall (b: B).(\forall (u: T).(pr2 (CHead c 
(Bind b) u) x0 t0)))) H21 x0 H28) in (H29 (refl_equal T x0) P)))))) (pr3_pr2 
c (THead (Bind Abbr) x x0) (THead (Bind Abbr) x x4) (pr2_head_2 c x x0 x4 
(Bind Abbr) (H21 Abbr x))))) H25))) x3 H23))) (\lambda (H23: (((eq T x x3) 
\to (\forall (P: Prop).P)))).(H6 (THead (Bind Abbr) x3 x4) (\lambda (H24: (eq 
T (THead (Bind Abbr) x x0) (THead (Bind Abbr) x3 x4))).(\lambda (P: 
Prop).(let H25 \def (f_equal T T (\lambda (e: T).(match e in T return 
(\lambda (_: T).T) with [(TSort _) \Rightarrow x | (TLRef _) \Rightarrow x | 
(THead _ t0 _) \Rightarrow t0])) (THead (Bind Abbr) x x0) (THead (Bind Abbr) 
x3 x4) H24) in ((let H26 \def (f_equal T T (\lambda (e: T).(match e in T 
return (\lambda (_: T).T) with [(TSort _) \Rightarrow x0 | (TLRef _) 
\Rightarrow x0 | (THead _ _ t0) \Rightarrow t0])) (THead (Bind Abbr) x x0) 
(THead (Bind Abbr) x3 x4) H24) in (\lambda (H27: (eq T x x3)).(let H28 \def 
(eq_ind_r T x4 (\lambda (t0: T).(\forall (b: B).(\forall (u: T).(pr2 (CHead c 
(Bind b) u) x0 t0)))) H21 x0 H26) in (let H29 \def (eq_ind_r T x3 (\lambda 
(t0: T).((eq T x t0) \to (\forall (P0: Prop).P0))) H23 x H27) in (let H30 
\def (eq_ind_r T x3 (\lambda (t0: T).(pr2 c x t0)) H15 x H27) in (H29 
(refl_equal T x) P)))))) H25)))) (pr3_head_12 c x x3 (pr3_pr2 c x x3 H15) 
(Bind Abbr) x0 x4 (pr3_pr2 (CHead c (Bind Abbr) x3) x0 x4 (H21 Abbr x3))))) 
H22)))))) H18)) t3 H14)))))))))) H12)) (\lambda (H12: (ex6_6 B T T T T T 
(\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T 
(THead (Bind Abst) t2 x0) (THead (Bind b) y1 z1)))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda 
(y2: T).(eq T t3 (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) 
z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c x u2))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 c y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b) 
y2) z1 z2))))))))).(ex6_6_ind B T T T T T (\lambda (b: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B 
b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind Abst) t2 x0) (THead 
(Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T t3 (THead (Bind 
b) y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr2 c x u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 y2))))))) 
(\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda 
(_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b) y2) z1 z2))))))) (sn3 c t3) 
(\lambda (x1: B).(\lambda (x2: T).(\lambda (x3: T).(\lambda (x4: T).(\lambda 
(x5: T).(\lambda (x6: T).(\lambda (H13: (not (eq B x1 Abst))).(\lambda (H14: 
(eq T (THead (Bind Abst) t2 x0) (THead (Bind x1) x2 x3))).(\lambda (H15: (eq 
T t3 (THead (Bind x1) x6 (THead (Flat Appl) (lift (S O) O x5) x4)))).(\lambda 
(_: (pr2 c x x5)).(\lambda (H17: (pr2 c x2 x6)).(\lambda (H18: (pr2 (CHead c 
(Bind x1) x6) x3 x4)).(let H19 \def (eq_ind T t3 (\lambda (t0: T).((eq T 
(THead (Flat Appl) x (THead (Bind Abst) t2 x0)) t0) \to (\forall (P: 
Prop).P))) H9 (THead (Bind x1) x6 (THead (Flat Appl) (lift (S O) O x5) x4)) 
H15) in (eq_ind_r T (THead (Bind x1) x6 (THead (Flat Appl) (lift (S O) O x5) 
x4)) (\lambda (t0: T).(sn3 c t0)) (let H20 \def (f_equal T B (\lambda (e: 
T).(match e in T return (\lambda (_: T).B) with [(TSort _) \Rightarrow Abst | 
(TLRef _) \Rightarrow Abst | (THead k _ _) \Rightarrow (match k in K return 
(\lambda (_: K).B) with [(Bind b) \Rightarrow b | (Flat _) \Rightarrow 
Abst])])) (THead (Bind Abst) t2 x0) (THead (Bind x1) x2 x3) H14) in ((let H21 
\def (f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) 
with [(TSort _) \Rightarrow t2 | (TLRef _) \Rightarrow t2 | (THead _ t0 _) 
\Rightarrow t0])) (THead (Bind Abst) t2 x0) (THead (Bind x1) x2 x3) H14) in 
((let H22 \def (f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: 
T).T) with [(TSort _) \Rightarrow x0 | (TLRef _) \Rightarrow x0 | (THead _ _ 
t0) \Rightarrow t0])) (THead (Bind Abst) t2 x0) (THead (Bind x1) x2 x3) H14) 
in (\lambda (H23: (eq T t2 x2)).(\lambda (H24: (eq B Abst x1)).(let H25 \def 
(eq_ind_r T x3 (\lambda (t0: T).(pr2 (CHead c (Bind x1) x6) t0 x4)) H18 x0 
H22) in (let H26 \def (eq_ind_r T x2 (\lambda (t0: T).(pr2 c t0 x6)) H17 t2 
H23) in (let H27 \def (eq_ind_r B x1 (\lambda (b: B).(pr2 (CHead c (Bind b) 
x6) x0 x4)) H25 Abst H24) in (let H28 \def (eq_ind_r B x1 (\lambda (b: 
B).(not (eq B b Abst))) H13 Abst H24) in (eq_ind B Abst (\lambda (b: B).(sn3 
c (THead (Bind b) x6 (THead (Flat Appl) (lift (S O) O x5) x4)))) (let H29 
\def (match (H28 (refl_equal B Abst)) in False return (\lambda (_: 
False).(sn3 c (THead (Bind Abst) x6 (THead (Flat Appl) (lift (S O) O x5) 
x4)))) with []) in H29) x1 H24)))))))) H21)) H20)) t3 H15)))))))))))))) H12)) 
H11))))))))) w H4))))))))))) y H0))))) H)))).

theorem nf3_appl_abbr:
 \forall (c: C).(\forall (d: C).(\forall (w: T).(\forall (i: nat).((getl i c 
(CHead d (Bind Abbr) w)) \to (\forall (v: T).((sn3 c (THead (Flat Appl) v 
(lift (S i) O w))) \to (sn3 c (THead (Flat Appl) v (TLRef i)))))))))
\def
 \lambda (c: C).(\lambda (d: C).(\lambda (w: T).(\lambda (i: nat).(\lambda 
(H: (getl i c (CHead d (Bind Abbr) w))).(\lambda (v: T).(\lambda (H0: (sn3 c 
(THead (Flat Appl) v (lift (S i) O w)))).(insert_eq T (THead (Flat Appl) v 
(lift (S i) O w)) (\lambda (t: T).(sn3 c t)) (sn3 c (THead (Flat Appl) v 
(TLRef i))) (\lambda (y: T).(\lambda (H1: (sn3 c y)).(unintro T v (\lambda 
(t: T).((eq T y (THead (Flat Appl) t (lift (S i) O w))) \to (sn3 c (THead 
(Flat Appl) t (TLRef i))))) (sn3_ind c (\lambda (t: T).(\forall (x: T).((eq T 
t (THead (Flat Appl) x (lift (S i) O w))) \to (sn3 c (THead (Flat Appl) x 
(TLRef i)))))) (\lambda (t1: T).(\lambda (H2: ((\forall (t2: T).((((eq T t1 
t2) \to (\forall (P: Prop).P))) \to ((pr3 c t1 t2) \to (sn3 c 
t2)))))).(\lambda (H3: ((\forall (t2: T).((((eq T t1 t2) \to (\forall (P: 
Prop).P))) \to ((pr3 c t1 t2) \to (\forall (x: T).((eq T t2 (THead (Flat 
Appl) x (lift (S i) O w))) \to (sn3 c (THead (Flat Appl) x (TLRef 
i)))))))))).(\lambda (x: T).(\lambda (H4: (eq T t1 (THead (Flat Appl) x (lift 
(S i) O w)))).(let H5 \def (eq_ind T t1 (\lambda (t: T).(\forall (t2: 
T).((((eq T t t2) \to (\forall (P: Prop).P))) \to ((pr3 c t t2) \to (\forall 
(x0: T).((eq T t2 (THead (Flat Appl) x0 (lift (S i) O w))) \to (sn3 c (THead 
(Flat Appl) x0 (TLRef i))))))))) H3 (THead (Flat Appl) x (lift (S i) O w)) 
H4) in (let H6 \def (eq_ind T t1 (\lambda (t: T).(\forall (t2: T).((((eq T t 
t2) \to (\forall (P: Prop).P))) \to ((pr3 c t t2) \to (sn3 c t2))))) H2 
(THead (Flat Appl) x (lift (S i) O w)) H4) in (sn3_pr2_intro c (THead (Flat 
Appl) x (TLRef i)) (\lambda (t2: T).(\lambda (H7: (((eq T (THead (Flat Appl) 
x (TLRef i)) t2) \to (\forall (P: Prop).P)))).(\lambda (H8: (pr2 c (THead 
(Flat Appl) x (TLRef i)) t2)).(let H9 \def (pr2_gen_appl c x (TLRef i) t2 H8) 
in (or3_ind (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead 
(Flat Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c x u2))) 
(\lambda (_: T).(\lambda (t3: T).(pr2 c (TLRef i) t3)))) (ex4_4 T T T T 
(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T 
(TLRef i) (THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind Abbr) u2 t3)))))) 
(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c x 
u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: 
T).(\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) z1 t3)))))))) 
(ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(eq T (TLRef i) (THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda 
(_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq 
T t2 (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) 
(\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr2 c x u2))))))) (\lambda (_: B).(\lambda (y1: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 
y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b) y2) z1 z2)))))))) 
(sn3 c t2) (\lambda (H10: (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T 
t2 (THead (Flat Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c x 
u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c (TLRef i) t3))))).(ex3_2_ind T 
T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Flat Appl) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c x u2))) (\lambda (_: T).(\lambda (t3: 
T).(pr2 c (TLRef i) t3))) (sn3 c t2) (\lambda (x0: T).(\lambda (x1: 
T).(\lambda (H11: (eq T t2 (THead (Flat Appl) x0 x1))).(\lambda (H12: (pr2 c 
x x0)).(\lambda (H13: (pr2 c (TLRef i) x1)).(let H14 \def (eq_ind T t2 
(\lambda (t: T).((eq T (THead (Flat Appl) x (TLRef i)) t) \to (\forall (P: 
Prop).P))) H7 (THead (Flat Appl) x0 x1) H11) in (eq_ind_r T (THead (Flat 
Appl) x0 x1) (\lambda (t: T).(sn3 c t)) (let H15 \def (pr2_gen_lref c x1 i 
H13) in (or_ind (eq T x1 (TLRef i)) (ex2_2 C T (\lambda (d0: C).(\lambda (u: 
T).(getl i c (CHead d0 (Bind Abbr) u)))) (\lambda (_: C).(\lambda (u: T).(eq 
T x1 (lift (S i) O u))))) (sn3 c (THead (Flat Appl) x0 x1)) (\lambda (H16: 
(eq T x1 (TLRef i))).(let H17 \def (eq_ind T x1 (\lambda (t: T).((eq T (THead 
(Flat Appl) x (TLRef i)) (THead (Flat Appl) x0 t)) \to (\forall (P: 
Prop).P))) H14 (TLRef i) H16) in (eq_ind_r T (TLRef i) (\lambda (t: T).(sn3 c 
(THead (Flat Appl) x0 t))) (let H_x \def (term_dec x x0) in (let H18 \def H_x 
in (or_ind (eq T x x0) ((eq T x x0) \to (\forall (P: Prop).P)) (sn3 c (THead 
(Flat Appl) x0 (TLRef i))) (\lambda (H19: (eq T x x0)).(let H20 \def 
(eq_ind_r T x0 (\lambda (t: T).((eq T (THead (Flat Appl) x (TLRef i)) (THead 
(Flat Appl) t (TLRef i))) \to (\forall (P: Prop).P))) H17 x H19) in (let H21 
\def (eq_ind_r T x0 (\lambda (t: T).(pr2 c x t)) H12 x H19) in (eq_ind T x 
(\lambda (t: T).(sn3 c (THead (Flat Appl) t (TLRef i)))) (H20 (refl_equal T 
(THead (Flat Appl) x (TLRef i))) (sn3 c (THead (Flat Appl) x (TLRef i)))) x0 
H19)))) (\lambda (H19: (((eq T x x0) \to (\forall (P: Prop).P)))).(H5 (THead 
(Flat Appl) x0 (lift (S i) O w)) (\lambda (H20: (eq T (THead (Flat Appl) x 
(lift (S i) O w)) (THead (Flat Appl) x0 (lift (S i) O w)))).(\lambda (P: 
Prop).(let H21 \def (f_equal T T (\lambda (e: T).(match e in T return 
(\lambda (_: T).T) with [(TSort _) \Rightarrow x | (TLRef _) \Rightarrow x | 
(THead _ t _) \Rightarrow t])) (THead (Flat Appl) x (lift (S i) O w)) (THead 
(Flat Appl) x0 (lift (S i) O w)) H20) in (let H22 \def (eq_ind_r T x0 
(\lambda (t: T).((eq T x t) \to (\forall (P0: Prop).P0))) H19 x H21) in (let 
H23 \def (eq_ind_r T x0 (\lambda (t: T).(pr2 c x t)) H12 x H21) in (H22 
(refl_equal T x) P)))))) (pr3_pr2 c (THead (Flat Appl) x (lift (S i) O w)) 
(THead (Flat Appl) x0 (lift (S i) O w)) (pr2_head_1 c x x0 H12 (Flat Appl) 
(lift (S i) O w))) x0 (refl_equal T (THead (Flat Appl) x0 (lift (S i) O 
w))))) H18))) x1 H16))) (\lambda (H16: (ex2_2 C T (\lambda (d0: C).(\lambda 
(u: T).(getl i c (CHead d0 (Bind Abbr) u)))) (\lambda (_: C).(\lambda (u: 
T).(eq T x1 (lift (S i) O u)))))).(ex2_2_ind C T (\lambda (d0: C).(\lambda 
(u: T).(getl i c (CHead d0 (Bind Abbr) u)))) (\lambda (_: C).(\lambda (u: 
T).(eq T x1 (lift (S i) O u)))) (sn3 c (THead (Flat Appl) x0 x1)) (\lambda 
(x2: C).(\lambda (x3: T).(\lambda (H17: (getl i c (CHead x2 (Bind Abbr) 
x3))).(\lambda (H18: (eq T x1 (lift (S i) O x3))).(let H19 \def (eq_ind T x1 
(\lambda (t: T).((eq T (THead (Flat Appl) x (TLRef i)) (THead (Flat Appl) x0 
t)) \to (\forall (P: Prop).P))) H14 (lift (S i) O x3) H18) in (eq_ind_r T 
(lift (S i) O x3) (\lambda (t: T).(sn3 c (THead (Flat Appl) x0 t))) (let H20 
\def (eq_ind C (CHead d (Bind Abbr) w) (\lambda (c0: C).(getl i c c0)) H 
(CHead x2 (Bind Abbr) x3) (getl_mono c (CHead d (Bind Abbr) w) i H (CHead x2 
(Bind Abbr) x3) H17)) in (let H21 \def (f_equal C C (\lambda (e: C).(match e 
in C return (\lambda (_: C).C) with [(CSort _) \Rightarrow d | (CHead c0 _ _) 
\Rightarrow c0])) (CHead d (Bind Abbr) w) (CHead x2 (Bind Abbr) x3) 
(getl_mono c (CHead d (Bind Abbr) w) i H (CHead x2 (Bind Abbr) x3) H17)) in 
((let H22 \def (f_equal C T (\lambda (e: C).(match e in C return (\lambda (_: 
C).T) with [(CSort _) \Rightarrow w | (CHead _ _ t) \Rightarrow t])) (CHead d 
(Bind Abbr) w) (CHead x2 (Bind Abbr) x3) (getl_mono c (CHead d (Bind Abbr) w) 
i H (CHead x2 (Bind Abbr) x3) H17)) in (\lambda (H23: (eq C d x2)).(let H24 
\def (eq_ind_r T x3 (\lambda (t: T).(getl i c (CHead x2 (Bind Abbr) t))) H20 
w H22) in (eq_ind T w (\lambda (t: T).(sn3 c (THead (Flat Appl) x0 (lift (S 
i) O t)))) (let H25 \def (eq_ind_r C x2 (\lambda (c0: C).(getl i c (CHead c0 
(Bind Abbr) w))) H24 d H23) in (let H_x \def (term_dec x x0) in (let H26 \def 
H_x in (or_ind (eq T x x0) ((eq T x x0) \to (\forall (P: Prop).P)) (sn3 c 
(THead (Flat Appl) x0 (lift (S i) O w))) (\lambda (H27: (eq T x x0)).(let H28 
\def (eq_ind_r T x0 (\lambda (t: T).(pr2 c x t)) H12 x H27) in (eq_ind T x 
(\lambda (t: T).(sn3 c (THead (Flat Appl) t (lift (S i) O w)))) (sn3_sing c 
(THead (Flat Appl) x (lift (S i) O w)) H6) x0 H27))) (\lambda (H27: (((eq T x 
x0) \to (\forall (P: Prop).P)))).(H6 (THead (Flat Appl) x0 (lift (S i) O w)) 
(\lambda (H28: (eq T (THead (Flat Appl) x (lift (S i) O w)) (THead (Flat 
Appl) x0 (lift (S i) O w)))).(\lambda (P: Prop).(let H29 \def (f_equal T T 
(\lambda (e: T).(match e in T return (\lambda (_: T).T) with [(TSort _) 
\Rightarrow x | (TLRef _) \Rightarrow x | (THead _ t _) \Rightarrow t])) 
(THead (Flat Appl) x (lift (S i) O w)) (THead (Flat Appl) x0 (lift (S i) O 
w)) H28) in (let H30 \def (eq_ind_r T x0 (\lambda (t: T).((eq T x t) \to 
(\forall (P0: Prop).P0))) H27 x H29) in (let H31 \def (eq_ind_r T x0 (\lambda 
(t: T).(pr2 c x t)) H12 x H29) in (H30 (refl_equal T x) P)))))) (pr3_pr2 c 
(THead (Flat Appl) x (lift (S i) O w)) (THead (Flat Appl) x0 (lift (S i) O 
w)) (pr2_head_1 c x x0 H12 (Flat Appl) (lift (S i) O w))))) H26)))) x3 
H22)))) H21))) x1 H18)))))) H16)) H15)) t2 H11))))))) H10)) (\lambda (H10: 
(ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: 
T).(eq T (TLRef i) (THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda 
(_: T).(\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind Abbr) u2 
t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: 
T).(pr2 c x u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda 
(t3: T).(\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) z1 
t3))))))))).(ex4_4_ind T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(eq T (TLRef i) (THead (Bind Abst) y1 z1)))))) (\lambda 
(_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead 
(Bind Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr2 c x u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda 
(_: T).(\lambda (t3: T).(\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind 
b) u) z1 t3))))))) (sn3 c t2) (\lambda (x0: T).(\lambda (x1: T).(\lambda (x2: 
T).(\lambda (x3: T).(\lambda (H11: (eq T (TLRef i) (THead (Bind Abst) x0 
x1))).(\lambda (H12: (eq T t2 (THead (Bind Abbr) x2 x3))).(\lambda (_: (pr2 c 
x x2)).(\lambda (_: ((\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind b) 
u) x1 x3))))).(let H15 \def (eq_ind T t2 (\lambda (t: T).((eq T (THead (Flat 
Appl) x (TLRef i)) t) \to (\forall (P: Prop).P))) H7 (THead (Bind Abbr) x2 
x3) H12) in (eq_ind_r T (THead (Bind Abbr) x2 x3) (\lambda (t: T).(sn3 c t)) 
(let H16 \def (eq_ind T (TLRef i) (\lambda (ee: T).(match ee in T return 
(\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow True | (THead _ _ _) \Rightarrow False])) I (THead (Bind Abst) x0 
x1) H11) in (False_ind (sn3 c (THead (Bind Abbr) x2 x3)) H16)) t2 
H12)))))))))) H10)) (\lambda (H10: (ex6_6 B T T T T T (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T (TLRef i) 
(THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T t2 (THead (Bind 
b) y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr2 c x u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 y2))))))) 
(\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda 
(_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b) y2) z1 z2))))))))).(ex6_6_ind 
B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(eq T (TLRef i) (THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda 
(_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq 
T t2 (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) 
(\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr2 c x u2))))))) (\lambda (_: B).(\lambda (y1: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 
y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b) y2) z1 z2))))))) 
(sn3 c t2) (\lambda (x0: B).(\lambda (x1: T).(\lambda (x2: T).(\lambda (x3: 
T).(\lambda (x4: T).(\lambda (x5: T).(\lambda (_: (not (eq B x0 
Abst))).(\lambda (H12: (eq T (TLRef i) (THead (Bind x0) x1 x2))).(\lambda 
(H13: (eq T t2 (THead (Bind x0) x5 (THead (Flat Appl) (lift (S O) O x4) 
x3)))).(\lambda (_: (pr2 c x x4)).(\lambda (_: (pr2 c x1 x5)).(\lambda (_: 
(pr2 (CHead c (Bind x0) x5) x2 x3)).(let H17 \def (eq_ind T t2 (\lambda (t: 
T).((eq T (THead (Flat Appl) x (TLRef i)) t) \to (\forall (P: Prop).P))) H7 
(THead (Bind x0) x5 (THead (Flat Appl) (lift (S O) O x4) x3)) H13) in 
(eq_ind_r T (THead (Bind x0) x5 (THead (Flat Appl) (lift (S O) O x4) x3)) 
(\lambda (t: T).(sn3 c t)) (let H18 \def (eq_ind T (TLRef i) (\lambda (ee: 
T).(match ee in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow 
False | (TLRef _) \Rightarrow True | (THead _ _ _) \Rightarrow False])) I 
(THead (Bind x0) x1 x2) H12) in (False_ind (sn3 c (THead (Bind x0) x5 (THead 
(Flat Appl) (lift (S O) O x4) x3))) H18)) t2 H13)))))))))))))) H10)) 
H9))))))))))))) y H1)))) H0))))))).

theorem sn3_appl_bind:
 \forall (b: B).((not (eq B b Abst)) \to (\forall (c: C).(\forall (u: 
T).((sn3 c u) \to (\forall (t: T).(\forall (v: T).((sn3 (CHead c (Bind b) u) 
(THead (Flat Appl) (lift (S O) O v) t)) \to (sn3 c (THead (Flat Appl) v 
(THead (Bind b) u t))))))))))
\def
 \lambda (b: B).(\lambda (H: (not (eq B b Abst))).(\lambda (c: C).(\lambda 
(u: T).(\lambda (H0: (sn3 c u)).(sn3_ind c (\lambda (t: T).(\forall (t0: 
T).(\forall (v: T).((sn3 (CHead c (Bind b) t) (THead (Flat Appl) (lift (S O) 
O v) t0)) \to (sn3 c (THead (Flat Appl) v (THead (Bind b) t t0))))))) 
(\lambda (t1: T).(\lambda (H1: ((\forall (t2: T).((((eq T t1 t2) \to (\forall 
(P: Prop).P))) \to ((pr3 c t1 t2) \to (sn3 c t2)))))).(\lambda (H2: ((\forall 
(t2: T).((((eq T t1 t2) \to (\forall (P: Prop).P))) \to ((pr3 c t1 t2) \to 
(\forall (t: T).(\forall (v: T).((sn3 (CHead c (Bind b) t2) (THead (Flat 
Appl) (lift (S O) O v) t)) \to (sn3 c (THead (Flat Appl) v (THead (Bind b) t2 
t))))))))))).(\lambda (t: T).(\lambda (v: T).(\lambda (H3: (sn3 (CHead c 
(Bind b) t1) (THead (Flat Appl) (lift (S O) O v) t))).(insert_eq T (THead 
(Flat Appl) (lift (S O) O v) t) (\lambda (t0: T).(sn3 (CHead c (Bind b) t1) 
t0)) (sn3 c (THead (Flat Appl) v (THead (Bind b) t1 t))) (\lambda (y: 
T).(\lambda (H4: (sn3 (CHead c (Bind b) t1) y)).(unintro T t (\lambda (t0: 
T).((eq T y (THead (Flat Appl) (lift (S O) O v) t0)) \to (sn3 c (THead (Flat 
Appl) v (THead (Bind b) t1 t0))))) (unintro T v (\lambda (t0: T).(\forall (x: 
T).((eq T y (THead (Flat Appl) (lift (S O) O t0) x)) \to (sn3 c (THead (Flat 
Appl) t0 (THead (Bind b) t1 x)))))) (sn3_ind (CHead c (Bind b) t1) (\lambda 
(t0: T).(\forall (x: T).(\forall (x0: T).((eq T t0 (THead (Flat Appl) (lift 
(S O) O x) x0)) \to (sn3 c (THead (Flat Appl) x (THead (Bind b) t1 x0))))))) 
(\lambda (t2: T).(\lambda (H5: ((\forall (t3: T).((((eq T t2 t3) \to (\forall 
(P: Prop).P))) \to ((pr3 (CHead c (Bind b) t1) t2 t3) \to (sn3 (CHead c (Bind 
b) t1) t3)))))).(\lambda (H6: ((\forall (t3: T).((((eq T t2 t3) \to (\forall 
(P: Prop).P))) \to ((pr3 (CHead c (Bind b) t1) t2 t3) \to (\forall (x: 
T).(\forall (x0: T).((eq T t3 (THead (Flat Appl) (lift (S O) O x) x0)) \to 
(sn3 c (THead (Flat Appl) x (THead (Bind b) t1 x0))))))))))).(\lambda (x: 
T).(\lambda (x0: T).(\lambda (H7: (eq T t2 (THead (Flat Appl) (lift (S O) O 
x) x0))).(let H8 \def (eq_ind T t2 (\lambda (t0: T).(\forall (t3: T).((((eq T 
t0 t3) \to (\forall (P: Prop).P))) \to ((pr3 (CHead c (Bind b) t1) t0 t3) \to 
(\forall (x1: T).(\forall (x2: T).((eq T t3 (THead (Flat Appl) (lift (S O) O 
x1) x2)) \to (sn3 c (THead (Flat Appl) x1 (THead (Bind b) t1 x2)))))))))) H6 
(THead (Flat Appl) (lift (S O) O x) x0) H7) in (let H9 \def (eq_ind T t2 
(\lambda (t0: T).(\forall (t3: T).((((eq T t0 t3) \to (\forall (P: Prop).P))) 
\to ((pr3 (CHead c (Bind b) t1) t0 t3) \to (sn3 (CHead c (Bind b) t1) t3))))) 
H5 (THead (Flat Appl) (lift (S O) O x) x0) H7) in (sn3_pr2_intro c (THead 
(Flat Appl) x (THead (Bind b) t1 x0)) (\lambda (t3: T).(\lambda (H10: (((eq T 
(THead (Flat Appl) x (THead (Bind b) t1 x0)) t3) \to (\forall (P: 
Prop).P)))).(\lambda (H11: (pr2 c (THead (Flat Appl) x (THead (Bind b) t1 
x0)) t3)).(let H12 \def (pr2_gen_appl c x (THead (Bind b) t1 x0) t3 H11) in 
(or3_ind (ex3_2 T T (\lambda (u2: T).(\lambda (t4: T).(eq T t3 (THead (Flat 
Appl) u2 t4)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c x u2))) (\lambda (_: 
T).(\lambda (t4: T).(pr2 c (THead (Bind b) t1 x0) t4)))) (ex4_4 T T T T 
(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T 
(THead (Bind b) t1 x0) (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t4: T).(eq T t3 (THead (Bind 
Abbr) u2 t4)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr2 c x u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t4: T).(\forall (b0: B).(\forall (u0: T).(pr2 (CHead c (Bind b0) 
u0) z1 t4)))))))) (ex6_6 B T T T T T (\lambda (b0: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B 
b0 Abst)))))))) (\lambda (b0: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind b) t1 x0) (THead 
(Bind b0) y1 z1)))))))) (\lambda (b0: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T t3 (THead (Bind 
b0) y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr2 c x u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 y2))))))) 
(\lambda (b0: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda 
(_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b0) y2) z1 z2)))))))) (sn3 c t3) 
(\lambda (H13: (ex3_2 T T (\lambda (u2: T).(\lambda (t4: T).(eq T t3 (THead 
(Flat Appl) u2 t4)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c x u2))) 
(\lambda (_: T).(\lambda (t4: T).(pr2 c (THead (Bind b) t1 x0) 
t4))))).(ex3_2_ind T T (\lambda (u2: T).(\lambda (t4: T).(eq T t3 (THead 
(Flat Appl) u2 t4)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c x u2))) 
(\lambda (_: T).(\lambda (t4: T).(pr2 c (THead (Bind b) t1 x0) t4))) (sn3 c 
t3) (\lambda (x1: T).(\lambda (x2: T).(\lambda (H14: (eq T t3 (THead (Flat 
Appl) x1 x2))).(\lambda (H15: (pr2 c x x1)).(\lambda (H16: (pr2 c (THead 
(Bind b) t1 x0) x2)).(let H17 \def (eq_ind T t3 (\lambda (t0: T).((eq T 
(THead (Flat Appl) x (THead (Bind b) t1 x0)) t0) \to (\forall (P: Prop).P))) 
H10 (THead (Flat Appl) x1 x2) H14) in (eq_ind_r T (THead (Flat Appl) x1 x2) 
(\lambda (t0: T).(sn3 c t0)) (let H_x \def (pr3_gen_bind b H c t1 x0 x2) in 
(let H18 \def (H_x (pr3_pr2 c (THead (Bind b) t1 x0) x2 H16)) in (or_ind 
(ex3_2 T T (\lambda (u2: T).(\lambda (t4: T).(eq T x2 (THead (Bind b) u2 
t4)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c t1 u2))) (\lambda (_: 
T).(\lambda (t4: T).(pr3 (CHead c (Bind b) t1) x0 t4)))) (pr3 (CHead c (Bind 
b) t1) x0 (lift (S O) O x2)) (sn3 c (THead (Flat Appl) x1 x2)) (\lambda (H19: 
(ex3_2 T T (\lambda (u2: T).(\lambda (t4: T).(eq T x2 (THead (Bind b) u2 
t4)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c t1 u2))) (\lambda (_: 
T).(\lambda (t4: T).(pr3 (CHead c (Bind b) t1) x0 t4))))).(ex3_2_ind T T 
(\lambda (u2: T).(\lambda (t4: T).(eq T x2 (THead (Bind b) u2 t4)))) (\lambda 
(u2: T).(\lambda (_: T).(pr3 c t1 u2))) (\lambda (_: T).(\lambda (t4: T).(pr3 
(CHead c (Bind b) t1) x0 t4))) (sn3 c (THead (Flat Appl) x1 x2)) (\lambda 
(x3: T).(\lambda (x4: T).(\lambda (H20: (eq T x2 (THead (Bind b) x3 
x4))).(\lambda (H21: (pr3 c t1 x3)).(\lambda (H22: (pr3 (CHead c (Bind b) t1) 
x0 x4)).(let H23 \def (eq_ind T x2 (\lambda (t0: T).((eq T (THead (Flat Appl) 
x (THead (Bind b) t1 x0)) (THead (Flat Appl) x1 t0)) \to (\forall (P: 
Prop).P))) H17 (THead (Bind b) x3 x4) H20) in (eq_ind_r T (THead (Bind b) x3 
x4) (\lambda (t0: T).(sn3 c (THead (Flat Appl) x1 t0))) (let H_x0 \def 
(term_dec t1 x3) in (let H24 \def H_x0 in (or_ind (eq T t1 x3) ((eq T t1 x3) 
\to (\forall (P: Prop).P)) (sn3 c (THead (Flat Appl) x1 (THead (Bind b) x3 
x4))) (\lambda (H25: (eq T t1 x3)).(let H26 \def (eq_ind_r T x3 (\lambda (t0: 
T).((eq T (THead (Flat Appl) x (THead (Bind b) t1 x0)) (THead (Flat Appl) x1 
(THead (Bind b) t0 x4))) \to (\forall (P: Prop).P))) H23 t1 H25) in (let H27 
\def (eq_ind_r T x3 (\lambda (t0: T).(pr3 c t1 t0)) H21 t1 H25) in (eq_ind T 
t1 (\lambda (t0: T).(sn3 c (THead (Flat Appl) x1 (THead (Bind b) t0 x4)))) 
(let H_x1 \def (term_dec x0 x4) in (let H28 \def H_x1 in (or_ind (eq T x0 x4) 
((eq T x0 x4) \to (\forall (P: Prop).P)) (sn3 c (THead (Flat Appl) x1 (THead 
(Bind b) t1 x4))) (\lambda (H29: (eq T x0 x4)).(let H30 \def (eq_ind_r T x4 
(\lambda (t0: T).((eq T (THead (Flat Appl) x (THead (Bind b) t1 x0)) (THead 
(Flat Appl) x1 (THead (Bind b) t1 t0))) \to (\forall (P: Prop).P))) H26 x0 
H29) in (let H31 \def (eq_ind_r T x4 (\lambda (t0: T).(pr3 (CHead c (Bind b) 
t1) x0 t0)) H22 x0 H29) in (eq_ind T x0 (\lambda (t0: T).(sn3 c (THead (Flat 
Appl) x1 (THead (Bind b) t1 t0)))) (let H_x2 \def (term_dec x x1) in (let H32 
\def H_x2 in (or_ind (eq T x x1) ((eq T x x1) \to (\forall (P: Prop).P)) (sn3 
c (THead (Flat Appl) x1 (THead (Bind b) t1 x0))) (\lambda (H33: (eq T x 
x1)).(let H34 \def (eq_ind_r T x1 (\lambda (t0: T).((eq T (THead (Flat Appl) 
x (THead (Bind b) t1 x0)) (THead (Flat Appl) t0 (THead (Bind b) t1 x0))) \to 
(\forall (P: Prop).P))) H30 x H33) in (let H35 \def (eq_ind_r T x1 (\lambda 
(t0: T).(pr2 c x t0)) H15 x H33) in (eq_ind T x (\lambda (t0: T).(sn3 c 
(THead (Flat Appl) t0 (THead (Bind b) t1 x0)))) (H34 (refl_equal T (THead 
(Flat Appl) x (THead (Bind b) t1 x0))) (sn3 c (THead (Flat Appl) x (THead 
(Bind b) t1 x0)))) x1 H33)))) (\lambda (H33: (((eq T x x1) \to (\forall (P: 
Prop).P)))).(H8 (THead (Flat Appl) (lift (S O) O x1) x0) (\lambda (H34: (eq T 
(THead (Flat Appl) (lift (S O) O x) x0) (THead (Flat Appl) (lift (S O) O x1) 
x0))).(\lambda (P: Prop).(let H35 \def (f_equal T T (\lambda (e: T).(match e 
in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow ((let rec lref_map 
(f: ((nat \to nat))) (d: nat) (t0: T) on t0: T \def (match t0 with [(TSort n) 
\Rightarrow (TSort n) | (TLRef i) \Rightarrow (TLRef (match (blt i d) with 
[true \Rightarrow i | false \Rightarrow (f i)])) | (THead k u0 t4) 
\Rightarrow (THead k (lref_map f d u0) (lref_map f (s k d) t4))]) in 
lref_map) (\lambda (x5: nat).(plus x5 (S O))) O x) | (TLRef _) \Rightarrow 
((let rec lref_map (f: ((nat \to nat))) (d: nat) (t0: T) on t0: T \def (match 
t0 with [(TSort n) \Rightarrow (TSort n) | (TLRef i) \Rightarrow (TLRef 
(match (blt i d) with [true \Rightarrow i | false \Rightarrow (f i)])) | 
(THead k u0 t4) \Rightarrow (THead k (lref_map f d u0) (lref_map f (s k d) 
t4))]) in lref_map) (\lambda (x5: nat).(plus x5 (S O))) O x) | (THead _ t0 _) 
\Rightarrow t0])) (THead (Flat Appl) (lift (S O) O x) x0) (THead (Flat Appl) 
(lift (S O) O x1) x0) H34) in (let H36 \def (eq_ind_r T x1 (\lambda (t0: 
T).((eq T x t0) \to (\forall (P0: Prop).P0))) H33 x (lift_inj x x1 (S O) O 
H35)) in (let H37 \def (eq_ind_r T x1 (\lambda (t0: T).(pr2 c x t0)) H15 x 
(lift_inj x x1 (S O) O H35)) in (H36 (refl_equal T x) P)))))) (pr3_flat 
(CHead c (Bind b) t1) (lift (S O) O x) (lift (S O) O x1) (pr3_lift (CHead c 
(Bind b) t1) c (S O) O (drop_drop (Bind b) O c c (drop_refl c) t1) x x1 
(pr3_pr2 c x x1 H15)) x0 x0 (pr3_refl (CHead c (Bind b) t1) x0) Appl) x1 x0 
(refl_equal T (THead (Flat Appl) (lift (S O) O x1) x0)))) H32))) x4 H29)))) 
(\lambda (H29: (((eq T x0 x4) \to (\forall (P: Prop).P)))).(H8 (THead (Flat 
Appl) (lift (S O) O x1) x4) (\lambda (H30: (eq T (THead (Flat Appl) (lift (S 
O) O x) x0) (THead (Flat Appl) (lift (S O) O x1) x4))).(\lambda (P: 
Prop).(let H31 \def (f_equal T T (\lambda (e: T).(match e in T return 
(\lambda (_: T).T) with [(TSort _) \Rightarrow ((let rec lref_map (f: ((nat 
\to nat))) (d: nat) (t0: T) on t0: T \def (match t0 with [(TSort n) 
\Rightarrow (TSort n) | (TLRef i) \Rightarrow (TLRef (match (blt i d) with 
[true \Rightarrow i | false \Rightarrow (f i)])) | (THead k u0 t4) 
\Rightarrow (THead k (lref_map f d u0) (lref_map f (s k d) t4))]) in 
lref_map) (\lambda (x5: nat).(plus x5 (S O))) O x) | (TLRef _) \Rightarrow 
((let rec lref_map (f: ((nat \to nat))) (d: nat) (t0: T) on t0: T \def (match 
t0 with [(TSort n) \Rightarrow (TSort n) | (TLRef i) \Rightarrow (TLRef 
(match (blt i d) with [true \Rightarrow i | false \Rightarrow (f i)])) | 
(THead k u0 t4) \Rightarrow (THead k (lref_map f d u0) (lref_map f (s k d) 
t4))]) in lref_map) (\lambda (x5: nat).(plus x5 (S O))) O x) | (THead _ t0 _) 
\Rightarrow t0])) (THead (Flat Appl) (lift (S O) O x) x0) (THead (Flat Appl) 
(lift (S O) O x1) x4) H30) in ((let H32 \def (f_equal T T (\lambda (e: 
T).(match e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow x0 | 
(TLRef _) \Rightarrow x0 | (THead _ _ t0) \Rightarrow t0])) (THead (Flat 
Appl) (lift (S O) O x) x0) (THead (Flat Appl) (lift (S O) O x1) x4) H30) in 
(\lambda (H33: (eq T (lift (S O) O x) (lift (S O) O x1))).(let H34 \def 
(eq_ind_r T x4 (\lambda (t0: T).((eq T x0 t0) \to (\forall (P0: Prop).P0))) 
H29 x0 H32) in (let H35 \def (eq_ind_r T x4 (\lambda (t0: T).((eq T (THead 
(Flat Appl) x (THead (Bind b) t1 x0)) (THead (Flat Appl) x1 (THead (Bind b) 
t1 t0))) \to (\forall (P0: Prop).P0))) H26 x0 H32) in (let H36 \def (eq_ind_r 
T x4 (\lambda (t0: T).(pr3 (CHead c (Bind b) t1) x0 t0)) H22 x0 H32) in (let 
H37 \def (eq_ind_r T x1 (\lambda (t0: T).((eq T (THead (Flat Appl) x (THead 
(Bind b) t1 x0)) (THead (Flat Appl) t0 (THead (Bind b) t1 x0))) \to (\forall 
(P0: Prop).P0))) H35 x (lift_inj x x1 (S O) O H33)) in (let H38 \def 
(eq_ind_r T x1 (\lambda (t0: T).(pr2 c x t0)) H15 x (lift_inj x x1 (S O) O 
H33)) in (H34 (refl_equal T x0) P)))))))) H31)))) (pr3_flat (CHead c (Bind b) 
t1) (lift (S O) O x) (lift (S O) O x1) (pr3_lift (CHead c (Bind b) t1) c (S 
O) O (drop_drop (Bind b) O c c (drop_refl c) t1) x x1 (pr3_pr2 c x x1 H15)) 
x0 x4 H22 Appl) x1 x4 (refl_equal T (THead (Flat Appl) (lift (S O) O x1) 
x4)))) H28))) x3 H25)))) (\lambda (H25: (((eq T t1 x3) \to (\forall (P: 
Prop).P)))).(H2 x3 H25 H21 x4 x1 (sn3_cpr3_trans c t1 x3 H21 (Bind b) (THead 
(Flat Appl) (lift (S O) O x1) x4) (let H_x1 \def (term_dec x0 x4) in (let H26 
\def H_x1 in (or_ind (eq T x0 x4) ((eq T x0 x4) \to (\forall (P: Prop).P)) 
(sn3 (CHead c (Bind b) t1) (THead (Flat Appl) (lift (S O) O x1) x4)) (\lambda 
(H27: (eq T x0 x4)).(let H28 \def (eq_ind_r T x4 (\lambda (t0: T).(pr3 (CHead 
c (Bind b) t1) x0 t0)) H22 x0 H27) in (eq_ind T x0 (\lambda (t0: T).(sn3 
(CHead c (Bind b) t1) (THead (Flat Appl) (lift (S O) O x1) t0))) (let H_x2 
\def (term_dec x x1) in (let H29 \def H_x2 in (or_ind (eq T x x1) ((eq T x 
x1) \to (\forall (P: Prop).P)) (sn3 (CHead c (Bind b) t1) (THead (Flat Appl) 
(lift (S O) O x1) x0)) (\lambda (H30: (eq T x x1)).(let H31 \def (eq_ind_r T 
x1 (\lambda (t0: T).(pr2 c x t0)) H15 x H30) in (eq_ind T x (\lambda (t0: 
T).(sn3 (CHead c (Bind b) t1) (THead (Flat Appl) (lift (S O) O t0) x0))) 
(sn3_sing (CHead c (Bind b) t1) (THead (Flat Appl) (lift (S O) O x) x0) H9) 
x1 H30))) (\lambda (H30: (((eq T x x1) \to (\forall (P: Prop).P)))).(H9 
(THead (Flat Appl) (lift (S O) O x1) x0) (\lambda (H31: (eq T (THead (Flat 
Appl) (lift (S O) O x) x0) (THead (Flat Appl) (lift (S O) O x1) 
x0))).(\lambda (P: Prop).(let H32 \def (f_equal T T (\lambda (e: T).(match e 
in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow ((let rec lref_map 
(f: ((nat \to nat))) (d: nat) (t0: T) on t0: T \def (match t0 with [(TSort n) 
\Rightarrow (TSort n) | (TLRef i) \Rightarrow (TLRef (match (blt i d) with 
[true \Rightarrow i | false \Rightarrow (f i)])) | (THead k u0 t4) 
\Rightarrow (THead k (lref_map f d u0) (lref_map f (s k d) t4))]) in 
lref_map) (\lambda (x5: nat).(plus x5 (S O))) O x) | (TLRef _) \Rightarrow 
((let rec lref_map (f: ((nat \to nat))) (d: nat) (t0: T) on t0: T \def (match 
t0 with [(TSort n) \Rightarrow (TSort n) | (TLRef i) \Rightarrow (TLRef 
(match (blt i d) with [true \Rightarrow i | false \Rightarrow (f i)])) | 
(THead k u0 t4) \Rightarrow (THead k (lref_map f d u0) (lref_map f (s k d) 
t4))]) in lref_map) (\lambda (x5: nat).(plus x5 (S O))) O x) | (THead _ t0 _) 
\Rightarrow t0])) (THead (Flat Appl) (lift (S O) O x) x0) (THead (Flat Appl) 
(lift (S O) O x1) x0) H31) in (let H33 \def (eq_ind_r T x1 (\lambda (t0: 
T).((eq T x t0) \to (\forall (P0: Prop).P0))) H30 x (lift_inj x x1 (S O) O 
H32)) in (let H34 \def (eq_ind_r T x1 (\lambda (t0: T).(pr2 c x t0)) H15 x 
(lift_inj x x1 (S O) O H32)) in (H33 (refl_equal T x) P)))))) (pr3_flat 
(CHead c (Bind b) t1) (lift (S O) O x) (lift (S O) O x1) (pr3_lift (CHead c 
(Bind b) t1) c (S O) O (drop_drop (Bind b) O c c (drop_refl c) t1) x x1 
(pr3_pr2 c x x1 H15)) x0 x0 (pr3_refl (CHead c (Bind b) t1) x0) Appl))) 
H29))) x4 H27))) (\lambda (H27: (((eq T x0 x4) \to (\forall (P: 
Prop).P)))).(H9 (THead (Flat Appl) (lift (S O) O x1) x4) (\lambda (H28: (eq T 
(THead (Flat Appl) (lift (S O) O x) x0) (THead (Flat Appl) (lift (S O) O x1) 
x4))).(\lambda (P: Prop).(let H29 \def (f_equal T T (\lambda (e: T).(match e 
in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow ((let rec lref_map 
(f: ((nat \to nat))) (d: nat) (t0: T) on t0: T \def (match t0 with [(TSort n) 
\Rightarrow (TSort n) | (TLRef i) \Rightarrow (TLRef (match (blt i d) with 
[true \Rightarrow i | false \Rightarrow (f i)])) | (THead k u0 t4) 
\Rightarrow (THead k (lref_map f d u0) (lref_map f (s k d) t4))]) in 
lref_map) (\lambda (x5: nat).(plus x5 (S O))) O x) | (TLRef _) \Rightarrow 
((let rec lref_map (f: ((nat \to nat))) (d: nat) (t0: T) on t0: T \def (match 
t0 with [(TSort n) \Rightarrow (TSort n) | (TLRef i) \Rightarrow (TLRef 
(match (blt i d) with [true \Rightarrow i | false \Rightarrow (f i)])) | 
(THead k u0 t4) \Rightarrow (THead k (lref_map f d u0) (lref_map f (s k d) 
t4))]) in lref_map) (\lambda (x5: nat).(plus x5 (S O))) O x) | (THead _ t0 _) 
\Rightarrow t0])) (THead (Flat Appl) (lift (S O) O x) x0) (THead (Flat Appl) 
(lift (S O) O x1) x4) H28) in ((let H30 \def (f_equal T T (\lambda (e: 
T).(match e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow x0 | 
(TLRef _) \Rightarrow x0 | (THead _ _ t0) \Rightarrow t0])) (THead (Flat 
Appl) (lift (S O) O x) x0) (THead (Flat Appl) (lift (S O) O x1) x4) H28) in 
(\lambda (H31: (eq T (lift (S O) O x) (lift (S O) O x1))).(let H32 \def 
(eq_ind_r T x4 (\lambda (t0: T).((eq T x0 t0) \to (\forall (P0: Prop).P0))) 
H27 x0 H30) in (let H33 \def (eq_ind_r T x4 (\lambda (t0: T).(pr3 (CHead c 
(Bind b) t1) x0 t0)) H22 x0 H30) in (let H34 \def (eq_ind_r T x1 (\lambda 
(t0: T).(pr2 c x t0)) H15 x (lift_inj x x1 (S O) O H31)) in (H32 (refl_equal 
T x0) P)))))) H29)))) (pr3_flat (CHead c (Bind b) t1) (lift (S O) O x) (lift 
(S O) O x1) (pr3_lift (CHead c (Bind b) t1) c (S O) O (drop_drop (Bind b) O c 
c (drop_refl c) t1) x x1 (pr3_pr2 c x x1 H15)) x0 x4 H22 Appl))) H26)))))) 
H24))) x2 H20))))))) H19)) (\lambda (H19: (pr3 (CHead c (Bind b) t1) x0 (lift 
(S O) O x2))).(sn3_gen_lift (CHead c (Bind b) t1) (THead (Flat Appl) x1 x2) 
(S O) O (eq_ind_r T (THead (Flat Appl) (lift (S O) O x1) (lift (S O) (s (Flat 
Appl) O) x2)) (\lambda (t0: T).(sn3 (CHead c (Bind b) t1) t0)) (sn3_pr3_trans 
(CHead c (Bind b) t1) (THead (Flat Appl) (lift (S O) O x1) x0) (let H_x0 \def 
(term_dec x x1) in (let H20 \def H_x0 in (or_ind (eq T x x1) ((eq T x x1) \to 
(\forall (P: Prop).P)) (sn3 (CHead c (Bind b) t1) (THead (Flat Appl) (lift (S 
O) O x1) x0)) (\lambda (H21: (eq T x x1)).(let H22 \def (eq_ind_r T x1 
(\lambda (t0: T).(pr2 c x t0)) H15 x H21) in (eq_ind T x (\lambda (t0: 
T).(sn3 (CHead c (Bind b) t1) (THead (Flat Appl) (lift (S O) O t0) x0))) 
(sn3_sing (CHead c (Bind b) t1) (THead (Flat Appl) (lift (S O) O x) x0) H9) 
x1 H21))) (\lambda (H21: (((eq T x x1) \to (\forall (P: Prop).P)))).(H9 
(THead (Flat Appl) (lift (S O) O x1) x0) (\lambda (H22: (eq T (THead (Flat 
Appl) (lift (S O) O x) x0) (THead (Flat Appl) (lift (S O) O x1) 
x0))).(\lambda (P: Prop).(let H23 \def (f_equal T T (\lambda (e: T).(match e 
in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow ((let rec lref_map 
(f: ((nat \to nat))) (d: nat) (t0: T) on t0: T \def (match t0 with [(TSort n) 
\Rightarrow (TSort n) | (TLRef i) \Rightarrow (TLRef (match (blt i d) with 
[true \Rightarrow i | false \Rightarrow (f i)])) | (THead k u0 t4) 
\Rightarrow (THead k (lref_map f d u0) (lref_map f (s k d) t4))]) in 
lref_map) (\lambda (x3: nat).(plus x3 (S O))) O x) | (TLRef _) \Rightarrow 
((let rec lref_map (f: ((nat \to nat))) (d: nat) (t0: T) on t0: T \def (match 
t0 with [(TSort n) \Rightarrow (TSort n) | (TLRef i) \Rightarrow (TLRef 
(match (blt i d) with [true \Rightarrow i | false \Rightarrow (f i)])) | 
(THead k u0 t4) \Rightarrow (THead k (lref_map f d u0) (lref_map f (s k d) 
t4))]) in lref_map) (\lambda (x3: nat).(plus x3 (S O))) O x) | (THead _ t0 _) 
\Rightarrow t0])) (THead (Flat Appl) (lift (S O) O x) x0) (THead (Flat Appl) 
(lift (S O) O x1) x0) H22) in (let H24 \def (eq_ind_r T x1 (\lambda (t0: 
T).((eq T x t0) \to (\forall (P0: Prop).P0))) H21 x (lift_inj x x1 (S O) O 
H23)) in (let H25 \def (eq_ind_r T x1 (\lambda (t0: T).(pr2 c x t0)) H15 x 
(lift_inj x x1 (S O) O H23)) in (H24 (refl_equal T x) P)))))) (pr3_flat 
(CHead c (Bind b) t1) (lift (S O) O x) (lift (S O) O x1) (pr3_lift (CHead c 
(Bind b) t1) c (S O) O (drop_drop (Bind b) O c c (drop_refl c) t1) x x1 
(pr3_pr2 c x x1 H15)) x0 x0 (pr3_refl (CHead c (Bind b) t1) x0) Appl))) 
H20))) (THead (Flat Appl) (lift (S O) O x1) (lift (S O) O x2)) (pr3_thin_dx 
(CHead c (Bind b) t1) x0 (lift (S O) O x2) H19 (lift (S O) O x1) Appl)) (lift 
(S O) O (THead (Flat Appl) x1 x2)) (lift_head (Flat Appl) x1 x2 (S O) O)) c 
(drop_drop (Bind b) O c c (drop_refl c) t1))) H18))) t3 H14))))))) H13)) 
(\lambda (H13: (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(eq T (THead (Bind b) t1 x0) (THead (Bind Abst) y1 
z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t4: 
T).(eq T t3 (THead (Bind Abbr) u2 t4)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c x u2))))) (\lambda (_: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (t4: T).(\forall (b0: B).(\forall (u0: 
T).(pr2 (CHead c (Bind b0) u0) z1 t4))))))))).(ex4_4_ind T T T T (\lambda 
(y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind 
b) t1 x0) (THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (t4: T).(eq T t3 (THead (Bind Abbr) u2 t4)))))) 
(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c x 
u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t4: 
T).(\forall (b0: B).(\forall (u0: T).(pr2 (CHead c (Bind b0) u0) z1 t4))))))) 
(sn3 c t3) (\lambda (x1: T).(\lambda (x2: T).(\lambda (x3: T).(\lambda (x4: 
T).(\lambda (H14: (eq T (THead (Bind b) t1 x0) (THead (Bind Abst) x1 
x2))).(\lambda (H15: (eq T t3 (THead (Bind Abbr) x3 x4))).(\lambda (_: (pr2 c 
x x3)).(\lambda (H17: ((\forall (b0: B).(\forall (u0: T).(pr2 (CHead c (Bind 
b0) u0) x2 x4))))).(let H18 \def (eq_ind T t3 (\lambda (t0: T).((eq T (THead 
(Flat Appl) x (THead (Bind b) t1 x0)) t0) \to (\forall (P: Prop).P))) H10 
(THead (Bind Abbr) x3 x4) H15) in (eq_ind_r T (THead (Bind Abbr) x3 x4) 
(\lambda (t0: T).(sn3 c t0)) (let H19 \def (f_equal T B (\lambda (e: 
T).(match e in T return (\lambda (_: T).B) with [(TSort _) \Rightarrow b | 
(TLRef _) \Rightarrow b | (THead k _ _) \Rightarrow (match k in K return 
(\lambda (_: K).B) with [(Bind b0) \Rightarrow b0 | (Flat _) \Rightarrow 
b])])) (THead (Bind b) t1 x0) (THead (Bind Abst) x1 x2) H14) in ((let H20 
\def (f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) 
with [(TSort _) \Rightarrow t1 | (TLRef _) \Rightarrow t1 | (THead _ t0 _) 
\Rightarrow t0])) (THead (Bind b) t1 x0) (THead (Bind Abst) x1 x2) H14) in 
((let H21 \def (f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: 
T).T) with [(TSort _) \Rightarrow x0 | (TLRef _) \Rightarrow x0 | (THead _ _ 
t0) \Rightarrow t0])) (THead (Bind b) t1 x0) (THead (Bind Abst) x1 x2) H14) 
in (\lambda (_: (eq T t1 x1)).(\lambda (H23: (eq B b Abst)).(let H24 \def 
(eq_ind_r T x2 (\lambda (t0: T).(\forall (b0: B).(\forall (u0: T).(pr2 (CHead 
c (Bind b0) u0) t0 x4)))) H17 x0 H21) in (let H25 \def (eq_ind B b (\lambda 
(b0: B).((eq T (THead (Flat Appl) x (THead (Bind b0) t1 x0)) (THead (Bind 
Abbr) x3 x4)) \to (\forall (P: Prop).P))) H18 Abst H23) in (let H26 \def 
(eq_ind B b (\lambda (b0: B).(\forall (t4: T).((((eq T (THead (Flat Appl) 
(lift (S O) O x) x0) t4) \to (\forall (P: Prop).P))) \to ((pr3 (CHead c (Bind 
b0) t1) (THead (Flat Appl) (lift (S O) O x) x0) t4) \to (sn3 (CHead c (Bind 
b0) t1) t4))))) H9 Abst H23) in (let H27 \def (eq_ind B b (\lambda (b0: 
B).(\forall (t4: T).((((eq T (THead (Flat Appl) (lift (S O) O x) x0) t4) \to 
(\forall (P: Prop).P))) \to ((pr3 (CHead c (Bind b0) t1) (THead (Flat Appl) 
(lift (S O) O x) x0) t4) \to (\forall (x5: T).(\forall (x6: T).((eq T t4 
(THead (Flat Appl) (lift (S O) O x5) x6)) \to (sn3 c (THead (Flat Appl) x5 
(THead (Bind b0) t1 x6)))))))))) H8 Abst H23) in (let H28 \def (eq_ind B b 
(\lambda (b0: B).(\forall (t4: T).((((eq T t1 t4) \to (\forall (P: Prop).P))) 
\to ((pr3 c t1 t4) \to (\forall (t0: T).(\forall (v0: T).((sn3 (CHead c (Bind 
b0) t4) (THead (Flat Appl) (lift (S O) O v0) t0)) \to (sn3 c (THead (Flat 
Appl) v0 (THead (Bind b0) t4 t0)))))))))) H2 Abst H23) in (let H29 \def 
(eq_ind B b (\lambda (b0: B).(not (eq B b0 Abst))) H Abst H23) in (let H30 
\def (match (H29 (refl_equal B Abst)) in False return (\lambda (_: 
False).(sn3 c (THead (Bind Abbr) x3 x4))) with []) in H30)))))))))) H20)) 
H19)) t3 H15)))))))))) H13)) (\lambda (H13: (ex6_6 B T T T T T (\lambda (b0: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(not (eq B b0 Abst)))))))) (\lambda (b0: B).(\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind b) 
t1 x0) (THead (Bind b0) y1 z1)))))))) (\lambda (b0: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T 
t3 (THead (Bind b0) y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) 
(\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr2 c x u2))))))) (\lambda (_: B).(\lambda (y1: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 
y2))))))) (\lambda (b0: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b0) y2) z1 
z2))))))))).(ex6_6_ind B T T T T T (\lambda (b0: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b0 
Abst)))))))) (\lambda (b0: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind b) t1 x0) (THead (Bind 
b0) y1 z1)))))))) (\lambda (b0: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T t3 (THead (Bind b0) y2 (THead 
(Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c x 
u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 y2))))))) (\lambda (b0: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 (CHead c (Bind b0) y2) z1 z2))))))) (sn3 c t3) (\lambda (x1: 
B).(\lambda (x2: T).(\lambda (x3: T).(\lambda (x4: T).(\lambda (x5: 
T).(\lambda (x6: T).(\lambda (_: (not (eq B x1 Abst))).(\lambda (H15: (eq T 
(THead (Bind b) t1 x0) (THead (Bind x1) x2 x3))).(\lambda (H16: (eq T t3 
(THead (Bind x1) x6 (THead (Flat Appl) (lift (S O) O x5) x4)))).(\lambda 
(H17: (pr2 c x x5)).(\lambda (H18: (pr2 c x2 x6)).(\lambda (H19: (pr2 (CHead 
c (Bind x1) x6) x3 x4)).(let H20 \def (eq_ind T t3 (\lambda (t0: T).((eq T 
(THead (Flat Appl) x (THead (Bind b) t1 x0)) t0) \to (\forall (P: Prop).P))) 
H10 (THead (Bind x1) x6 (THead (Flat Appl) (lift (S O) O x5) x4)) H16) in 
(eq_ind_r T (THead (Bind x1) x6 (THead (Flat Appl) (lift (S O) O x5) x4)) 
(\lambda (t0: T).(sn3 c t0)) (let H21 \def (f_equal T B (\lambda (e: 
T).(match e in T return (\lambda (_: T).B) with [(TSort _) \Rightarrow b | 
(TLRef _) \Rightarrow b | (THead k _ _) \Rightarrow (match k in K return 
(\lambda (_: K).B) with [(Bind b0) \Rightarrow b0 | (Flat _) \Rightarrow 
b])])) (THead (Bind b) t1 x0) (THead (Bind x1) x2 x3) H15) in ((let H22 \def 
(f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) with 
[(TSort _) \Rightarrow t1 | (TLRef _) \Rightarrow t1 | (THead _ t0 _) 
\Rightarrow t0])) (THead (Bind b) t1 x0) (THead (Bind x1) x2 x3) H15) in 
((let H23 \def (f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: 
T).T) with [(TSort _) \Rightarrow x0 | (TLRef _) \Rightarrow x0 | (THead _ _ 
t0) \Rightarrow t0])) (THead (Bind b) t1 x0) (THead (Bind x1) x2 x3) H15) in 
(\lambda (H24: (eq T t1 x2)).(\lambda (H25: (eq B b x1)).(let H26 \def 
(eq_ind_r T x3 (\lambda (t0: T).(pr2 (CHead c (Bind x1) x6) t0 x4)) H19 x0 
H23) in (let H27 \def (eq_ind_r T x2 (\lambda (t0: T).(pr2 c t0 x6)) H18 t1 
H24) in (let H28 \def (eq_ind_r B x1 (\lambda (b0: B).(pr2 (CHead c (Bind b0) 
x6) x0 x4)) H26 b H25) in (eq_ind B b (\lambda (b0: B).(sn3 c (THead (Bind 
b0) x6 (THead (Flat Appl) (lift (S O) O x5) x4)))) (sn3_pr3_trans c (THead 
(Bind b) t1 (THead (Flat Appl) (lift (S O) O x5) x4)) (sn3_bind b H c t1 
(sn3_sing c t1 H1) (THead (Flat Appl) (lift (S O) O x5) x4) (let H_x \def 
(term_dec x x5) in (let H29 \def H_x in (or_ind (eq T x x5) ((eq T x x5) \to 
(\forall (P: Prop).P)) (sn3 (CHead c (Bind b) t1) (THead (Flat Appl) (lift (S 
O) O x5) x4)) (\lambda (H30: (eq T x x5)).(let H31 \def (eq_ind_r T x5 
(\lambda (t0: T).(pr2 c x t0)) H17 x H30) in (eq_ind T x (\lambda (t0: 
T).(sn3 (CHead c (Bind b) t1) (THead (Flat Appl) (lift (S O) O t0) x4))) (let 
H_x0 \def (term_dec x0 x4) in (let H32 \def H_x0 in (or_ind (eq T x0 x4) ((eq 
T x0 x4) \to (\forall (P: Prop).P)) (sn3 (CHead c (Bind b) t1) (THead (Flat 
Appl) (lift (S O) O x) x4)) (\lambda (H33: (eq T x0 x4)).(let H34 \def 
(eq_ind_r T x4 (\lambda (t0: T).(pr2 (CHead c (Bind b) x6) x0 t0)) H28 x0 
H33) in (eq_ind T x0 (\lambda (t0: T).(sn3 (CHead c (Bind b) t1) (THead (Flat 
Appl) (lift (S O) O x) t0))) (sn3_sing (CHead c (Bind b) t1) (THead (Flat 
Appl) (lift (S O) O x) x0) H9) x4 H33))) (\lambda (H33: (((eq T x0 x4) \to 
(\forall (P: Prop).P)))).(H9 (THead (Flat Appl) (lift (S O) O x) x4) (\lambda 
(H34: (eq T (THead (Flat Appl) (lift (S O) O x) x0) (THead (Flat Appl) (lift 
(S O) O x) x4))).(\lambda (P: Prop).(let H35 \def (f_equal T T (\lambda (e: 
T).(match e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow x0 | 
(TLRef _) \Rightarrow x0 | (THead _ _ t0) \Rightarrow t0])) (THead (Flat 
Appl) (lift (S O) O x) x0) (THead (Flat Appl) (lift (S O) O x) x4) H34) in 
(let H36 \def (eq_ind_r T x4 (\lambda (t0: T).((eq T x0 t0) \to (\forall (P0: 
Prop).P0))) H33 x0 H35) in (let H37 \def (eq_ind_r T x4 (\lambda (t0: T).(pr2 
(CHead c (Bind b) x6) x0 t0)) H28 x0 H35) in (H36 (refl_equal T x0) P)))))) 
(pr3_pr3_pr3_t c t1 x6 (pr3_pr2 c t1 x6 H27) (THead (Flat Appl) (lift (S O) O 
x) x0) (THead (Flat Appl) (lift (S O) O x) x4) (Bind b) (pr3_pr2 (CHead c 
(Bind b) x6) (THead (Flat Appl) (lift (S O) O x) x0) (THead (Flat Appl) (lift 
(S O) O x) x4) (pr2_thin_dx (CHead c (Bind b) x6) x0 x4 H28 (lift (S O) O x) 
Appl))))) H32))) x5 H30))) (\lambda (H30: (((eq T x x5) \to (\forall (P: 
Prop).P)))).(H9 (THead (Flat Appl) (lift (S O) O x5) x4) (\lambda (H31: (eq T 
(THead (Flat Appl) (lift (S O) O x) x0) (THead (Flat Appl) (lift (S O) O x5) 
x4))).(\lambda (P: Prop).(let H32 \def (f_equal T T (\lambda (e: T).(match e 
in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow ((let rec lref_map 
(f: ((nat \to nat))) (d: nat) (t0: T) on t0: T \def (match t0 with [(TSort n) 
\Rightarrow (TSort n) | (TLRef i) \Rightarrow (TLRef (match (blt i d) with 
[true \Rightarrow i | false \Rightarrow (f i)])) | (THead k u0 t4) 
\Rightarrow (THead k (lref_map f d u0) (lref_map f (s k d) t4))]) in 
lref_map) (\lambda (x7: nat).(plus x7 (S O))) O x) | (TLRef _) \Rightarrow 
((let rec lref_map (f: ((nat \to nat))) (d: nat) (t0: T) on t0: T \def (match 
t0 with [(TSort n) \Rightarrow (TSort n) | (TLRef i) \Rightarrow (TLRef 
(match (blt i d) with [true \Rightarrow i | false \Rightarrow (f i)])) | 
(THead k u0 t4) \Rightarrow (THead k (lref_map f d u0) (lref_map f (s k d) 
t4))]) in lref_map) (\lambda (x7: nat).(plus x7 (S O))) O x) | (THead _ t0 _) 
\Rightarrow t0])) (THead (Flat Appl) (lift (S O) O x) x0) (THead (Flat Appl) 
(lift (S O) O x5) x4) H31) in ((let H33 \def (f_equal T T (\lambda (e: 
T).(match e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow x0 | 
(TLRef _) \Rightarrow x0 | (THead _ _ t0) \Rightarrow t0])) (THead (Flat 
Appl) (lift (S O) O x) x0) (THead (Flat Appl) (lift (S O) O x5) x4) H31) in 
(\lambda (H34: (eq T (lift (S O) O x) (lift (S O) O x5))).(let H35 \def 
(eq_ind_r T x5 (\lambda (t0: T).((eq T x t0) \to (\forall (P0: Prop).P0))) 
H30 x (lift_inj x x5 (S O) O H34)) in (let H36 \def (eq_ind_r T x5 (\lambda 
(t0: T).(pr2 c x t0)) H17 x (lift_inj x x5 (S O) O H34)) in (let H37 \def 
(eq_ind_r T x4 (\lambda (t0: T).(pr2 (CHead c (Bind b) x6) x0 t0)) H28 x0 
H33) in (H35 (refl_equal T x) P)))))) H32)))) (pr3_pr3_pr3_t c t1 x6 (pr3_pr2 
c t1 x6 H27) (THead (Flat Appl) (lift (S O) O x) x0) (THead (Flat Appl) (lift 
(S O) O x5) x4) (Bind b) (pr3_flat (CHead c (Bind b) x6) (lift (S O) O x) 
(lift (S O) O x5) (pr3_lift (CHead c (Bind b) x6) c (S O) O (drop_drop (Bind 
b) O c c (drop_refl c) x6) x x5 (pr3_pr2 c x x5 H17)) x0 x4 (pr3_pr2 (CHead c 
(Bind b) x6) x0 x4 H28) Appl)))) H29)))) (THead (Bind b) x6 (THead (Flat 
Appl) (lift (S O) O x5) x4)) (pr3_pr2 c (THead (Bind b) t1 (THead (Flat Appl) 
(lift (S O) O x5) x4)) (THead (Bind b) x6 (THead (Flat Appl) (lift (S O) O 
x5) x4)) (pr2_head_1 c t1 x6 H27 (Bind b) (THead (Flat Appl) (lift (S O) O 
x5) x4)))) x1 H25))))))) H22)) H21)) t3 H16)))))))))))))) H13)) 
H12)))))))))))))) y H4))))) H3))))))) u H0))))).

theorem sn3_appl_beta:
 \forall (c: C).(\forall (u: T).(\forall (v: T).(\forall (t: T).((sn3 c 
(THead (Flat Appl) u (THead (Bind Abbr) v t))) \to (\forall (w: T).((sn3 c w) 
\to (sn3 c (THead (Flat Appl) u (THead (Flat Appl) v (THead (Bind Abst) w 
t))))))))))
\def
 \lambda (c: C).(\lambda (u: T).(\lambda (v: T).(\lambda (t: T).(\lambda (H: 
(sn3 c (THead (Flat Appl) u (THead (Bind Abbr) v t)))).(\lambda (w: 
T).(\lambda (H0: (sn3 c w)).(let H1 \def (sn3_gen_flat Appl c u (THead (Bind 
Abbr) v t) H) in (and_ind (sn3 c u) (sn3 c (THead (Bind Abbr) v t)) (sn3 c 
(THead (Flat Appl) u (THead (Flat Appl) v (THead (Bind Abst) w t)))) (\lambda 
(H2: (sn3 c u)).(\lambda (H3: (sn3 c (THead (Bind Abbr) v t))).(sn3_appl_appl 
v (THead (Bind Abst) w t) c (sn3_beta c v t H3 w H0) u H2 (\lambda (u2: 
T).(\lambda (H4: (pr3 c (THead (Flat Appl) v (THead (Bind Abst) w t)) 
u2)).(\lambda (H5: (((iso (THead (Flat Appl) v (THead (Bind Abst) w t)) u2) 
\to (\forall (P: Prop).P)))).(sn3_pr3_trans c (THead (Flat Appl) u (THead 
(Bind Abbr) v t)) H (THead (Flat Appl) u u2) (pr3_thin_dx c (THead (Bind 
Abbr) v t) u2 (pr3_iso_beta v w t c u2 H4 H5) u Appl)))))))) H1)))))))).

theorem sn3_appls_bind:
 \forall (b: B).((not (eq B b Abst)) \to (\forall (c: C).(\forall (u: 
T).((sn3 c u) \to (\forall (vs: TList).(\forall (t: T).((sn3 (CHead c (Bind 
b) u) (THeads (Flat Appl) (lifts (S O) O vs) t)) \to (sn3 c (THeads (Flat 
Appl) vs (THead (Bind b) u t))))))))))
\def
 \lambda (b: B).(\lambda (H: (not (eq B b Abst))).(\lambda (c: C).(\lambda 
(u: T).(\lambda (H0: (sn3 c u)).(\lambda (vs: TList).(TList_ind (\lambda (t: 
TList).(\forall (t0: T).((sn3 (CHead c (Bind b) u) (THeads (Flat Appl) (lifts 
(S O) O t) t0)) \to (sn3 c (THeads (Flat Appl) t (THead (Bind b) u t0)))))) 
(\lambda (t: T).(\lambda (H1: (sn3 (CHead c (Bind b) u) t)).(sn3_bind b H c u 
H0 t H1))) (\lambda (v: T).(\lambda (vs0: TList).(TList_ind (\lambda (t: 
TList).(((\forall (t0: T).((sn3 (CHead c (Bind b) u) (THeads (Flat Appl) 
(lifts (S O) O t) t0)) \to (sn3 c (THeads (Flat Appl) t (THead (Bind b) u 
t0)))))) \to (\forall (t0: T).((sn3 (CHead c (Bind b) u) (THead (Flat Appl) 
(lift (S O) O v) (THeads (Flat Appl) (lifts (S O) O t) t0))) \to (sn3 c 
(THead (Flat Appl) v (THeads (Flat Appl) t (THead (Bind b) u t0)))))))) 
(\lambda (_: ((\forall (t: T).((sn3 (CHead c (Bind b) u) (THeads (Flat Appl) 
(lifts (S O) O TNil) t)) \to (sn3 c (THeads (Flat Appl) TNil (THead (Bind b) 
u t))))))).(\lambda (t: T).(\lambda (H2: (sn3 (CHead c (Bind b) u) (THead 
(Flat Appl) (lift (S O) O v) (THeads (Flat Appl) (lifts (S O) O TNil) 
t)))).(sn3_appl_bind b H c u H0 t v H2)))) (\lambda (t: T).(\lambda (t0: 
TList).(\lambda (_: ((((\forall (t1: T).((sn3 (CHead c (Bind b) u) (THeads 
(Flat Appl) (lifts (S O) O t0) t1)) \to (sn3 c (THeads (Flat Appl) t0 (THead 
(Bind b) u t1)))))) \to (\forall (t1: T).((sn3 (CHead c (Bind b) u) (THead 
(Flat Appl) (lift (S O) O v) (THeads (Flat Appl) (lifts (S O) O t0) t1))) \to 
(sn3 c (THead (Flat Appl) v (THeads (Flat Appl) t0 (THead (Bind b) u 
t1))))))))).(\lambda (H2: ((\forall (t1: T).((sn3 (CHead c (Bind b) u) 
(THeads (Flat Appl) (lifts (S O) O (TCons t t0)) t1)) \to (sn3 c (THeads 
(Flat Appl) (TCons t t0) (THead (Bind b) u t1))))))).(\lambda (t1: 
T).(\lambda (H3: (sn3 (CHead c (Bind b) u) (THead (Flat Appl) (lift (S O) O 
v) (THeads (Flat Appl) (lifts (S O) O (TCons t t0)) t1)))).(let H4 \def 
(sn3_gen_flat Appl (CHead c (Bind b) u) (lift (S O) O v) (THeads (Flat Appl) 
(lifts (S O) O (TCons t t0)) t1) H3) in (and_ind (sn3 (CHead c (Bind b) u) 
(lift (S O) O v)) (sn3 (CHead c (Bind b) u) (THead (Flat Appl) (lift (S O) O 
t) (THeads (Flat Appl) (lifts (S O) O t0) t1))) (sn3 c (THead (Flat Appl) v 
(THeads (Flat Appl) (TCons t t0) (THead (Bind b) u t1)))) (\lambda (H5: (sn3 
(CHead c (Bind b) u) (lift (S O) O v))).(\lambda (H6: (sn3 (CHead c (Bind b) 
u) (THead (Flat Appl) (lift (S O) O t) (THeads (Flat Appl) (lifts (S O) O t0) 
t1)))).(let H_y \def (sn3_gen_lift (CHead c (Bind b) u) v (S O) O H5 c) in 
(sn3_appl_appls t (THead (Bind b) u t1) t0 c (H2 t1 H6) v (H_y (drop_drop 
(Bind b) O c c (drop_refl c) u)) (\lambda (u2: T).(\lambda (H7: (pr3 c 
(THeads (Flat Appl) (TCons t t0) (THead (Bind b) u t1)) u2)).(\lambda (H8: 
(((iso (THeads (Flat Appl) (TCons t t0) (THead (Bind b) u t1)) u2) \to 
(\forall (P: Prop).P)))).(let H9 \def (pr3_iso_appls_bind b H (TCons t t0) u 
t1 c u2 H7 H8) in (sn3_pr3_trans c (THead (Flat Appl) v (THead (Bind b) u 
(THeads (Flat Appl) (lifts (S O) O (TCons t t0)) t1))) (sn3_appl_bind b H c u 
H0 (THeads (Flat Appl) (lifts (S O) O (TCons t t0)) t1) v H3) (THead (Flat 
Appl) v u2) (pr3_flat c v v (pr3_refl c v) (THead (Bind b) u (THeads (Flat 
Appl) (lifts (S O) O (TCons t t0)) t1)) u2 H9 Appl)))))))))) H4)))))))) 
vs0))) vs)))))).

theorem sn3_appls_beta:
 \forall (c: C).(\forall (v: T).(\forall (t: T).(\forall (us: TList).((sn3 c 
(THeads (Flat Appl) us (THead (Bind Abbr) v t))) \to (\forall (w: T).((sn3 c 
w) \to (sn3 c (THeads (Flat Appl) us (THead (Flat Appl) v (THead (Bind Abst) 
w t))))))))))
\def
 \lambda (c: C).(\lambda (v: T).(\lambda (t: T).(\lambda (us: 
TList).(TList_ind (\lambda (t0: TList).((sn3 c (THeads (Flat Appl) t0 (THead 
(Bind Abbr) v t))) \to (\forall (w: T).((sn3 c w) \to (sn3 c (THeads (Flat 
Appl) t0 (THead (Flat Appl) v (THead (Bind Abst) w t)))))))) (\lambda (H: 
(sn3 c (THead (Bind Abbr) v t))).(\lambda (w: T).(\lambda (H0: (sn3 c 
w)).(sn3_beta c v t H w H0)))) (\lambda (u: T).(\lambda (us0: 
TList).(TList_ind (\lambda (t0: TList).((((sn3 c (THeads (Flat Appl) t0 
(THead (Bind Abbr) v t))) \to (\forall (w: T).((sn3 c w) \to (sn3 c (THeads 
(Flat Appl) t0 (THead (Flat Appl) v (THead (Bind Abst) w t)))))))) \to ((sn3 
c (THead (Flat Appl) u (THeads (Flat Appl) t0 (THead (Bind Abbr) v t)))) \to 
(\forall (w: T).((sn3 c w) \to (sn3 c (THead (Flat Appl) u (THeads (Flat 
Appl) t0 (THead (Flat Appl) v (THead (Bind Abst) w t)))))))))) (\lambda (_: 
(((sn3 c (THeads (Flat Appl) TNil (THead (Bind Abbr) v t))) \to (\forall (w: 
T).((sn3 c w) \to (sn3 c (THeads (Flat Appl) TNil (THead (Flat Appl) v (THead 
(Bind Abst) w t))))))))).(\lambda (H0: (sn3 c (THead (Flat Appl) u (THeads 
(Flat Appl) TNil (THead (Bind Abbr) v t))))).(\lambda (w: T).(\lambda (H1: 
(sn3 c w)).(sn3_appl_beta c u v t H0 w H1))))) (\lambda (t0: T).(\lambda (t1: 
TList).(\lambda (_: (((((sn3 c (THeads (Flat Appl) t1 (THead (Bind Abbr) v 
t))) \to (\forall (w: T).((sn3 c w) \to (sn3 c (THeads (Flat Appl) t1 (THead 
(Flat Appl) v (THead (Bind Abst) w t)))))))) \to ((sn3 c (THead (Flat Appl) u 
(THeads (Flat Appl) t1 (THead (Bind Abbr) v t)))) \to (\forall (w: T).((sn3 c 
w) \to (sn3 c (THead (Flat Appl) u (THeads (Flat Appl) t1 (THead (Flat Appl) 
v (THead (Bind Abst) w t))))))))))).(\lambda (H0: (((sn3 c (THeads (Flat 
Appl) (TCons t0 t1) (THead (Bind Abbr) v t))) \to (\forall (w: T).((sn3 c w) 
\to (sn3 c (THeads (Flat Appl) (TCons t0 t1) (THead (Flat Appl) v (THead 
(Bind Abst) w t))))))))).(\lambda (H1: (sn3 c (THead (Flat Appl) u (THeads 
(Flat Appl) (TCons t0 t1) (THead (Bind Abbr) v t))))).(\lambda (w: 
T).(\lambda (H2: (sn3 c w)).(let H3 \def (sn3_gen_flat Appl c u (THeads (Flat 
Appl) (TCons t0 t1) (THead (Bind Abbr) v t)) H1) in (and_ind (sn3 c u) (sn3 c 
(THead (Flat Appl) t0 (THeads (Flat Appl) t1 (THead (Bind Abbr) v t)))) (sn3 
c (THead (Flat Appl) u (THeads (Flat Appl) (TCons t0 t1) (THead (Flat Appl) v 
(THead (Bind Abst) w t))))) (\lambda (H4: (sn3 c u)).(\lambda (H5: (sn3 c 
(THead (Flat Appl) t0 (THeads (Flat Appl) t1 (THead (Bind Abbr) v 
t))))).(sn3_appl_appls t0 (THead (Flat Appl) v (THead (Bind Abst) w t)) t1 c 
(H0 H5 w H2) u H4 (\lambda (u2: T).(\lambda (H6: (pr3 c (THeads (Flat Appl) 
(TCons t0 t1) (THead (Flat Appl) v (THead (Bind Abst) w t))) u2)).(\lambda 
(H7: (((iso (THeads (Flat Appl) (TCons t0 t1) (THead (Flat Appl) v (THead 
(Bind Abst) w t))) u2) \to (\forall (P: Prop).P)))).(let H8 \def 
(pr3_iso_appls_beta (TCons t0 t1) v w t c u2 H6 H7) in (sn3_pr3_trans c 
(THead (Flat Appl) u (THeads (Flat Appl) (TCons t0 t1) (THead (Bind Abbr) v 
t))) H1 (THead (Flat Appl) u u2) (pr3_thin_dx c (THeads (Flat Appl) (TCons t0 
t1) (THead (Bind Abbr) v t)) u2 H8 u Appl))))))))) H3))))))))) us0))) us)))).

theorem sn3_appls_abbr:
 \forall (c: C).(\forall (d: C).(\forall (w: T).(\forall (i: nat).((getl i c 
(CHead d (Bind Abbr) w)) \to (\forall (vs: TList).((sn3 c (THeads (Flat Appl) 
vs (lift (S i) O w))) \to (sn3 c (THeads (Flat Appl) vs (TLRef i)))))))))
\def
 \lambda (c: C).(\lambda (d: C).(\lambda (w: T).(\lambda (i: nat).(\lambda 
(H: (getl i c (CHead d (Bind Abbr) w))).(\lambda (vs: TList).(TList_ind 
(\lambda (t: TList).((sn3 c (THeads (Flat Appl) t (lift (S i) O w))) \to (sn3 
c (THeads (Flat Appl) t (TLRef i))))) (\lambda (H0: (sn3 c (lift (S i) O 
w))).(let H_y \def (sn3_gen_lift c w (S i) O H0 d (getl_drop Abbr c d w i H)) 
in (sn3_abbr c d w i H H_y))) (\lambda (v: T).(\lambda (vs0: 
TList).(TList_ind (\lambda (t: TList).((((sn3 c (THeads (Flat Appl) t (lift 
(S i) O w))) \to (sn3 c (THeads (Flat Appl) t (TLRef i))))) \to ((sn3 c 
(THead (Flat Appl) v (THeads (Flat Appl) t (lift (S i) O w)))) \to (sn3 c 
(THead (Flat Appl) v (THeads (Flat Appl) t (TLRef i))))))) (\lambda (_: 
(((sn3 c (THeads (Flat Appl) TNil (lift (S i) O w))) \to (sn3 c (THeads (Flat 
Appl) TNil (TLRef i)))))).(\lambda (H1: (sn3 c (THead (Flat Appl) v (THeads 
(Flat Appl) TNil (lift (S i) O w))))).(nf3_appl_abbr c d w i H v H1))) 
(\lambda (t: T).(\lambda (t0: TList).(\lambda (_: (((((sn3 c (THeads (Flat 
Appl) t0 (lift (S i) O w))) \to (sn3 c (THeads (Flat Appl) t0 (TLRef i))))) 
\to ((sn3 c (THead (Flat Appl) v (THeads (Flat Appl) t0 (lift (S i) O w)))) 
\to (sn3 c (THead (Flat Appl) v (THeads (Flat Appl) t0 (TLRef 
i)))))))).(\lambda (H1: (((sn3 c (THeads (Flat Appl) (TCons t t0) (lift (S i) 
O w))) \to (sn3 c (THeads (Flat Appl) (TCons t t0) (TLRef i)))))).(\lambda 
(H2: (sn3 c (THead (Flat Appl) v (THeads (Flat Appl) (TCons t t0) (lift (S i) 
O w))))).(let H3 \def (sn3_gen_flat Appl c v (THeads (Flat Appl) (TCons t t0) 
(lift (S i) O w)) H2) in (and_ind (sn3 c v) (sn3 c (THead (Flat Appl) t 
(THeads (Flat Appl) t0 (lift (S i) O w)))) (sn3 c (THead (Flat Appl) v 
(THeads (Flat Appl) (TCons t t0) (TLRef i)))) (\lambda (H4: (sn3 c 
v)).(\lambda (H5: (sn3 c (THead (Flat Appl) t (THeads (Flat Appl) t0 (lift (S 
i) O w))))).(sn3_appl_appls t (TLRef i) t0 c (H1 H5) v H4 (\lambda (u2: 
T).(\lambda (H6: (pr3 c (THeads (Flat Appl) (TCons t t0) (TLRef i)) 
u2)).(\lambda (H7: (((iso (THeads (Flat Appl) (TCons t t0) (TLRef i)) u2) \to 
(\forall (P: Prop).P)))).(sn3_pr3_trans c (THead (Flat Appl) v (THeads (Flat 
Appl) (TCons t t0) (lift (S i) O w))) H2 (THead (Flat Appl) v u2) 
(pr3_thin_dx c (THeads (Flat Appl) (TCons t t0) (lift (S i) O w)) u2 
(pr3_iso_appls_abbr c d w i H (TCons t t0) u2 H6 H7) v Appl)))))))) H3))))))) 
vs0))) vs)))))).

