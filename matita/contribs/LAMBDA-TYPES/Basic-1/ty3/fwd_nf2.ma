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

include "Basic-1/ty3/arity_props.ma".

include "Basic-1/pc3/nf2.ma".

include "Basic-1/nf2/fwd.ma".

theorem ty3_gen_appl_nf2:
 \forall (g: G).(\forall (c: C).(\forall (w: T).(\forall (v: T).(\forall (x: 
T).((ty3 g c (THead (Flat Appl) w v) x) \to (ex4_2 T T (\lambda (u: 
T).(\lambda (t: T).(pc3 c (THead (Flat Appl) w (THead (Bind Abst) u t)) x))) 
(\lambda (u: T).(\lambda (t: T).(ty3 g c v (THead (Bind Abst) u t)))) 
(\lambda (u: T).(\lambda (_: T).(ty3 g c w u))) (\lambda (u: T).(\lambda (t: 
T).(nf2 c (THead (Bind Abst) u t))))))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (w: T).(\lambda (v: T).(\lambda (x: 
T).(\lambda (H: (ty3 g c (THead (Flat Appl) w v) x)).(ex3_2_ind T T (\lambda 
(u: T).(\lambda (t: T).(pc3 c (THead (Flat Appl) w (THead (Bind Abst) u t)) 
x))) (\lambda (u: T).(\lambda (t: T).(ty3 g c v (THead (Bind Abst) u t)))) 
(\lambda (u: T).(\lambda (_: T).(ty3 g c w u))) (ex4_2 T T (\lambda (u: 
T).(\lambda (t: T).(pc3 c (THead (Flat Appl) w (THead (Bind Abst) u t)) x))) 
(\lambda (u: T).(\lambda (t: T).(ty3 g c v (THead (Bind Abst) u t)))) 
(\lambda (u: T).(\lambda (_: T).(ty3 g c w u))) (\lambda (u: T).(\lambda (t: 
T).(nf2 c (THead (Bind Abst) u t))))) (\lambda (x0: T).(\lambda (x1: 
T).(\lambda (H0: (pc3 c (THead (Flat Appl) w (THead (Bind Abst) x0 x1)) 
x)).(\lambda (H1: (ty3 g c v (THead (Bind Abst) x0 x1))).(\lambda (H2: (ty3 g 
c w x0)).(let H_x \def (ty3_correct g c v (THead (Bind Abst) x0 x1) H1) in 
(let H3 \def H_x in (ex_ind T (\lambda (t: T).(ty3 g c (THead (Bind Abst) x0 
x1) t)) (ex4_2 T T (\lambda (u: T).(\lambda (t: T).(pc3 c (THead (Flat Appl) 
w (THead (Bind Abst) u t)) x))) (\lambda (u: T).(\lambda (t: T).(ty3 g c v 
(THead (Bind Abst) u t)))) (\lambda (u: T).(\lambda (_: T).(ty3 g c w u))) 
(\lambda (u: T).(\lambda (t: T).(nf2 c (THead (Bind Abst) u t))))) (\lambda 
(x2: T).(\lambda (H4: (ty3 g c (THead (Bind Abst) x0 x1) x2)).(let H_x0 \def 
(ty3_correct g c w x0 H2) in (let H5 \def H_x0 in (ex_ind T (\lambda (t: 
T).(ty3 g c x0 t)) (ex4_2 T T (\lambda (u: T).(\lambda (t: T).(pc3 c (THead 
(Flat Appl) w (THead (Bind Abst) u t)) x))) (\lambda (u: T).(\lambda (t: 
T).(ty3 g c v (THead (Bind Abst) u t)))) (\lambda (u: T).(\lambda (_: T).(ty3 
g c w u))) (\lambda (u: T).(\lambda (t: T).(nf2 c (THead (Bind Abst) u t))))) 
(\lambda (x3: T).(\lambda (H6: (ty3 g c x0 x3)).(let H7 \def (ty3_sn3 g c 
(THead (Bind Abst) x0 x1) x2 H4) in (let H_x1 \def (nf2_sn3 c (THead (Bind 
Abst) x0 x1) H7) in (let H8 \def H_x1 in (ex2_ind T (\lambda (u: T).(pr3 c 
(THead (Bind Abst) x0 x1) u)) (\lambda (u: T).(nf2 c u)) (ex4_2 T T (\lambda 
(u: T).(\lambda (t: T).(pc3 c (THead (Flat Appl) w (THead (Bind Abst) u t)) 
x))) (\lambda (u: T).(\lambda (t: T).(ty3 g c v (THead (Bind Abst) u t)))) 
(\lambda (u: T).(\lambda (_: T).(ty3 g c w u))) (\lambda (u: T).(\lambda (t: 
T).(nf2 c (THead (Bind Abst) u t))))) (\lambda (x4: T).(\lambda (H9: (pr3 c 
(THead (Bind Abst) x0 x1) x4)).(\lambda (H10: (nf2 c x4)).(let H11 \def 
(pr3_gen_abst c x0 x1 x4 H9) in (ex3_2_ind T T (\lambda (u2: T).(\lambda (t2: 
T).(eq T x4 (THead (Bind Abst) u2 t2)))) (\lambda (u2: T).(\lambda (_: 
T).(pr3 c x0 u2))) (\lambda (_: T).(\lambda (t2: T).(\forall (b: B).(\forall 
(u: T).(pr3 (CHead c (Bind b) u) x1 t2))))) (ex4_2 T T (\lambda (u: 
T).(\lambda (t: T).(pc3 c (THead (Flat Appl) w (THead (Bind Abst) u t)) x))) 
(\lambda (u: T).(\lambda (t: T).(ty3 g c v (THead (Bind Abst) u t)))) 
(\lambda (u: T).(\lambda (_: T).(ty3 g c w u))) (\lambda (u: T).(\lambda (t: 
T).(nf2 c (THead (Bind Abst) u t))))) (\lambda (x5: T).(\lambda (x6: 
T).(\lambda (H12: (eq T x4 (THead (Bind Abst) x5 x6))).(\lambda (H13: (pr3 c 
x0 x5)).(\lambda (H14: ((\forall (b: B).(\forall (u: T).(pr3 (CHead c (Bind 
b) u) x1 x6))))).(let H15 \def (eq_ind T x4 (\lambda (t: T).(nf2 c t)) H10 
(THead (Bind Abst) x5 x6) H12) in (let H16 \def (pr3_head_12 c x0 x5 H13 
(Bind Abst) x1 x6 (H14 Abst x5)) in (ex4_2_intro T T (\lambda (u: T).(\lambda 
(t: T).(pc3 c (THead (Flat Appl) w (THead (Bind Abst) u t)) x))) (\lambda (u: 
T).(\lambda (t: T).(ty3 g c v (THead (Bind Abst) u t)))) (\lambda (u: 
T).(\lambda (_: T).(ty3 g c w u))) (\lambda (u: T).(\lambda (t: T).(nf2 c 
(THead (Bind Abst) u t)))) x5 x6 (pc3_pr3_conf c (THead (Flat Appl) w (THead 
(Bind Abst) x0 x1)) x H0 (THead (Flat Appl) w (THead (Bind Abst) x5 x6)) 
(pr3_thin_dx c (THead (Bind Abst) x0 x1) (THead (Bind Abst) x5 x6) H16 w 
Appl)) (ty3_conv g c (THead (Bind Abst) x5 x6) x2 (ty3_sred_pr3 c (THead 
(Bind Abst) x0 x1) (THead (Bind Abst) x5 x6) H16 g x2 H4) v (THead (Bind 
Abst) x0 x1) H1 (pc3_pr3_r c (THead (Bind Abst) x0 x1) (THead (Bind Abst) x5 
x6) H16)) (ty3_conv g c x5 x3 (ty3_sred_pr3 c x0 x5 H13 g x3 H6) w x0 H2 
(pc3_pr3_r c x0 x5 H13)) H15)))))))) H11))))) H8)))))) H5))))) H3)))))))) 
(ty3_gen_appl g c w v x H))))))).
(* COMMENTS
Initial nodes: 1289
END *)

theorem ty3_inv_lref_nf2_pc3:
 \forall (g: G).(\forall (c: C).(\forall (u1: T).(\forall (i: nat).((ty3 g c 
(TLRef i) u1) \to ((nf2 c (TLRef i)) \to (\forall (u2: T).((nf2 c u2) \to 
((pc3 c u1 u2) \to (ex T (\lambda (u: T).(eq T u2 (lift (S i) O u))))))))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (u1: T).(\lambda (i: nat).(\lambda 
(H: (ty3 g c (TLRef i) u1)).(insert_eq T (TLRef i) (\lambda (t: T).(ty3 g c t 
u1)) (\lambda (t: T).((nf2 c t) \to (\forall (u2: T).((nf2 c u2) \to ((pc3 c 
u1 u2) \to (ex T (\lambda (u: T).(eq T u2 (lift (S i) O u))))))))) (\lambda 
(y: T).(\lambda (H0: (ty3 g c y u1)).(ty3_ind g (\lambda (c0: C).(\lambda (t: 
T).(\lambda (t0: T).((eq T t (TLRef i)) \to ((nf2 c0 t) \to (\forall (u2: 
T).((nf2 c0 u2) \to ((pc3 c0 t0 u2) \to (ex T (\lambda (u: T).(eq T u2 (lift 
(S i) O u)))))))))))) (\lambda (c0: C).(\lambda (t2: T).(\lambda (t: 
T).(\lambda (_: (ty3 g c0 t2 t)).(\lambda (_: (((eq T t2 (TLRef i)) \to ((nf2 
c0 t2) \to (\forall (u2: T).((nf2 c0 u2) \to ((pc3 c0 t u2) \to (ex T 
(\lambda (u: T).(eq T u2 (lift (S i) O u))))))))))).(\lambda (u: T).(\lambda 
(t1: T).(\lambda (H3: (ty3 g c0 u t1)).(\lambda (H4: (((eq T u (TLRef i)) \to 
((nf2 c0 u) \to (\forall (u2: T).((nf2 c0 u2) \to ((pc3 c0 t1 u2) \to (ex T 
(\lambda (u0: T).(eq T u2 (lift (S i) O u0))))))))))).(\lambda (H5: (pc3 c0 
t1 t2)).(\lambda (H6: (eq T u (TLRef i))).(\lambda (H7: (nf2 c0 u)).(\lambda 
(u2: T).(\lambda (H8: (nf2 c0 u2)).(\lambda (H9: (pc3 c0 t2 u2)).(let H10 
\def (eq_ind T u (\lambda (t0: T).(nf2 c0 t0)) H7 (TLRef i) H6) in (let H11 
\def (eq_ind T u (\lambda (t0: T).((eq T t0 (TLRef i)) \to ((nf2 c0 t0) \to 
(\forall (u3: T).((nf2 c0 u3) \to ((pc3 c0 t1 u3) \to (ex T (\lambda (u0: 
T).(eq T u3 (lift (S i) O u0)))))))))) H4 (TLRef i) H6) in (let H12 \def 
(eq_ind T u (\lambda (t0: T).(ty3 g c0 t0 t1)) H3 (TLRef i) H6) in (let H_y 
\def (H11 (refl_equal T (TLRef i)) H10 u2 H8) in (H_y (pc3_t t2 c0 t1 H5 u2 
H9))))))))))))))))))))) (\lambda (c0: C).(\lambda (m: nat).(\lambda (H1: (eq 
T (TSort m) (TLRef i))).(\lambda (_: (nf2 c0 (TSort m))).(\lambda (u2: 
T).(\lambda (_: (nf2 c0 u2)).(\lambda (_: (pc3 c0 (TSort (next g m)) 
u2)).(let H5 \def (eq_ind T (TSort m) (\lambda (ee: T).(match ee in T return 
(\lambda (_: T).Prop) with [(TSort _) \Rightarrow True | (TLRef _) 
\Rightarrow False | (THead _ _ _) \Rightarrow False])) I (TLRef i) H1) in 
(False_ind (ex T (\lambda (u: T).(eq T u2 (lift (S i) O u)))) H5))))))))) 
(\lambda (n: nat).(\lambda (c0: C).(\lambda (d: C).(\lambda (u: T).(\lambda 
(H1: (getl n c0 (CHead d (Bind Abbr) u))).(\lambda (t: T).(\lambda (_: (ty3 g 
d u t)).(\lambda (_: (((eq T u (TLRef i)) \to ((nf2 d u) \to (\forall (u2: 
T).((nf2 d u2) \to ((pc3 d t u2) \to (ex T (\lambda (u0: T).(eq T u2 (lift (S 
i) O u0))))))))))).(\lambda (H4: (eq T (TLRef n) (TLRef i))).(\lambda (H5: 
(nf2 c0 (TLRef n))).(\lambda (u2: T).(\lambda (_: (nf2 c0 u2)).(\lambda (H7: 
(pc3 c0 (lift (S n) O t) u2)).(let H8 \def (f_equal T nat (\lambda (e: 
T).(match e in T return (\lambda (_: T).nat) with [(TSort _) \Rightarrow n | 
(TLRef n0) \Rightarrow n0 | (THead _ _ _) \Rightarrow n])) (TLRef n) (TLRef 
i) H4) in (let H9 \def (eq_ind nat n (\lambda (n0: nat).(pc3 c0 (lift (S n0) 
O t) u2)) H7 i H8) in (let H10 \def (eq_ind nat n (\lambda (n0: nat).(nf2 c0 
(TLRef n0))) H5 i H8) in (let H11 \def (eq_ind nat n (\lambda (n0: nat).(getl 
n0 c0 (CHead d (Bind Abbr) u))) H1 i H8) in (nf2_gen_lref c0 d u i H11 H10 
(ex T (\lambda (u0: T).(eq T u2 (lift (S i) O u0)))))))))))))))))))))) 
(\lambda (n: nat).(\lambda (c0: C).(\lambda (d: C).(\lambda (u: T).(\lambda 
(H1: (getl n c0 (CHead d (Bind Abst) u))).(\lambda (t: T).(\lambda (_: (ty3 g 
d u t)).(\lambda (_: (((eq T u (TLRef i)) \to ((nf2 d u) \to (\forall (u2: 
T).((nf2 d u2) \to ((pc3 d t u2) \to (ex T (\lambda (u0: T).(eq T u2 (lift (S 
i) O u0))))))))))).(\lambda (H4: (eq T (TLRef n) (TLRef i))).(\lambda (H5: 
(nf2 c0 (TLRef n))).(\lambda (u2: T).(\lambda (H6: (nf2 c0 u2)).(\lambda (H7: 
(pc3 c0 (lift (S n) O u) u2)).(let H8 \def (f_equal T nat (\lambda (e: 
T).(match e in T return (\lambda (_: T).nat) with [(TSort _) \Rightarrow n | 
(TLRef n0) \Rightarrow n0 | (THead _ _ _) \Rightarrow n])) (TLRef n) (TLRef 
i) H4) in (let H9 \def (eq_ind nat n (\lambda (n0: nat).(pc3 c0 (lift (S n0) 
O u) u2)) H7 i H8) in (let H10 \def (eq_ind nat n (\lambda (n0: nat).(nf2 c0 
(TLRef n0))) H5 i H8) in (let H11 \def (eq_ind nat n (\lambda (n0: nat).(getl 
n0 c0 (CHead d (Bind Abst) u))) H1 i H8) in (let H_y \def (pc3_nf2_unfold c0 
(lift (S i) O u) u2 H9 H6) in (let H12 \def (pr3_gen_lift c0 u u2 (S i) O H_y 
d (getl_drop Abst c0 d u i H11)) in (ex2_ind T (\lambda (t2: T).(eq T u2 
(lift (S i) O t2))) (\lambda (t2: T).(pr3 d u t2)) (ex T (\lambda (u0: T).(eq 
T u2 (lift (S i) O u0)))) (\lambda (x: T).(\lambda (H13: (eq T u2 (lift (S i) 
O x))).(\lambda (_: (pr3 d u x)).(eq_ind_r T (lift (S i) O x) (\lambda (t0: 
T).(ex T (\lambda (u0: T).(eq T t0 (lift (S i) O u0))))) (ex_intro T (\lambda 
(u0: T).(eq T (lift (S i) O x) (lift (S i) O u0))) x (refl_equal T (lift (S 
i) O x))) u2 H13)))) H12)))))))))))))))))))) (\lambda (c0: C).(\lambda (u: 
T).(\lambda (t: T).(\lambda (_: (ty3 g c0 u t)).(\lambda (_: (((eq T u (TLRef 
i)) \to ((nf2 c0 u) \to (\forall (u2: T).((nf2 c0 u2) \to ((pc3 c0 t u2) \to 
(ex T (\lambda (u0: T).(eq T u2 (lift (S i) O u0))))))))))).(\lambda (b: 
B).(\lambda (t1: T).(\lambda (t2: T).(\lambda (_: (ty3 g (CHead c0 (Bind b) 
u) t1 t2)).(\lambda (_: (((eq T t1 (TLRef i)) \to ((nf2 (CHead c0 (Bind b) u) 
t1) \to (\forall (u2: T).((nf2 (CHead c0 (Bind b) u) u2) \to ((pc3 (CHead c0 
(Bind b) u) t2 u2) \to (ex T (\lambda (u0: T).(eq T u2 (lift (S i) O 
u0))))))))))).(\lambda (H5: (eq T (THead (Bind b) u t1) (TLRef i))).(\lambda 
(_: (nf2 c0 (THead (Bind b) u t1))).(\lambda (u2: T).(\lambda (_: (nf2 c0 
u2)).(\lambda (_: (pc3 c0 (THead (Bind b) u t2) u2)).(let H9 \def (eq_ind T 
(THead (Bind b) u t1) (\lambda (ee: T).(match ee in T return (\lambda (_: 
T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | 
(THead _ _ _) \Rightarrow True])) I (TLRef i) H5) in (False_ind (ex T 
(\lambda (u0: T).(eq T u2 (lift (S i) O u0)))) H9))))))))))))))))) (\lambda 
(c0: C).(\lambda (w: T).(\lambda (u: T).(\lambda (_: (ty3 g c0 w u)).(\lambda 
(_: (((eq T w (TLRef i)) \to ((nf2 c0 w) \to (\forall (u2: T).((nf2 c0 u2) 
\to ((pc3 c0 u u2) \to (ex T (\lambda (u0: T).(eq T u2 (lift (S i) O 
u0))))))))))).(\lambda (v: T).(\lambda (t: T).(\lambda (_: (ty3 g c0 v (THead 
(Bind Abst) u t))).(\lambda (_: (((eq T v (TLRef i)) \to ((nf2 c0 v) \to 
(\forall (u2: T).((nf2 c0 u2) \to ((pc3 c0 (THead (Bind Abst) u t) u2) \to 
(ex T (\lambda (u0: T).(eq T u2 (lift (S i) O u0))))))))))).(\lambda (H5: (eq 
T (THead (Flat Appl) w v) (TLRef i))).(\lambda (_: (nf2 c0 (THead (Flat Appl) 
w v))).(\lambda (u2: T).(\lambda (_: (nf2 c0 u2)).(\lambda (_: (pc3 c0 (THead 
(Flat Appl) w (THead (Bind Abst) u t)) u2)).(let H9 \def (eq_ind T (THead 
(Flat Appl) w v) (\lambda (ee: T).(match ee in T return (\lambda (_: T).Prop) 
with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | (THead _ _ 
_) \Rightarrow True])) I (TLRef i) H5) in (False_ind (ex T (\lambda (u0: 
T).(eq T u2 (lift (S i) O u0)))) H9)))))))))))))))) (\lambda (c0: C).(\lambda 
(t1: T).(\lambda (t2: T).(\lambda (_: (ty3 g c0 t1 t2)).(\lambda (_: (((eq T 
t1 (TLRef i)) \to ((nf2 c0 t1) \to (\forall (u2: T).((nf2 c0 u2) \to ((pc3 c0 
t2 u2) \to (ex T (\lambda (u: T).(eq T u2 (lift (S i) O u))))))))))).(\lambda 
(t0: T).(\lambda (_: (ty3 g c0 t2 t0)).(\lambda (_: (((eq T t2 (TLRef i)) \to 
((nf2 c0 t2) \to (\forall (u2: T).((nf2 c0 u2) \to ((pc3 c0 t0 u2) \to (ex T 
(\lambda (u: T).(eq T u2 (lift (S i) O u))))))))))).(\lambda (H5: (eq T 
(THead (Flat Cast) t2 t1) (TLRef i))).(\lambda (_: (nf2 c0 (THead (Flat Cast) 
t2 t1))).(\lambda (u2: T).(\lambda (_: (nf2 c0 u2)).(\lambda (_: (pc3 c0 
(THead (Flat Cast) t0 t2) u2)).(let H9 \def (eq_ind T (THead (Flat Cast) t2 
t1) (\lambda (ee: T).(match ee in T return (\lambda (_: T).Prop) with [(TSort 
_) \Rightarrow False | (TLRef _) \Rightarrow False | (THead _ _ _) 
\Rightarrow True])) I (TLRef i) H5) in (False_ind (ex T (\lambda (u: T).(eq T 
u2 (lift (S i) O u)))) H9))))))))))))))) c y u1 H0))) H))))).
(* COMMENTS
Initial nodes: 2175
END *)

theorem ty3_inv_lref_nf2:
 \forall (g: G).(\forall (c: C).(\forall (u: T).(\forall (i: nat).((ty3 g c 
(TLRef i) u) \to ((nf2 c (TLRef i)) \to ((nf2 c u) \to (ex T (\lambda (u0: 
T).(eq T u (lift (S i) O u0))))))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (u: T).(\lambda (i: nat).(\lambda 
(H: (ty3 g c (TLRef i) u)).(\lambda (H0: (nf2 c (TLRef i))).(\lambda (H1: 
(nf2 c u)).(ty3_inv_lref_nf2_pc3 g c u i H H0 u H1 (pc3_refl c u)))))))).
(* COMMENTS
Initial nodes: 57
END *)

theorem ty3_inv_appls_lref_nf2:
 \forall (g: G).(\forall (c: C).(\forall (vs: TList).(\forall (u1: 
T).(\forall (i: nat).((ty3 g c (THeads (Flat Appl) vs (TLRef i)) u1) \to 
((nf2 c (TLRef i)) \to ((nf2 c u1) \to (ex2 T (\lambda (u: T).(nf2 c (lift (S 
i) O u))) (\lambda (u: T).(pc3 c (THeads (Flat Appl) vs (lift (S i) O u)) 
u1))))))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (vs: TList).(TList_ind (\lambda (t: 
TList).(\forall (u1: T).(\forall (i: nat).((ty3 g c (THeads (Flat Appl) t 
(TLRef i)) u1) \to ((nf2 c (TLRef i)) \to ((nf2 c u1) \to (ex2 T (\lambda (u: 
T).(nf2 c (lift (S i) O u))) (\lambda (u: T).(pc3 c (THeads (Flat Appl) t 
(lift (S i) O u)) u1))))))))) (\lambda (u1: T).(\lambda (i: nat).(\lambda (H: 
(ty3 g c (TLRef i) u1)).(\lambda (H0: (nf2 c (TLRef i))).(\lambda (H1: (nf2 c 
u1)).(let H_x \def (ty3_inv_lref_nf2 g c u1 i H H0 H1) in (let H2 \def H_x in 
(ex_ind T (\lambda (u0: T).(eq T u1 (lift (S i) O u0))) (ex2 T (\lambda (u: 
T).(nf2 c (lift (S i) O u))) (\lambda (u: T).(pc3 c (lift (S i) O u) u1))) 
(\lambda (x: T).(\lambda (H3: (eq T u1 (lift (S i) O x))).(let H4 \def 
(eq_ind T u1 (\lambda (t: T).(nf2 c t)) H1 (lift (S i) O x) H3) in (eq_ind_r 
T (lift (S i) O x) (\lambda (t: T).(ex2 T (\lambda (u: T).(nf2 c (lift (S i) 
O u))) (\lambda (u: T).(pc3 c (lift (S i) O u) t)))) (ex_intro2 T (\lambda 
(u: T).(nf2 c (lift (S i) O u))) (\lambda (u: T).(pc3 c (lift (S i) O u) 
(lift (S i) O x))) x H4 (pc3_refl c (lift (S i) O x))) u1 H3)))) H2)))))))) 
(\lambda (t: T).(\lambda (t0: TList).(\lambda (H: ((\forall (u1: T).(\forall 
(i: nat).((ty3 g c (THeads (Flat Appl) t0 (TLRef i)) u1) \to ((nf2 c (TLRef 
i)) \to ((nf2 c u1) \to (ex2 T (\lambda (u: T).(nf2 c (lift (S i) O u))) 
(\lambda (u: T).(pc3 c (THeads (Flat Appl) t0 (lift (S i) O u)) 
u1)))))))))).(\lambda (u1: T).(\lambda (i: nat).(\lambda (H0: (ty3 g c (THead 
(Flat Appl) t (THeads (Flat Appl) t0 (TLRef i))) u1)).(\lambda (H1: (nf2 c 
(TLRef i))).(\lambda (_: (nf2 c u1)).(let H_x \def (ty3_gen_appl_nf2 g c t 
(THeads (Flat Appl) t0 (TLRef i)) u1 H0) in (let H3 \def H_x in (ex4_2_ind T 
T (\lambda (u: T).(\lambda (t1: T).(pc3 c (THead (Flat Appl) t (THead (Bind 
Abst) u t1)) u1))) (\lambda (u: T).(\lambda (t1: T).(ty3 g c (THeads (Flat 
Appl) t0 (TLRef i)) (THead (Bind Abst) u t1)))) (\lambda (u: T).(\lambda (_: 
T).(ty3 g c t u))) (\lambda (u: T).(\lambda (t1: T).(nf2 c (THead (Bind Abst) 
u t1)))) (ex2 T (\lambda (u: T).(nf2 c (lift (S i) O u))) (\lambda (u: 
T).(pc3 c (THead (Flat Appl) t (THeads (Flat Appl) t0 (lift (S i) O u))) 
u1))) (\lambda (x0: T).(\lambda (x1: T).(\lambda (H4: (pc3 c (THead (Flat 
Appl) t (THead (Bind Abst) x0 x1)) u1)).(\lambda (H5: (ty3 g c (THeads (Flat 
Appl) t0 (TLRef i)) (THead (Bind Abst) x0 x1))).(\lambda (_: (ty3 g c t 
x0)).(\lambda (H7: (nf2 c (THead (Bind Abst) x0 x1))).(let H8 \def 
(nf2_gen_abst c x0 x1 H7) in (land_ind (nf2 c x0) (nf2 (CHead c (Bind Abst) 
x0) x1) (ex2 T (\lambda (u: T).(nf2 c (lift (S i) O u))) (\lambda (u: T).(pc3 
c (THead (Flat Appl) t (THeads (Flat Appl) t0 (lift (S i) O u))) u1))) 
(\lambda (H9: (nf2 c x0)).(\lambda (H10: (nf2 (CHead c (Bind Abst) x0) 
x1)).(let H_y \def (H (THead (Bind Abst) x0 x1) i H5 H1) in (let H11 \def 
(H_y (nf2_abst_shift c x0 H9 x1 H10)) in (ex2_ind T (\lambda (u: T).(nf2 c 
(lift (S i) O u))) (\lambda (u: T).(pc3 c (THeads (Flat Appl) t0 (lift (S i) 
O u)) (THead (Bind Abst) x0 x1))) (ex2 T (\lambda (u: T).(nf2 c (lift (S i) O 
u))) (\lambda (u: T).(pc3 c (THead (Flat Appl) t (THeads (Flat Appl) t0 (lift 
(S i) O u))) u1))) (\lambda (x: T).(\lambda (H12: (nf2 c (lift (S i) O 
x))).(\lambda (H13: (pc3 c (THeads (Flat Appl) t0 (lift (S i) O x)) (THead 
(Bind Abst) x0 x1))).(ex_intro2 T (\lambda (u: T).(nf2 c (lift (S i) O u))) 
(\lambda (u: T).(pc3 c (THead (Flat Appl) t (THeads (Flat Appl) t0 (lift (S 
i) O u))) u1)) x H12 (pc3_t (THead (Flat Appl) t (THead (Bind Abst) x0 x1)) c 
(THead (Flat Appl) t (THeads (Flat Appl) t0 (lift (S i) O x))) (pc3_thin_dx c 
(THeads (Flat Appl) t0 (lift (S i) O x)) (THead (Bind Abst) x0 x1) H13 t 
Appl) u1 H4))))) H11))))) H8)))))))) H3))))))))))) vs))).
(* COMMENTS
Initial nodes: 1213
END *)

theorem ty3_inv_lref_lref_nf2:
 \forall (g: G).(\forall (c: C).(\forall (i: nat).(\forall (j: nat).((ty3 g c 
(TLRef i) (TLRef j)) \to ((nf2 c (TLRef i)) \to ((nf2 c (TLRef j)) \to (lt i 
j)))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (i: nat).(\lambda (j: nat).(\lambda 
(H: (ty3 g c (TLRef i) (TLRef j))).(\lambda (H0: (nf2 c (TLRef i))).(\lambda 
(H1: (nf2 c (TLRef j))).(let H_x \def (ty3_inv_lref_nf2 g c (TLRef j) i H H0 
H1) in (let H2 \def H_x in (ex_ind T (\lambda (u0: T).(eq T (TLRef j) (lift 
(S i) O u0))) (lt i j) (\lambda (x: T).(\lambda (H3: (eq T (TLRef j) (lift (S 
i) O x))).(let H_x0 \def (lift_gen_lref x O (S i) j H3) in (let H4 \def H_x0 
in (or_ind (land (lt j O) (eq T x (TLRef j))) (land (le (S i) j) (eq T x 
(TLRef (minus j (S i))))) (lt i j) (\lambda (H5: (land (lt j O) (eq T x 
(TLRef j)))).(land_ind (lt j O) (eq T x (TLRef j)) (lt i j) (\lambda (H6: (lt 
j O)).(\lambda (_: (eq T x (TLRef j))).(lt_x_O j H6 (lt i j)))) H5)) (\lambda 
(H5: (land (le (S i) j) (eq T x (TLRef (minus j (S i)))))).(land_ind (le (S 
i) j) (eq T x (TLRef (minus j (S i)))) (lt i j) (\lambda (H6: (le (S i) 
j)).(\lambda (_: (eq T x (TLRef (minus j (S i))))).H6)) H5)) H4))))) 
H2))))))))).
(* COMMENTS
Initial nodes: 337
END *)

