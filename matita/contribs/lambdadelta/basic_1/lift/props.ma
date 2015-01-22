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

include "Basic-1/lift/fwd.ma".

include "Basic-1/s/props.ma".

theorem thead_x_lift_y_y:
 \forall (k: K).(\forall (t: T).(\forall (v: T).(\forall (h: nat).(\forall 
(d: nat).((eq T (THead k v (lift h d t)) t) \to (\forall (P: Prop).P))))))
\def
 \lambda (k: K).(\lambda (t: T).(T_ind (\lambda (t0: T).(\forall (v: 
T).(\forall (h: nat).(\forall (d: nat).((eq T (THead k v (lift h d t0)) t0) 
\to (\forall (P: Prop).P)))))) (\lambda (n: nat).(\lambda (v: T).(\lambda (h: 
nat).(\lambda (d: nat).(\lambda (H: (eq T (THead k v (lift h d (TSort n))) 
(TSort n))).(\lambda (P: Prop).(let H0 \def (eq_ind T (THead k v (lift h d 
(TSort n))) (\lambda (ee: T).(match ee in T return (\lambda (_: T).Prop) with 
[(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | (THead _ _ _) 
\Rightarrow True])) I (TSort n) H) in (False_ind P H0)))))))) (\lambda (n: 
nat).(\lambda (v: T).(\lambda (h: nat).(\lambda (d: nat).(\lambda (H: (eq T 
(THead k v (lift h d (TLRef n))) (TLRef n))).(\lambda (P: Prop).(let H0 \def 
(eq_ind T (THead k v (lift h d (TLRef n))) (\lambda (ee: T).(match ee in T 
return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow False | (THead _ _ _) \Rightarrow True])) I (TLRef n) H) in 
(False_ind P H0)))))))) (\lambda (k0: K).(\lambda (t0: T).(\lambda (_: 
((\forall (v: T).(\forall (h: nat).(\forall (d: nat).((eq T (THead k v (lift 
h d t0)) t0) \to (\forall (P: Prop).P))))))).(\lambda (t1: T).(\lambda (H0: 
((\forall (v: T).(\forall (h: nat).(\forall (d: nat).((eq T (THead k v (lift 
h d t1)) t1) \to (\forall (P: Prop).P))))))).(\lambda (v: T).(\lambda (h: 
nat).(\lambda (d: nat).(\lambda (H1: (eq T (THead k v (lift h d (THead k0 t0 
t1))) (THead k0 t0 t1))).(\lambda (P: Prop).(let H2 \def (f_equal T K 
(\lambda (e: T).(match e in T return (\lambda (_: T).K) with [(TSort _) 
\Rightarrow k | (TLRef _) \Rightarrow k | (THead k1 _ _) \Rightarrow k1])) 
(THead k v (lift h d (THead k0 t0 t1))) (THead k0 t0 t1) H1) in ((let H3 \def 
(f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) with 
[(TSort _) \Rightarrow v | (TLRef _) \Rightarrow v | (THead _ t2 _) 
\Rightarrow t2])) (THead k v (lift h d (THead k0 t0 t1))) (THead k0 t0 t1) 
H1) in ((let H4 \def (f_equal T T (\lambda (e: T).(match e in T return 
(\lambda (_: T).T) with [(TSort _) \Rightarrow (THead k0 ((let rec lref_map 
(f: ((nat \to nat))) (d0: nat) (t2: T) on t2: T \def (match t2 with [(TSort 
n) \Rightarrow (TSort n) | (TLRef i) \Rightarrow (TLRef (match (blt i d0) 
with [true \Rightarrow i | false \Rightarrow (f i)])) | (THead k1 u t3) 
\Rightarrow (THead k1 (lref_map f d0 u) (lref_map f (s k1 d0) t3))]) in 
lref_map) (\lambda (x: nat).(plus x h)) d t0) ((let rec lref_map (f: ((nat 
\to nat))) (d0: nat) (t2: T) on t2: T \def (match t2 with [(TSort n) 
\Rightarrow (TSort n) | (TLRef i) \Rightarrow (TLRef (match (blt i d0) with 
[true \Rightarrow i | false \Rightarrow (f i)])) | (THead k1 u t3) 
\Rightarrow (THead k1 (lref_map f d0 u) (lref_map f (s k1 d0) t3))]) in 
lref_map) (\lambda (x: nat).(plus x h)) (s k0 d) t1)) | (TLRef _) \Rightarrow 
(THead k0 ((let rec lref_map (f: ((nat \to nat))) (d0: nat) (t2: T) on t2: T 
\def (match t2 with [(TSort n) \Rightarrow (TSort n) | (TLRef i) \Rightarrow 
(TLRef (match (blt i d0) with [true \Rightarrow i | false \Rightarrow (f 
i)])) | (THead k1 u t3) \Rightarrow (THead k1 (lref_map f d0 u) (lref_map f 
(s k1 d0) t3))]) in lref_map) (\lambda (x: nat).(plus x h)) d t0) ((let rec 
lref_map (f: ((nat \to nat))) (d0: nat) (t2: T) on t2: T \def (match t2 with 
[(TSort n) \Rightarrow (TSort n) | (TLRef i) \Rightarrow (TLRef (match (blt i 
d0) with [true \Rightarrow i | false \Rightarrow (f i)])) | (THead k1 u t3) 
\Rightarrow (THead k1 (lref_map f d0 u) (lref_map f (s k1 d0) t3))]) in 
lref_map) (\lambda (x: nat).(plus x h)) (s k0 d) t1)) | (THead _ _ t2) 
\Rightarrow t2])) (THead k v (lift h d (THead k0 t0 t1))) (THead k0 t0 t1) 
H1) in (\lambda (_: (eq T v t0)).(\lambda (H6: (eq K k k0)).(let H7 \def 
(eq_ind K k (\lambda (k1: K).(\forall (v0: T).(\forall (h0: nat).(\forall 
(d0: nat).((eq T (THead k1 v0 (lift h0 d0 t1)) t1) \to (\forall (P0: 
Prop).P0)))))) H0 k0 H6) in (let H8 \def (eq_ind T (lift h d (THead k0 t0 
t1)) (\lambda (t2: T).(eq T t2 t1)) H4 (THead k0 (lift h d t0) (lift h (s k0 
d) t1)) (lift_head k0 t0 t1 h d)) in (H7 (lift h d t0) h (s k0 d) H8 P)))))) 
H3)) H2)))))))))))) t)).
(* COMMENTS
Initial nodes: 887
END *)

theorem lift_r:
 \forall (t: T).(\forall (d: nat).(eq T (lift O d t) t))
\def
 \lambda (t: T).(T_ind (\lambda (t0: T).(\forall (d: nat).(eq T (lift O d t0) 
t0))) (\lambda (n: nat).(\lambda (_: nat).(refl_equal T (TSort n)))) (\lambda 
(n: nat).(\lambda (d: nat).(lt_le_e n d (eq T (lift O d (TLRef n)) (TLRef n)) 
(\lambda (H: (lt n d)).(eq_ind_r T (TLRef n) (\lambda (t0: T).(eq T t0 (TLRef 
n))) (refl_equal T (TLRef n)) (lift O d (TLRef n)) (lift_lref_lt n O d H))) 
(\lambda (H: (le d n)).(eq_ind_r T (TLRef (plus n O)) (\lambda (t0: T).(eq T 
t0 (TLRef n))) (f_equal nat T TLRef (plus n O) n (sym_eq nat n (plus n O) 
(plus_n_O n))) (lift O d (TLRef n)) (lift_lref_ge n O d H)))))) (\lambda (k: 
K).(\lambda (t0: T).(\lambda (H: ((\forall (d: nat).(eq T (lift O d t0) 
t0)))).(\lambda (t1: T).(\lambda (H0: ((\forall (d: nat).(eq T (lift O d t1) 
t1)))).(\lambda (d: nat).(eq_ind_r T (THead k (lift O d t0) (lift O (s k d) 
t1)) (\lambda (t2: T).(eq T t2 (THead k t0 t1))) (f_equal3 K T T T THead k k 
(lift O d t0) t0 (lift O (s k d) t1) t1 (refl_equal K k) (H d) (H0 (s k d))) 
(lift O d (THead k t0 t1)) (lift_head k t0 t1 O d)))))))) t).
(* COMMENTS
Initial nodes: 367
END *)

theorem lift_lref_gt:
 \forall (d: nat).(\forall (n: nat).((lt d n) \to (eq T (lift (S O) d (TLRef 
(pred n))) (TLRef n))))
\def
 \lambda (d: nat).(\lambda (n: nat).(\lambda (H: (lt d n)).(eq_ind_r T (TLRef 
(plus (pred n) (S O))) (\lambda (t: T).(eq T t (TLRef n))) (eq_ind nat (plus 
(S O) (pred n)) (\lambda (n0: nat).(eq T (TLRef n0) (TLRef n))) (eq_ind nat n 
(\lambda (n0: nat).(eq T (TLRef n0) (TLRef n))) (refl_equal T (TLRef n)) (S 
(pred n)) (S_pred n d H)) (plus (pred n) (S O)) (plus_sym (S O) (pred n))) 
(lift (S O) d (TLRef (pred n))) (lift_lref_ge (pred n) (S O) d (le_S_n d 
(pred n) (eq_ind nat n (\lambda (n0: nat).(le (S d) n0)) H (S (pred n)) 
(S_pred n d H))))))).
(* COMMENTS
Initial nodes: 193
END *)

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
(* COMMENTS
Initial nodes: 215
END *)

theorem lift_inj:
 \forall (x: T).(\forall (t: T).(\forall (h: nat).(\forall (d: nat).((eq T 
(lift h d x) (lift h d t)) \to (eq T x t)))))
\def
 \lambda (x: T).(T_ind (\lambda (t: T).(\forall (t0: T).(\forall (h: 
nat).(\forall (d: nat).((eq T (lift h d t) (lift h d t0)) \to (eq T t 
t0)))))) (\lambda (n: nat).(\lambda (t: T).(\lambda (h: nat).(\lambda (d: 
nat).(\lambda (H: (eq T (lift h d (TSort n)) (lift h d t))).(let H0 \def 
(eq_ind T (lift h d (TSort n)) (\lambda (t0: T).(eq T t0 (lift h d t))) H 
(TSort n) (lift_sort n h d)) in (sym_eq T t (TSort n) (lift_gen_sort h d n t 
H0)))))))) (\lambda (n: nat).(\lambda (t: T).(\lambda (h: nat).(\lambda (d: 
nat).(\lambda (H: (eq T (lift h d (TLRef n)) (lift h d t))).(lt_le_e n d (eq 
T (TLRef n) t) (\lambda (H0: (lt n d)).(let H1 \def (eq_ind T (lift h d 
(TLRef n)) (\lambda (t0: T).(eq T t0 (lift h d t))) H (TLRef n) (lift_lref_lt 
n h d H0)) in (sym_eq T t (TLRef n) (lift_gen_lref_lt h d n (lt_le_trans n d 
d H0 (le_n d)) t H1)))) (\lambda (H0: (le d n)).(let H1 \def (eq_ind T (lift 
h d (TLRef n)) (\lambda (t0: T).(eq T t0 (lift h d t))) H (TLRef (plus n h)) 
(lift_lref_ge n h d H0)) in (sym_eq T t (TLRef n) (lift_gen_lref_ge h d n H0 
t H1)))))))))) (\lambda (k: K).(K_ind (\lambda (k0: K).(\forall (t: 
T).(((\forall (t0: T).(\forall (h: nat).(\forall (d: nat).((eq T (lift h d t) 
(lift h d t0)) \to (eq T t t0)))))) \to (\forall (t0: T).(((\forall (t1: 
T).(\forall (h: nat).(\forall (d: nat).((eq T (lift h d t0) (lift h d t1)) 
\to (eq T t0 t1)))))) \to (\forall (t1: T).(\forall (h: nat).(\forall (d: 
nat).((eq T (lift h d (THead k0 t t0)) (lift h d t1)) \to (eq T (THead k0 t 
t0) t1)))))))))) (\lambda (b: B).(\lambda (t: T).(\lambda (H: ((\forall (t0: 
T).(\forall (h: nat).(\forall (d: nat).((eq T (lift h d t) (lift h d t0)) \to 
(eq T t t0))))))).(\lambda (t0: T).(\lambda (H0: ((\forall (t1: T).(\forall 
(h: nat).(\forall (d: nat).((eq T (lift h d t0) (lift h d t1)) \to (eq T t0 
t1))))))).(\lambda (t1: T).(\lambda (h: nat).(\lambda (d: nat).(\lambda (H1: 
(eq T (lift h d (THead (Bind b) t t0)) (lift h d t1))).(let H2 \def (eq_ind T 
(lift h d (THead (Bind b) t t0)) (\lambda (t2: T).(eq T t2 (lift h d t1))) H1 
(THead (Bind b) (lift h d t) (lift h (S d) t0)) (lift_bind b t t0 h d)) in 
(ex3_2_ind T T (\lambda (y: T).(\lambda (z: T).(eq T t1 (THead (Bind b) y 
z)))) (\lambda (y: T).(\lambda (_: T).(eq T (lift h d t) (lift h d y)))) 
(\lambda (_: T).(\lambda (z: T).(eq T (lift h (S d) t0) (lift h (S d) z)))) 
(eq T (THead (Bind b) t t0) t1) (\lambda (x0: T).(\lambda (x1: T).(\lambda 
(H3: (eq T t1 (THead (Bind b) x0 x1))).(\lambda (H4: (eq T (lift h d t) (lift 
h d x0))).(\lambda (H5: (eq T (lift h (S d) t0) (lift h (S d) x1))).(eq_ind_r 
T (THead (Bind b) x0 x1) (\lambda (t2: T).(eq T (THead (Bind b) t t0) t2)) 
(f_equal3 K T T T THead (Bind b) (Bind b) t x0 t0 x1 (refl_equal K (Bind b)) 
(H x0 h d H4) (H0 x1 h (S d) H5)) t1 H3)))))) (lift_gen_bind b (lift h d t) 
(lift h (S d) t0) t1 h d H2)))))))))))) (\lambda (f: F).(\lambda (t: 
T).(\lambda (H: ((\forall (t0: T).(\forall (h: nat).(\forall (d: nat).((eq T 
(lift h d t) (lift h d t0)) \to (eq T t t0))))))).(\lambda (t0: T).(\lambda 
(H0: ((\forall (t1: T).(\forall (h: nat).(\forall (d: nat).((eq T (lift h d 
t0) (lift h d t1)) \to (eq T t0 t1))))))).(\lambda (t1: T).(\lambda (h: 
nat).(\lambda (d: nat).(\lambda (H1: (eq T (lift h d (THead (Flat f) t t0)) 
(lift h d t1))).(let H2 \def (eq_ind T (lift h d (THead (Flat f) t t0)) 
(\lambda (t2: T).(eq T t2 (lift h d t1))) H1 (THead (Flat f) (lift h d t) 
(lift h d t0)) (lift_flat f t t0 h d)) in (ex3_2_ind T T (\lambda (y: 
T).(\lambda (z: T).(eq T t1 (THead (Flat f) y z)))) (\lambda (y: T).(\lambda 
(_: T).(eq T (lift h d t) (lift h d y)))) (\lambda (_: T).(\lambda (z: T).(eq 
T (lift h d t0) (lift h d z)))) (eq T (THead (Flat f) t t0) t1) (\lambda (x0: 
T).(\lambda (x1: T).(\lambda (H3: (eq T t1 (THead (Flat f) x0 x1))).(\lambda 
(H4: (eq T (lift h d t) (lift h d x0))).(\lambda (H5: (eq T (lift h d t0) 
(lift h d x1))).(eq_ind_r T (THead (Flat f) x0 x1) (\lambda (t2: T).(eq T 
(THead (Flat f) t t0) t2)) (f_equal3 K T T T THead (Flat f) (Flat f) t x0 t0 
x1 (refl_equal K (Flat f)) (H x0 h d H4) (H0 x1 h d H5)) t1 H3)))))) 
(lift_gen_flat f (lift h d t) (lift h d t0) t1 h d H2)))))))))))) k)) x).
(* COMMENTS
Initial nodes: 1391
END *)

theorem lift_gen_lift:
 \forall (t1: T).(\forall (x: T).(\forall (h1: nat).(\forall (h2: 
nat).(\forall (d1: nat).(\forall (d2: nat).((le d1 d2) \to ((eq T (lift h1 d1 
t1) (lift h2 (plus d2 h1) x)) \to (ex2 T (\lambda (t2: T).(eq T x (lift h1 d1 
t2))) (\lambda (t2: T).(eq T t1 (lift h2 d2 t2)))))))))))
\def
 \lambda (t1: T).(T_ind (\lambda (t: T).(\forall (x: T).(\forall (h1: 
nat).(\forall (h2: nat).(\forall (d1: nat).(\forall (d2: nat).((le d1 d2) \to 
((eq T (lift h1 d1 t) (lift h2 (plus d2 h1) x)) \to (ex2 T (\lambda (t2: 
T).(eq T x (lift h1 d1 t2))) (\lambda (t2: T).(eq T t (lift h2 d2 
t2)))))))))))) (\lambda (n: nat).(\lambda (x: T).(\lambda (h1: nat).(\lambda 
(h2: nat).(\lambda (d1: nat).(\lambda (d2: nat).(\lambda (_: (le d1 
d2)).(\lambda (H0: (eq T (lift h1 d1 (TSort n)) (lift h2 (plus d2 h1) 
x))).(let H1 \def (eq_ind T (lift h1 d1 (TSort n)) (\lambda (t: T).(eq T t 
(lift h2 (plus d2 h1) x))) H0 (TSort n) (lift_sort n h1 d1)) in (eq_ind_r T 
(TSort n) (\lambda (t: T).(ex2 T (\lambda (t2: T).(eq T t (lift h1 d1 t2))) 
(\lambda (t2: T).(eq T (TSort n) (lift h2 d2 t2))))) (ex_intro2 T (\lambda 
(t2: T).(eq T (TSort n) (lift h1 d1 t2))) (\lambda (t2: T).(eq T (TSort n) 
(lift h2 d2 t2))) (TSort n) (eq_ind_r T (TSort n) (\lambda (t: T).(eq T 
(TSort n) t)) (refl_equal T (TSort n)) (lift h1 d1 (TSort n)) (lift_sort n h1 
d1)) (eq_ind_r T (TSort n) (\lambda (t: T).(eq T (TSort n) t)) (refl_equal T 
(TSort n)) (lift h2 d2 (TSort n)) (lift_sort n h2 d2))) x (lift_gen_sort h2 
(plus d2 h1) n x H1))))))))))) (\lambda (n: nat).(\lambda (x: T).(\lambda 
(h1: nat).(\lambda (h2: nat).(\lambda (d1: nat).(\lambda (d2: nat).(\lambda 
(H: (le d1 d2)).(\lambda (H0: (eq T (lift h1 d1 (TLRef n)) (lift h2 (plus d2 
h1) x))).(lt_le_e n d1 (ex2 T (\lambda (t2: T).(eq T x (lift h1 d1 t2))) 
(\lambda (t2: T).(eq T (TLRef n) (lift h2 d2 t2)))) (\lambda (H1: (lt n 
d1)).(let H2 \def (eq_ind T (lift h1 d1 (TLRef n)) (\lambda (t: T).(eq T t 
(lift h2 (plus d2 h1) x))) H0 (TLRef n) (lift_lref_lt n h1 d1 H1)) in 
(eq_ind_r T (TLRef n) (\lambda (t: T).(ex2 T (\lambda (t2: T).(eq T t (lift 
h1 d1 t2))) (\lambda (t2: T).(eq T (TLRef n) (lift h2 d2 t2))))) (ex_intro2 T 
(\lambda (t2: T).(eq T (TLRef n) (lift h1 d1 t2))) (\lambda (t2: T).(eq T 
(TLRef n) (lift h2 d2 t2))) (TLRef n) (eq_ind_r T (TLRef n) (\lambda (t: 
T).(eq T (TLRef n) t)) (refl_equal T (TLRef n)) (lift h1 d1 (TLRef n)) 
(lift_lref_lt n h1 d1 H1)) (eq_ind_r T (TLRef n) (\lambda (t: T).(eq T (TLRef 
n) t)) (refl_equal T (TLRef n)) (lift h2 d2 (TLRef n)) (lift_lref_lt n h2 d2 
(lt_le_trans n d1 d2 H1 H)))) x (lift_gen_lref_lt h2 (plus d2 h1) n 
(lt_le_trans n d1 (plus d2 h1) H1 (le_plus_trans d1 d2 h1 H)) x H2)))) 
(\lambda (H1: (le d1 n)).(let H2 \def (eq_ind T (lift h1 d1 (TLRef n)) 
(\lambda (t: T).(eq T t (lift h2 (plus d2 h1) x))) H0 (TLRef (plus n h1)) 
(lift_lref_ge n h1 d1 H1)) in (lt_le_e n d2 (ex2 T (\lambda (t2: T).(eq T x 
(lift h1 d1 t2))) (\lambda (t2: T).(eq T (TLRef n) (lift h2 d2 t2)))) 
(\lambda (H3: (lt n d2)).(eq_ind_r T (TLRef (plus n h1)) (\lambda (t: T).(ex2 
T (\lambda (t2: T).(eq T t (lift h1 d1 t2))) (\lambda (t2: T).(eq T (TLRef n) 
(lift h2 d2 t2))))) (ex_intro2 T (\lambda (t2: T).(eq T (TLRef (plus n h1)) 
(lift h1 d1 t2))) (\lambda (t2: T).(eq T (TLRef n) (lift h2 d2 t2))) (TLRef 
n) (eq_ind_r T (TLRef (plus n h1)) (\lambda (t: T).(eq T (TLRef (plus n h1)) 
t)) (refl_equal T (TLRef (plus n h1))) (lift h1 d1 (TLRef n)) (lift_lref_ge n 
h1 d1 H1)) (eq_ind_r T (TLRef n) (\lambda (t: T).(eq T (TLRef n) t)) 
(refl_equal T (TLRef n)) (lift h2 d2 (TLRef n)) (lift_lref_lt n h2 d2 H3))) x 
(lift_gen_lref_lt h2 (plus d2 h1) (plus n h1) (lt_reg_r n d2 h1 H3) x H2))) 
(\lambda (H3: (le d2 n)).(lt_le_e n (plus d2 h2) (ex2 T (\lambda (t2: T).(eq 
T x (lift h1 d1 t2))) (\lambda (t2: T).(eq T (TLRef n) (lift h2 d2 t2)))) 
(\lambda (H4: (lt n (plus d2 h2))).(lift_gen_lref_false h2 (plus d2 h1) (plus 
n h1) (le_plus_plus d2 n h1 h1 H3 (le_n h1)) (eq_ind_r nat (plus (plus d2 h2) 
h1) (\lambda (n0: nat).(lt (plus n h1) n0)) (lt_reg_r n (plus d2 h2) h1 H4) 
(plus (plus d2 h1) h2) (plus_permute_2_in_3 d2 h1 h2)) x H2 (ex2 T (\lambda 
(t2: T).(eq T x (lift h1 d1 t2))) (\lambda (t2: T).(eq T (TLRef n) (lift h2 
d2 t2)))))) (\lambda (H4: (le (plus d2 h2) n)).(let H5 \def (eq_ind nat (plus 
n h1) (\lambda (n0: nat).(eq T (TLRef n0) (lift h2 (plus d2 h1) x))) H2 (plus 
(minus (plus n h1) h2) h2) (le_plus_minus_sym h2 (plus n h1) (le_plus_trans 
h2 n h1 (le_trans h2 (plus d2 h2) n (le_plus_r d2 h2) H4)))) in (eq_ind_r T 
(TLRef (minus (plus n h1) h2)) (\lambda (t: T).(ex2 T (\lambda (t2: T).(eq T 
t (lift h1 d1 t2))) (\lambda (t2: T).(eq T (TLRef n) (lift h2 d2 t2))))) 
(ex_intro2 T (\lambda (t2: T).(eq T (TLRef (minus (plus n h1) h2)) (lift h1 
d1 t2))) (\lambda (t2: T).(eq T (TLRef n) (lift h2 d2 t2))) (TLRef (minus n 
h2)) (eq_ind_r nat (plus (minus n h2) h1) (\lambda (n0: nat).(eq T (TLRef n0) 
(lift h1 d1 (TLRef (minus n h2))))) (eq_ind_r T (TLRef (plus (minus n h2) 
h1)) (\lambda (t: T).(eq T (TLRef (plus (minus n h2) h1)) t)) (refl_equal T 
(TLRef (plus (minus n h2) h1))) (lift h1 d1 (TLRef (minus n h2))) 
(lift_lref_ge (minus n h2) h1 d1 (le_trans d1 d2 (minus n h2) H (le_minus d2 
n h2 H4)))) (minus (plus n h1) h2) (le_minus_plus h2 n (le_trans h2 (plus d2 
h2) n (le_plus_r d2 h2) H4) h1)) (eq_ind_r nat (plus (minus n h2) h2) 
(\lambda (n0: nat).(eq T (TLRef n0) (lift h2 d2 (TLRef (minus n0 h2))))) 
(eq_ind_r T (TLRef (plus (minus (plus (minus n h2) h2) h2) h2)) (\lambda (t: 
T).(eq T (TLRef (plus (minus n h2) h2)) t)) (f_equal nat T TLRef (plus (minus 
n h2) h2) (plus (minus (plus (minus n h2) h2) h2) h2) (f_equal2 nat nat nat 
plus (minus n h2) (minus (plus (minus n h2) h2) h2) h2 h2 (sym_eq nat (minus 
(plus (minus n h2) h2) h2) (minus n h2) (minus_plus_r (minus n h2) h2)) 
(refl_equal nat h2))) (lift h2 d2 (TLRef (minus (plus (minus n h2) h2) h2))) 
(lift_lref_ge (minus (plus (minus n h2) h2) h2) h2 d2 (le_minus d2 (plus 
(minus n h2) h2) h2 (le_plus_plus d2 (minus n h2) h2 h2 (le_minus d2 n h2 H4) 
(le_n h2))))) n (le_plus_minus_sym h2 n (le_trans h2 (plus d2 h2) n 
(le_plus_r d2 h2) H4)))) x (lift_gen_lref_ge h2 (plus d2 h1) (minus (plus n 
h1) h2) (arith0 h2 d2 n H4 h1) x H5)))))))))))))))))) (\lambda (k: 
K).(\lambda (t: T).(\lambda (H: ((\forall (x: T).(\forall (h1: nat).(\forall 
(h2: nat).(\forall (d1: nat).(\forall (d2: nat).((le d1 d2) \to ((eq T (lift 
h1 d1 t) (lift h2 (plus d2 h1) x)) \to (ex2 T (\lambda (t2: T).(eq T x (lift 
h1 d1 t2))) (\lambda (t2: T).(eq T t (lift h2 d2 t2))))))))))))).(\lambda 
(t0: T).(\lambda (H0: ((\forall (x: T).(\forall (h1: nat).(\forall (h2: 
nat).(\forall (d1: nat).(\forall (d2: nat).((le d1 d2) \to ((eq T (lift h1 d1 
t0) (lift h2 (plus d2 h1) x)) \to (ex2 T (\lambda (t2: T).(eq T x (lift h1 d1 
t2))) (\lambda (t2: T).(eq T t0 (lift h2 d2 t2))))))))))))).(\lambda (x: 
T).(\lambda (h1: nat).(\lambda (h2: nat).(\lambda (d1: nat).(\lambda (d2: 
nat).(\lambda (H1: (le d1 d2)).(\lambda (H2: (eq T (lift h1 d1 (THead k t 
t0)) (lift h2 (plus d2 h1) x))).(K_ind (\lambda (k0: K).((eq T (lift h1 d1 
(THead k0 t t0)) (lift h2 (plus d2 h1) x)) \to (ex2 T (\lambda (t2: T).(eq T 
x (lift h1 d1 t2))) (\lambda (t2: T).(eq T (THead k0 t t0) (lift h2 d2 
t2)))))) (\lambda (b: B).(\lambda (H3: (eq T (lift h1 d1 (THead (Bind b) t 
t0)) (lift h2 (plus d2 h1) x))).(let H4 \def (eq_ind T (lift h1 d1 (THead 
(Bind b) t t0)) (\lambda (t2: T).(eq T t2 (lift h2 (plus d2 h1) x))) H3 
(THead (Bind b) (lift h1 d1 t) (lift h1 (S d1) t0)) (lift_bind b t t0 h1 d1)) 
in (ex3_2_ind T T (\lambda (y: T).(\lambda (z: T).(eq T x (THead (Bind b) y 
z)))) (\lambda (y: T).(\lambda (_: T).(eq T (lift h1 d1 t) (lift h2 (plus d2 
h1) y)))) (\lambda (_: T).(\lambda (z: T).(eq T (lift h1 (S d1) t0) (lift h2 
(S (plus d2 h1)) z)))) (ex2 T (\lambda (t2: T).(eq T x (lift h1 d1 t2))) 
(\lambda (t2: T).(eq T (THead (Bind b) t t0) (lift h2 d2 t2)))) (\lambda (x0: 
T).(\lambda (x1: T).(\lambda (H5: (eq T x (THead (Bind b) x0 x1))).(\lambda 
(H6: (eq T (lift h1 d1 t) (lift h2 (plus d2 h1) x0))).(\lambda (H7: (eq T 
(lift h1 (S d1) t0) (lift h2 (S (plus d2 h1)) x1))).(eq_ind_r T (THead (Bind 
b) x0 x1) (\lambda (t2: T).(ex2 T (\lambda (t3: T).(eq T t2 (lift h1 d1 t3))) 
(\lambda (t3: T).(eq T (THead (Bind b) t t0) (lift h2 d2 t3))))) (ex2_ind T 
(\lambda (t2: T).(eq T x0 (lift h1 d1 t2))) (\lambda (t2: T).(eq T t (lift h2 
d2 t2))) (ex2 T (\lambda (t2: T).(eq T (THead (Bind b) x0 x1) (lift h1 d1 
t2))) (\lambda (t2: T).(eq T (THead (Bind b) t t0) (lift h2 d2 t2)))) 
(\lambda (x2: T).(\lambda (H8: (eq T x0 (lift h1 d1 x2))).(\lambda (H9: (eq T 
t (lift h2 d2 x2))).(eq_ind_r T (lift h1 d1 x2) (\lambda (t2: T).(ex2 T 
(\lambda (t3: T).(eq T (THead (Bind b) t2 x1) (lift h1 d1 t3))) (\lambda (t3: 
T).(eq T (THead (Bind b) t t0) (lift h2 d2 t3))))) (eq_ind_r T (lift h2 d2 
x2) (\lambda (t2: T).(ex2 T (\lambda (t3: T).(eq T (THead (Bind b) (lift h1 
d1 x2) x1) (lift h1 d1 t3))) (\lambda (t3: T).(eq T (THead (Bind b) t2 t0) 
(lift h2 d2 t3))))) (let H10 \def (refl_equal nat (plus (S d2) h1)) in (let 
H11 \def (eq_ind nat (S (plus d2 h1)) (\lambda (n: nat).(eq T (lift h1 (S d1) 
t0) (lift h2 n x1))) H7 (plus (S d2) h1) H10) in (ex2_ind T (\lambda (t2: 
T).(eq T x1 (lift h1 (S d1) t2))) (\lambda (t2: T).(eq T t0 (lift h2 (S d2) 
t2))) (ex2 T (\lambda (t2: T).(eq T (THead (Bind b) (lift h1 d1 x2) x1) (lift 
h1 d1 t2))) (\lambda (t2: T).(eq T (THead (Bind b) (lift h2 d2 x2) t0) (lift 
h2 d2 t2)))) (\lambda (x3: T).(\lambda (H12: (eq T x1 (lift h1 (S d1) 
x3))).(\lambda (H13: (eq T t0 (lift h2 (S d2) x3))).(eq_ind_r T (lift h1 (S 
d1) x3) (\lambda (t2: T).(ex2 T (\lambda (t3: T).(eq T (THead (Bind b) (lift 
h1 d1 x2) t2) (lift h1 d1 t3))) (\lambda (t3: T).(eq T (THead (Bind b) (lift 
h2 d2 x2) t0) (lift h2 d2 t3))))) (eq_ind_r T (lift h2 (S d2) x3) (\lambda 
(t2: T).(ex2 T (\lambda (t3: T).(eq T (THead (Bind b) (lift h1 d1 x2) (lift 
h1 (S d1) x3)) (lift h1 d1 t3))) (\lambda (t3: T).(eq T (THead (Bind b) (lift 
h2 d2 x2) t2) (lift h2 d2 t3))))) (ex_intro2 T (\lambda (t2: T).(eq T (THead 
(Bind b) (lift h1 d1 x2) (lift h1 (S d1) x3)) (lift h1 d1 t2))) (\lambda (t2: 
T).(eq T (THead (Bind b) (lift h2 d2 x2) (lift h2 (S d2) x3)) (lift h2 d2 
t2))) (THead (Bind b) x2 x3) (eq_ind_r T (THead (Bind b) (lift h1 d1 x2) 
(lift h1 (S d1) x3)) (\lambda (t2: T).(eq T (THead (Bind b) (lift h1 d1 x2) 
(lift h1 (S d1) x3)) t2)) (refl_equal T (THead (Bind b) (lift h1 d1 x2) (lift 
h1 (S d1) x3))) (lift h1 d1 (THead (Bind b) x2 x3)) (lift_bind b x2 x3 h1 
d1)) (eq_ind_r T (THead (Bind b) (lift h2 d2 x2) (lift h2 (S d2) x3)) 
(\lambda (t2: T).(eq T (THead (Bind b) (lift h2 d2 x2) (lift h2 (S d2) x3)) 
t2)) (refl_equal T (THead (Bind b) (lift h2 d2 x2) (lift h2 (S d2) x3))) 
(lift h2 d2 (THead (Bind b) x2 x3)) (lift_bind b x2 x3 h2 d2))) t0 H13) x1 
H12)))) (H0 x1 h1 h2 (S d1) (S d2) (le_n_S d1 d2 H1) H11)))) t H9) x0 H8)))) 
(H x0 h1 h2 d1 d2 H1 H6)) x H5)))))) (lift_gen_bind b (lift h1 d1 t) (lift h1 
(S d1) t0) x h2 (plus d2 h1) H4))))) (\lambda (f: F).(\lambda (H3: (eq T 
(lift h1 d1 (THead (Flat f) t t0)) (lift h2 (plus d2 h1) x))).(let H4 \def 
(eq_ind T (lift h1 d1 (THead (Flat f) t t0)) (\lambda (t2: T).(eq T t2 (lift 
h2 (plus d2 h1) x))) H3 (THead (Flat f) (lift h1 d1 t) (lift h1 d1 t0)) 
(lift_flat f t t0 h1 d1)) in (ex3_2_ind T T (\lambda (y: T).(\lambda (z: 
T).(eq T x (THead (Flat f) y z)))) (\lambda (y: T).(\lambda (_: T).(eq T 
(lift h1 d1 t) (lift h2 (plus d2 h1) y)))) (\lambda (_: T).(\lambda (z: 
T).(eq T (lift h1 d1 t0) (lift h2 (plus d2 h1) z)))) (ex2 T (\lambda (t2: 
T).(eq T x (lift h1 d1 t2))) (\lambda (t2: T).(eq T (THead (Flat f) t t0) 
(lift h2 d2 t2)))) (\lambda (x0: T).(\lambda (x1: T).(\lambda (H5: (eq T x 
(THead (Flat f) x0 x1))).(\lambda (H6: (eq T (lift h1 d1 t) (lift h2 (plus d2 
h1) x0))).(\lambda (H7: (eq T (lift h1 d1 t0) (lift h2 (plus d2 h1) 
x1))).(eq_ind_r T (THead (Flat f) x0 x1) (\lambda (t2: T).(ex2 T (\lambda 
(t3: T).(eq T t2 (lift h1 d1 t3))) (\lambda (t3: T).(eq T (THead (Flat f) t 
t0) (lift h2 d2 t3))))) (ex2_ind T (\lambda (t2: T).(eq T x0 (lift h1 d1 
t2))) (\lambda (t2: T).(eq T t (lift h2 d2 t2))) (ex2 T (\lambda (t2: T).(eq 
T (THead (Flat f) x0 x1) (lift h1 d1 t2))) (\lambda (t2: T).(eq T (THead 
(Flat f) t t0) (lift h2 d2 t2)))) (\lambda (x2: T).(\lambda (H8: (eq T x0 
(lift h1 d1 x2))).(\lambda (H9: (eq T t (lift h2 d2 x2))).(eq_ind_r T (lift 
h1 d1 x2) (\lambda (t2: T).(ex2 T (\lambda (t3: T).(eq T (THead (Flat f) t2 
x1) (lift h1 d1 t3))) (\lambda (t3: T).(eq T (THead (Flat f) t t0) (lift h2 
d2 t3))))) (eq_ind_r T (lift h2 d2 x2) (\lambda (t2: T).(ex2 T (\lambda (t3: 
T).(eq T (THead (Flat f) (lift h1 d1 x2) x1) (lift h1 d1 t3))) (\lambda (t3: 
T).(eq T (THead (Flat f) t2 t0) (lift h2 d2 t3))))) (ex2_ind T (\lambda (t2: 
T).(eq T x1 (lift h1 d1 t2))) (\lambda (t2: T).(eq T t0 (lift h2 d2 t2))) 
(ex2 T (\lambda (t2: T).(eq T (THead (Flat f) (lift h1 d1 x2) x1) (lift h1 d1 
t2))) (\lambda (t2: T).(eq T (THead (Flat f) (lift h2 d2 x2) t0) (lift h2 d2 
t2)))) (\lambda (x3: T).(\lambda (H10: (eq T x1 (lift h1 d1 x3))).(\lambda 
(H11: (eq T t0 (lift h2 d2 x3))).(eq_ind_r T (lift h1 d1 x3) (\lambda (t2: 
T).(ex2 T (\lambda (t3: T).(eq T (THead (Flat f) (lift h1 d1 x2) t2) (lift h1 
d1 t3))) (\lambda (t3: T).(eq T (THead (Flat f) (lift h2 d2 x2) t0) (lift h2 
d2 t3))))) (eq_ind_r T (lift h2 d2 x3) (\lambda (t2: T).(ex2 T (\lambda (t3: 
T).(eq T (THead (Flat f) (lift h1 d1 x2) (lift h1 d1 x3)) (lift h1 d1 t3))) 
(\lambda (t3: T).(eq T (THead (Flat f) (lift h2 d2 x2) t2) (lift h2 d2 
t3))))) (ex_intro2 T (\lambda (t2: T).(eq T (THead (Flat f) (lift h1 d1 x2) 
(lift h1 d1 x3)) (lift h1 d1 t2))) (\lambda (t2: T).(eq T (THead (Flat f) 
(lift h2 d2 x2) (lift h2 d2 x3)) (lift h2 d2 t2))) (THead (Flat f) x2 x3) 
(eq_ind_r T (THead (Flat f) (lift h1 d1 x2) (lift h1 d1 x3)) (\lambda (t2: 
T).(eq T (THead (Flat f) (lift h1 d1 x2) (lift h1 d1 x3)) t2)) (refl_equal T 
(THead (Flat f) (lift h1 d1 x2) (lift h1 d1 x3))) (lift h1 d1 (THead (Flat f) 
x2 x3)) (lift_flat f x2 x3 h1 d1)) (eq_ind_r T (THead (Flat f) (lift h2 d2 
x2) (lift h2 d2 x3)) (\lambda (t2: T).(eq T (THead (Flat f) (lift h2 d2 x2) 
(lift h2 d2 x3)) t2)) (refl_equal T (THead (Flat f) (lift h2 d2 x2) (lift h2 
d2 x3))) (lift h2 d2 (THead (Flat f) x2 x3)) (lift_flat f x2 x3 h2 d2))) t0 
H11) x1 H10)))) (H0 x1 h1 h2 d1 d2 H1 H7)) t H9) x0 H8)))) (H x0 h1 h2 d1 d2 
H1 H6)) x H5)))))) (lift_gen_flat f (lift h1 d1 t) (lift h1 d1 t0) x h2 (plus 
d2 h1) H4))))) k H2))))))))))))) t1).
(* COMMENTS
Initial nodes: 5037
END *)

theorem lifts_inj:
 \forall (xs: TList).(\forall (ts: TList).(\forall (h: nat).(\forall (d: 
nat).((eq TList (lifts h d xs) (lifts h d ts)) \to (eq TList xs ts)))))
\def
 \lambda (xs: TList).(TList_ind (\lambda (t: TList).(\forall (ts: 
TList).(\forall (h: nat).(\forall (d: nat).((eq TList (lifts h d t) (lifts h 
d ts)) \to (eq TList t ts)))))) (\lambda (ts: TList).(TList_ind (\lambda (t: 
TList).(\forall (h: nat).(\forall (d: nat).((eq TList (lifts h d TNil) (lifts 
h d t)) \to (eq TList TNil t))))) (\lambda (_: nat).(\lambda (_: 
nat).(\lambda (_: (eq TList TNil TNil)).(refl_equal TList TNil)))) (\lambda 
(t: T).(\lambda (t0: TList).(\lambda (_: ((\forall (h: nat).(\forall (d: 
nat).((eq TList TNil (lifts h d t0)) \to (eq TList TNil t0)))))).(\lambda (h: 
nat).(\lambda (d: nat).(\lambda (H0: (eq TList TNil (TCons (lift h d t) 
(lifts h d t0)))).(let H1 \def (eq_ind TList TNil (\lambda (ee: TList).(match 
ee in TList return (\lambda (_: TList).Prop) with [TNil \Rightarrow True | 
(TCons _ _) \Rightarrow False])) I (TCons (lift h d t) (lifts h d t0)) H0) in 
(False_ind (eq TList TNil (TCons t t0)) H1)))))))) ts)) (\lambda (t: 
T).(\lambda (t0: TList).(\lambda (H: ((\forall (ts: TList).(\forall (h: 
nat).(\forall (d: nat).((eq TList (lifts h d t0) (lifts h d ts)) \to (eq 
TList t0 ts))))))).(\lambda (ts: TList).(TList_ind (\lambda (t1: 
TList).(\forall (h: nat).(\forall (d: nat).((eq TList (lifts h d (TCons t 
t0)) (lifts h d t1)) \to (eq TList (TCons t t0) t1))))) (\lambda (h: 
nat).(\lambda (d: nat).(\lambda (H0: (eq TList (TCons (lift h d t) (lifts h d 
t0)) TNil)).(let H1 \def (eq_ind TList (TCons (lift h d t) (lifts h d t0)) 
(\lambda (ee: TList).(match ee in TList return (\lambda (_: TList).Prop) with 
[TNil \Rightarrow False | (TCons _ _) \Rightarrow True])) I TNil H0) in 
(False_ind (eq TList (TCons t t0) TNil) H1))))) (\lambda (t1: T).(\lambda 
(t2: TList).(\lambda (_: ((\forall (h: nat).(\forall (d: nat).((eq TList 
(TCons (lift h d t) (lifts h d t0)) (lifts h d t2)) \to (eq TList (TCons t 
t0) t2)))))).(\lambda (h: nat).(\lambda (d: nat).(\lambda (H1: (eq TList 
(TCons (lift h d t) (lifts h d t0)) (TCons (lift h d t1) (lifts h d 
t2)))).(let H2 \def (f_equal TList T (\lambda (e: TList).(match e in TList 
return (\lambda (_: TList).T) with [TNil \Rightarrow ((let rec lref_map (f: 
((nat \to nat))) (d0: nat) (t3: T) on t3: T \def (match t3 with [(TSort n) 
\Rightarrow (TSort n) | (TLRef i) \Rightarrow (TLRef (match (blt i d0) with 
[true \Rightarrow i | false \Rightarrow (f i)])) | (THead k u t4) \Rightarrow 
(THead k (lref_map f d0 u) (lref_map f (s k d0) t4))]) in lref_map) (\lambda 
(x: nat).(plus x h)) d t) | (TCons t3 _) \Rightarrow t3])) (TCons (lift h d 
t) (lifts h d t0)) (TCons (lift h d t1) (lifts h d t2)) H1) in ((let H3 \def 
(f_equal TList TList (\lambda (e: TList).(match e in TList return (\lambda 
(_: TList).TList) with [TNil \Rightarrow ((let rec lifts (h0: nat) (d0: nat) 
(ts0: TList) on ts0: TList \def (match ts0 with [TNil \Rightarrow TNil | 
(TCons t3 ts1) \Rightarrow (TCons (lift h0 d0 t3) (lifts h0 d0 ts1))]) in 
lifts) h d t0) | (TCons _ t3) \Rightarrow t3])) (TCons (lift h d t) (lifts h 
d t0)) (TCons (lift h d t1) (lifts h d t2)) H1) in (\lambda (H4: (eq T (lift 
h d t) (lift h d t1))).(eq_ind T t (\lambda (t3: T).(eq TList (TCons t t0) 
(TCons t3 t2))) (f_equal2 T TList TList TCons t t t0 t2 (refl_equal T t) (H 
t2 h d H3)) t1 (lift_inj t t1 h d H4)))) H2)))))))) ts))))) xs).
(* COMMENTS
Initial nodes: 772
END *)

theorem lift_free:
 \forall (t: T).(\forall (h: nat).(\forall (k: nat).(\forall (d: 
nat).(\forall (e: nat).((le e (plus d h)) \to ((le d e) \to (eq T (lift k e 
(lift h d t)) (lift (plus k h) d t))))))))
\def
 \lambda (t: T).(T_ind (\lambda (t0: T).(\forall (h: nat).(\forall (k: 
nat).(\forall (d: nat).(\forall (e: nat).((le e (plus d h)) \to ((le d e) \to 
(eq T (lift k e (lift h d t0)) (lift (plus k h) d t0))))))))) (\lambda (n: 
nat).(\lambda (h: nat).(\lambda (k: nat).(\lambda (d: nat).(\lambda (e: 
nat).(\lambda (_: (le e (plus d h))).(\lambda (_: (le d e)).(eq_ind_r T 
(TSort n) (\lambda (t0: T).(eq T (lift k e t0) (lift (plus k h) d (TSort 
n)))) (eq_ind_r T (TSort n) (\lambda (t0: T).(eq T t0 (lift (plus k h) d 
(TSort n)))) (eq_ind_r T (TSort n) (\lambda (t0: T).(eq T (TSort n) t0)) 
(refl_equal T (TSort n)) (lift (plus k h) d (TSort n)) (lift_sort n (plus k 
h) d)) (lift k e (TSort n)) (lift_sort n k e)) (lift h d (TSort n)) 
(lift_sort n h d))))))))) (\lambda (n: nat).(\lambda (h: nat).(\lambda (k: 
nat).(\lambda (d: nat).(\lambda (e: nat).(\lambda (H: (le e (plus d 
h))).(\lambda (H0: (le d e)).(lt_le_e n d (eq T (lift k e (lift h d (TLRef 
n))) (lift (plus k h) d (TLRef n))) (\lambda (H1: (lt n d)).(eq_ind_r T 
(TLRef n) (\lambda (t0: T).(eq T (lift k e t0) (lift (plus k h) d (TLRef 
n)))) (eq_ind_r T (TLRef n) (\lambda (t0: T).(eq T t0 (lift (plus k h) d 
(TLRef n)))) (eq_ind_r T (TLRef n) (\lambda (t0: T).(eq T (TLRef n) t0)) 
(refl_equal T (TLRef n)) (lift (plus k h) d (TLRef n)) (lift_lref_lt n (plus 
k h) d H1)) (lift k e (TLRef n)) (lift_lref_lt n k e (lt_le_trans n d e H1 
H0))) (lift h d (TLRef n)) (lift_lref_lt n h d H1))) (\lambda (H1: (le d 
n)).(eq_ind_r T (TLRef (plus n h)) (\lambda (t0: T).(eq T (lift k e t0) (lift 
(plus k h) d (TLRef n)))) (eq_ind_r T (TLRef (plus (plus n h) k)) (\lambda 
(t0: T).(eq T t0 (lift (plus k h) d (TLRef n)))) (eq_ind_r T (TLRef (plus n 
(plus k h))) (\lambda (t0: T).(eq T (TLRef (plus (plus n h) k)) t0)) (f_equal 
nat T TLRef (plus (plus n h) k) (plus n (plus k h)) 
(plus_permute_2_in_3_assoc n h k)) (lift (plus k h) d (TLRef n)) 
(lift_lref_ge n (plus k h) d H1)) (lift k e (TLRef (plus n h))) (lift_lref_ge 
(plus n h) k e (le_trans e (plus d h) (plus n h) H (le_plus_plus d n h h H1 
(le_n h))))) (lift h d (TLRef n)) (lift_lref_ge n h d H1))))))))))) (\lambda 
(k: K).(\lambda (t0: T).(\lambda (H: ((\forall (h: nat).(\forall (k0: 
nat).(\forall (d: nat).(\forall (e: nat).((le e (plus d h)) \to ((le d e) \to 
(eq T (lift k0 e (lift h d t0)) (lift (plus k0 h) d t0)))))))))).(\lambda 
(t1: T).(\lambda (H0: ((\forall (h: nat).(\forall (k0: nat).(\forall (d: 
nat).(\forall (e: nat).((le e (plus d h)) \to ((le d e) \to (eq T (lift k0 e 
(lift h d t1)) (lift (plus k0 h) d t1)))))))))).(\lambda (h: nat).(\lambda 
(k0: nat).(\lambda (d: nat).(\lambda (e: nat).(\lambda (H1: (le e (plus d 
h))).(\lambda (H2: (le d e)).(eq_ind_r T (THead k (lift h d t0) (lift h (s k 
d) t1)) (\lambda (t2: T).(eq T (lift k0 e t2) (lift (plus k0 h) d (THead k t0 
t1)))) (eq_ind_r T (THead k (lift k0 e (lift h d t0)) (lift k0 (s k e) (lift 
h (s k d) t1))) (\lambda (t2: T).(eq T t2 (lift (plus k0 h) d (THead k t0 
t1)))) (eq_ind_r T (THead k (lift (plus k0 h) d t0) (lift (plus k0 h) (s k d) 
t1)) (\lambda (t2: T).(eq T (THead k (lift k0 e (lift h d t0)) (lift k0 (s k 
e) (lift h (s k d) t1))) t2)) (f_equal3 K T T T THead k k (lift k0 e (lift h 
d t0)) (lift (plus k0 h) d t0) (lift k0 (s k e) (lift h (s k d) t1)) (lift 
(plus k0 h) (s k d) t1) (refl_equal K k) (H h k0 d e H1 H2) (H0 h k0 (s k d) 
(s k e) (eq_ind nat (s k (plus d h)) (\lambda (n: nat).(le (s k e) n)) (s_le 
k e (plus d h) H1) (plus (s k d) h) (s_plus k d h)) (s_le k d e H2))) (lift 
(plus k0 h) d (THead k t0 t1)) (lift_head k t0 t1 (plus k0 h) d)) (lift k0 e 
(THead k (lift h d t0) (lift h (s k d) t1))) (lift_head k (lift h d t0) (lift 
h (s k d) t1) k0 e)) (lift h d (THead k t0 t1)) (lift_head k t0 t1 h 
d))))))))))))) t).
(* COMMENTS
Initial nodes: 1407
END *)

theorem lift_d:
 \forall (t: T).(\forall (h: nat).(\forall (k: nat).(\forall (d: 
nat).(\forall (e: nat).((le e d) \to (eq T (lift h (plus k d) (lift k e t)) 
(lift k e (lift h d t))))))))
\def
 \lambda (t: T).(T_ind (\lambda (t0: T).(\forall (h: nat).(\forall (k: 
nat).(\forall (d: nat).(\forall (e: nat).((le e d) \to (eq T (lift h (plus k 
d) (lift k e t0)) (lift k e (lift h d t0))))))))) (\lambda (n: nat).(\lambda 
(h: nat).(\lambda (k: nat).(\lambda (d: nat).(\lambda (e: nat).(\lambda (_: 
(le e d)).(eq_ind_r T (TSort n) (\lambda (t0: T).(eq T (lift h (plus k d) t0) 
(lift k e (lift h d (TSort n))))) (eq_ind_r T (TSort n) (\lambda (t0: T).(eq 
T t0 (lift k e (lift h d (TSort n))))) (eq_ind_r T (TSort n) (\lambda (t0: 
T).(eq T (TSort n) (lift k e t0))) (eq_ind_r T (TSort n) (\lambda (t0: T).(eq 
T (TSort n) t0)) (refl_equal T (TSort n)) (lift k e (TSort n)) (lift_sort n k 
e)) (lift h d (TSort n)) (lift_sort n h d)) (lift h (plus k d) (TSort n)) 
(lift_sort n h (plus k d))) (lift k e (TSort n)) (lift_sort n k e)))))))) 
(\lambda (n: nat).(\lambda (h: nat).(\lambda (k: nat).(\lambda (d: 
nat).(\lambda (e: nat).(\lambda (H: (le e d)).(lt_le_e n e (eq T (lift h 
(plus k d) (lift k e (TLRef n))) (lift k e (lift h d (TLRef n)))) (\lambda 
(H0: (lt n e)).(let H1 \def (lt_le_trans n e d H0 H) in (eq_ind_r T (TLRef n) 
(\lambda (t0: T).(eq T (lift h (plus k d) t0) (lift k e (lift h d (TLRef 
n))))) (eq_ind_r T (TLRef n) (\lambda (t0: T).(eq T t0 (lift k e (lift h d 
(TLRef n))))) (eq_ind_r T (TLRef n) (\lambda (t0: T).(eq T (TLRef n) (lift k 
e t0))) (eq_ind_r T (TLRef n) (\lambda (t0: T).(eq T (TLRef n) t0)) 
(refl_equal T (TLRef n)) (lift k e (TLRef n)) (lift_lref_lt n k e H0)) (lift 
h d (TLRef n)) (lift_lref_lt n h d H1)) (lift h (plus k d) (TLRef n)) 
(lift_lref_lt n h (plus k d) (lt_le_trans n d (plus k d) H1 (le_plus_r k 
d)))) (lift k e (TLRef n)) (lift_lref_lt n k e H0)))) (\lambda (H0: (le e 
n)).(eq_ind_r T (TLRef (plus n k)) (\lambda (t0: T).(eq T (lift h (plus k d) 
t0) (lift k e (lift h d (TLRef n))))) (eq_ind_r nat (plus d k) (\lambda (n0: 
nat).(eq T (lift h n0 (TLRef (plus n k))) (lift k e (lift h d (TLRef n))))) 
(lt_le_e n d (eq T (lift h (plus d k) (TLRef (plus n k))) (lift k e (lift h d 
(TLRef n)))) (\lambda (H1: (lt n d)).(eq_ind_r T (TLRef (plus n k)) (\lambda 
(t0: T).(eq T t0 (lift k e (lift h d (TLRef n))))) (eq_ind_r T (TLRef n) 
(\lambda (t0: T).(eq T (TLRef (plus n k)) (lift k e t0))) (eq_ind_r T (TLRef 
(plus n k)) (\lambda (t0: T).(eq T (TLRef (plus n k)) t0)) (refl_equal T 
(TLRef (plus n k))) (lift k e (TLRef n)) (lift_lref_ge n k e H0)) (lift h d 
(TLRef n)) (lift_lref_lt n h d H1)) (lift h (plus d k) (TLRef (plus n k))) 
(lift_lref_lt (plus n k) h (plus d k) (lt_reg_r n d k H1)))) (\lambda (H1: 
(le d n)).(eq_ind_r T (TLRef (plus (plus n k) h)) (\lambda (t0: T).(eq T t0 
(lift k e (lift h d (TLRef n))))) (eq_ind_r T (TLRef (plus n h)) (\lambda 
(t0: T).(eq T (TLRef (plus (plus n k) h)) (lift k e t0))) (eq_ind_r T (TLRef 
(plus (plus n h) k)) (\lambda (t0: T).(eq T (TLRef (plus (plus n k) h)) t0)) 
(f_equal nat T TLRef (plus (plus n k) h) (plus (plus n h) k) (sym_eq nat 
(plus (plus n h) k) (plus (plus n k) h) (plus_permute_2_in_3 n h k))) (lift k 
e (TLRef (plus n h))) (lift_lref_ge (plus n h) k e (le_plus_trans e n h H0))) 
(lift h d (TLRef n)) (lift_lref_ge n h d H1)) (lift h (plus d k) (TLRef (plus 
n k))) (lift_lref_ge (plus n k) h (plus d k) (le_plus_plus d n k k H1 (le_n 
k)))))) (plus k d) (plus_sym k d)) (lift k e (TLRef n)) (lift_lref_ge n k e 
H0)))))))))) (\lambda (k: K).(\lambda (t0: T).(\lambda (H: ((\forall (h: 
nat).(\forall (k0: nat).(\forall (d: nat).(\forall (e: nat).((le e d) \to (eq 
T (lift h (plus k0 d) (lift k0 e t0)) (lift k0 e (lift h d 
t0)))))))))).(\lambda (t1: T).(\lambda (H0: ((\forall (h: nat).(\forall (k0: 
nat).(\forall (d: nat).(\forall (e: nat).((le e d) \to (eq T (lift h (plus k0 
d) (lift k0 e t1)) (lift k0 e (lift h d t1)))))))))).(\lambda (h: 
nat).(\lambda (k0: nat).(\lambda (d: nat).(\lambda (e: nat).(\lambda (H1: (le 
e d)).(eq_ind_r T (THead k (lift k0 e t0) (lift k0 (s k e) t1)) (\lambda (t2: 
T).(eq T (lift h (plus k0 d) t2) (lift k0 e (lift h d (THead k t0 t1))))) 
(eq_ind_r T (THead k (lift h (plus k0 d) (lift k0 e t0)) (lift h (s k (plus 
k0 d)) (lift k0 (s k e) t1))) (\lambda (t2: T).(eq T t2 (lift k0 e (lift h d 
(THead k t0 t1))))) (eq_ind_r T (THead k (lift h d t0) (lift h (s k d) t1)) 
(\lambda (t2: T).(eq T (THead k (lift h (plus k0 d) (lift k0 e t0)) (lift h 
(s k (plus k0 d)) (lift k0 (s k e) t1))) (lift k0 e t2))) (eq_ind_r T (THead 
k (lift k0 e (lift h d t0)) (lift k0 (s k e) (lift h (s k d) t1))) (\lambda 
(t2: T).(eq T (THead k (lift h (plus k0 d) (lift k0 e t0)) (lift h (s k (plus 
k0 d)) (lift k0 (s k e) t1))) t2)) (eq_ind_r nat (plus k0 (s k d)) (\lambda 
(n: nat).(eq T (THead k (lift h (plus k0 d) (lift k0 e t0)) (lift h n (lift 
k0 (s k e) t1))) (THead k (lift k0 e (lift h d t0)) (lift k0 (s k e) (lift h 
(s k d) t1))))) (f_equal3 K T T T THead k k (lift h (plus k0 d) (lift k0 e 
t0)) (lift k0 e (lift h d t0)) (lift h (plus k0 (s k d)) (lift k0 (s k e) 
t1)) (lift k0 (s k e) (lift h (s k d) t1)) (refl_equal K k) (H h k0 d e H1) 
(H0 h k0 (s k d) (s k e) (s_le k e d H1))) (s k (plus k0 d)) (s_plus_sym k k0 
d)) (lift k0 e (THead k (lift h d t0) (lift h (s k d) t1))) (lift_head k 
(lift h d t0) (lift h (s k d) t1) k0 e)) (lift h d (THead k t0 t1)) 
(lift_head k t0 t1 h d)) (lift h (plus k0 d) (THead k (lift k0 e t0) (lift k0 
(s k e) t1))) (lift_head k (lift k0 e t0) (lift k0 (s k e) t1) h (plus k0 
d))) (lift k0 e (THead k t0 t1)) (lift_head k t0 t1 k0 e)))))))))))) t).
(* COMMENTS
Initial nodes: 2143
END *)

