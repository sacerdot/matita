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

include "basic_1/lift/defs.ma".

include "basic_1/s/props.ma".

include "basic_1/T/fwd.ma".

theorem lift_sort:
 \forall (n: nat).(\forall (h: nat).(\forall (d: nat).(eq T (lift h d (TSort 
n)) (TSort n))))
\def
 \lambda (n: nat).(\lambda (_: nat).(\lambda (_: nat).(refl_equal T (TSort 
n)))).

theorem lift_lref_lt:
 \forall (n: nat).(\forall (h: nat).(\forall (d: nat).((lt n d) \to (eq T 
(lift h d (TLRef n)) (TLRef n)))))
\def
 \lambda (n: nat).(\lambda (h: nat).(\lambda (d: nat).(\lambda (H: (lt n 
d)).(eq_ind bool true (\lambda (b: bool).(eq T (TLRef (match b with [true 
\Rightarrow n | false \Rightarrow (plus n h)])) (TLRef n))) (refl_equal T 
(TLRef n)) (blt n d) (sym_eq bool (blt n d) true (lt_blt d n H)))))).

theorem lift_lref_ge:
 \forall (n: nat).(\forall (h: nat).(\forall (d: nat).((le d n) \to (eq T 
(lift h d (TLRef n)) (TLRef (plus n h))))))
\def
 \lambda (n: nat).(\lambda (h: nat).(\lambda (d: nat).(\lambda (H: (le d 
n)).(eq_ind bool false (\lambda (b: bool).(eq T (TLRef (match b with [true 
\Rightarrow n | false \Rightarrow (plus n h)])) (TLRef (plus n h)))) 
(refl_equal T (TLRef (plus n h))) (blt n d) (sym_eq bool (blt n d) false 
(le_bge d n H)))))).

theorem lift_head:
 \forall (k: K).(\forall (u: T).(\forall (t: T).(\forall (h: nat).(\forall 
(d: nat).(eq T (lift h d (THead k u t)) (THead k (lift h d u) (lift h (s k d) 
t)))))))
\def
 \lambda (k: K).(\lambda (u: T).(\lambda (t: T).(\lambda (h: nat).(\lambda 
(d: nat).(refl_equal T (THead k (lift h d u) (lift h (s k d) t))))))).

theorem lift_bind:
 \forall (b: B).(\forall (u: T).(\forall (t: T).(\forall (h: nat).(\forall 
(d: nat).(eq T (lift h d (THead (Bind b) u t)) (THead (Bind b) (lift h d u) 
(lift h (S d) t)))))))
\def
 \lambda (b: B).(\lambda (u: T).(\lambda (t: T).(\lambda (h: nat).(\lambda 
(d: nat).(refl_equal T (THead (Bind b) (lift h d u) (lift h (S d) t))))))).

theorem lift_flat:
 \forall (f: F).(\forall (u: T).(\forall (t: T).(\forall (h: nat).(\forall 
(d: nat).(eq T (lift h d (THead (Flat f) u t)) (THead (Flat f) (lift h d u) 
(lift h d t)))))))
\def
 \lambda (f: F).(\lambda (u: T).(\lambda (t: T).(\lambda (h: nat).(\lambda 
(d: nat).(refl_equal T (THead (Flat f) (lift h d u) (lift h d t))))))).

theorem thead_x_lift_y_y:
 \forall (k: K).(\forall (t: T).(\forall (v: T).(\forall (h: nat).(\forall 
(d: nat).((eq T (THead k v (lift h d t)) t) \to (\forall (P: Prop).P))))))
\def
 \lambda (k: K).(\lambda (t: T).(T_ind (\lambda (t0: T).(\forall (v: 
T).(\forall (h: nat).(\forall (d: nat).((eq T (THead k v (lift h d t0)) t0) 
\to (\forall (P: Prop).P)))))) (\lambda (n: nat).(\lambda (v: T).(\lambda (h: 
nat).(\lambda (d: nat).(\lambda (H: (eq T (THead k v (lift h d (TSort n))) 
(TSort n))).(\lambda (P: Prop).(let H0 \def (eq_ind T (THead k v (lift h d 
(TSort n))) (\lambda (ee: T).(match ee with [(TSort _) \Rightarrow False | 
(TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow True])) I (TSort n) 
H) in (False_ind P H0)))))))) (\lambda (n: nat).(\lambda (v: T).(\lambda (h: 
nat).(\lambda (d: nat).(\lambda (H: (eq T (THead k v (lift h d (TLRef n))) 
(TLRef n))).(\lambda (P: Prop).(let H0 \def (eq_ind T (THead k v (lift h d 
(TLRef n))) (\lambda (ee: T).(match ee with [(TSort _) \Rightarrow False | 
(TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow True])) I (TLRef n) 
H) in (False_ind P H0)))))))) (\lambda (k0: K).(\lambda (t0: T).(\lambda (_: 
((\forall (v: T).(\forall (h: nat).(\forall (d: nat).((eq T (THead k v (lift 
h d t0)) t0) \to (\forall (P: Prop).P))))))).(\lambda (t1: T).(\lambda (H0: 
((\forall (v: T).(\forall (h: nat).(\forall (d: nat).((eq T (THead k v (lift 
h d t1)) t1) \to (\forall (P: Prop).P))))))).(\lambda (v: T).(\lambda (h: 
nat).(\lambda (d: nat).(\lambda (H1: (eq T (THead k v (lift h d (THead k0 t0 
t1))) (THead k0 t0 t1))).(\lambda (P: Prop).(let H2 \def (f_equal T K 
(\lambda (e: T).(match e with [(TSort _) \Rightarrow k | (TLRef _) 
\Rightarrow k | (THead k1 _ _) \Rightarrow k1])) (THead k v (lift h d (THead 
k0 t0 t1))) (THead k0 t0 t1) H1) in ((let H3 \def (f_equal T T (\lambda (e: 
T).(match e with [(TSort _) \Rightarrow v | (TLRef _) \Rightarrow v | (THead 
_ t2 _) \Rightarrow t2])) (THead k v (lift h d (THead k0 t0 t1))) (THead k0 
t0 t1) H1) in ((let H4 \def (f_equal T T (\lambda (e: T).(match e with 
[(TSort _) \Rightarrow (THead k0 (lref_map (\lambda (x: nat).(plus x h)) d 
t0) (lref_map (\lambda (x: nat).(plus x h)) (s k0 d) t1)) | (TLRef _) 
\Rightarrow (THead k0 (lref_map (\lambda (x: nat).(plus x h)) d t0) (lref_map 
(\lambda (x: nat).(plus x h)) (s k0 d) t1)) | (THead _ _ t2) \Rightarrow 
t2])) (THead k v (lift h d (THead k0 t0 t1))) (THead k0 t0 t1) H1) in 
(\lambda (_: (eq T v t0)).(\lambda (H6: (eq K k k0)).(let H7 \def (eq_ind K k 
(\lambda (k1: K).(\forall (v0: T).(\forall (h0: nat).(\forall (d0: nat).((eq 
T (THead k1 v0 (lift h0 d0 t1)) t1) \to (\forall (P0: Prop).P0)))))) H0 k0 
H6) in (let H8 \def (eq_ind T (lift h d (THead k0 t0 t1)) (\lambda (t2: 
T).(eq T t2 t1)) H4 (THead k0 (lift h d t0) (lift h (s k0 d) t1)) (lift_head 
k0 t0 t1 h d)) in (H7 (lift h d t0) h (s k0 d) H8 P)))))) H3)) H2)))))))))))) 
t)).

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
t1)) (\lambda (t2: T).(eq T t2 (THead k t0 t1))) (sym_eq T (THead k t0 t1) 
(THead k (lift O d t0) (lift O (s k d) t1)) (sym_eq T (THead k (lift O d t0) 
(lift O (s k d) t1)) (THead k t0 t1) (f_equal3 K T T T THead k k (lift O d 
t0) t0 (lift O (s k d) t1) t1 (refl_equal K k) (H d) (H0 (s k d))))) (lift O 
d (THead k t0 t1)) (lift_head k t0 t1 O d)))))))) t).

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

theorem lift_tle:
 \forall (t: T).(\forall (h: nat).(\forall (d: nat).(tle t (lift h d t))))
\def
 \lambda (t: T).(T_ind (\lambda (t0: T).(\forall (h: nat).(\forall (d: 
nat).(le (tweight t0) (tweight (lift h d t0)))))) (\lambda (_: nat).(\lambda 
(_: nat).(\lambda (_: nat).(le_n (S O))))) (\lambda (_: nat).(\lambda (_: 
nat).(\lambda (_: nat).(le_n (S O))))) (\lambda (k: K).(\lambda (t0: 
T).(\lambda (H: ((\forall (h: nat).(\forall (d: nat).(le (tweight t0) 
(tweight (lift h d t0))))))).(\lambda (t1: T).(\lambda (H0: ((\forall (h: 
nat).(\forall (d: nat).(le (tweight t1) (tweight (lift h d t1))))))).(\lambda 
(h: nat).(\lambda (d: nat).(let H_y \def (H h d) in (let H_y0 \def (H0 h (s k 
d)) in (le_n_S (plus (tweight t0) (tweight t1)) (plus (tweight (lref_map 
(\lambda (x: nat).(plus x h)) d t0)) (tweight (lref_map (\lambda (x: 
nat).(plus x h)) (s k d) t1))) (le_plus_plus (tweight t0) (tweight (lref_map 
(\lambda (x: nat).(plus x h)) d t0)) (tweight t1) (tweight (lref_map (\lambda 
(x: nat).(plus x h)) (s k d) t1)) H_y H_y0))))))))))) t).

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

theorem lift_free_sym:
 \forall (t: T).(\forall (h: nat).(\forall (k: nat).(\forall (d: 
nat).(\forall (e: nat).((le e (plus d h)) \to ((le d e) \to (eq T (lift k e 
(lift h d t)) (lift (plus h k) d t))))))))
\def
 \lambda (t: T).(\lambda (h: nat).(\lambda (k: nat).(\lambda (d: 
nat).(\lambda (e: nat).(\lambda (H: (le e (plus d h))).(\lambda (H0: (le d 
e)).(eq_ind_r nat (plus k h) (\lambda (n: nat).(eq T (lift k e (lift h d t)) 
(lift n d t))) (lift_free t h k d e H H0) (plus h k) (plus_sym h k)))))))).

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
(f_equal nat T TLRef (plus (plus n k) h) (plus (plus n h) k) 
(plus_permute_2_in_3 n k h)) (lift k e (TLRef (plus n h))) (lift_lref_ge 
(plus n h) k e (le_plus_trans e n h H0))) (lift h d (TLRef n)) (lift_lref_ge 
n h d H1)) (lift h (plus d k) (TLRef (plus n k))) (lift_lref_ge (plus n k) h 
(plus d k) (le_plus_plus d n k k H1 (le_n k)))))) (plus k d) (plus_sym k d)) 
(lift k e (TLRef n)) (lift_lref_ge n k e H0)))))))))) (\lambda (k: 
K).(\lambda (t0: T).(\lambda (H: ((\forall (h: nat).(\forall (k0: 
nat).(\forall (d: nat).(\forall (e: nat).((le e d) \to (eq T (lift h (plus k0 
d) (lift k0 e t0)) (lift k0 e (lift h d t0)))))))))).(\lambda (t1: 
T).(\lambda (H0: ((\forall (h: nat).(\forall (k0: nat).(\forall (d: 
nat).(\forall (e: nat).((le e d) \to (eq T (lift h (plus k0 d) (lift k0 e 
t1)) (lift k0 e (lift h d t1)))))))))).(\lambda (h: nat).(\lambda (k0: 
nat).(\lambda (d: nat).(\lambda (e: nat).(\lambda (H1: (le e d)).(eq_ind_r T 
(THead k (lift k0 e t0) (lift k0 (s k e) t1)) (\lambda (t2: T).(eq T (lift h 
(plus k0 d) t2) (lift k0 e (lift h d (THead k t0 t1))))) (eq_ind_r T (THead k 
(lift h (plus k0 d) (lift k0 e t0)) (lift h (s k (plus k0 d)) (lift k0 (s k 
e) t1))) (\lambda (t2: T).(eq T t2 (lift k0 e (lift h d (THead k t0 t1))))) 
(eq_ind_r T (THead k (lift h d t0) (lift h (s k d) t1)) (\lambda (t2: T).(eq 
T (THead k (lift h (plus k0 d) (lift k0 e t0)) (lift h (s k (plus k0 d)) 
(lift k0 (s k e) t1))) (lift k0 e t2))) (eq_ind_r T (THead k (lift k0 e (lift 
h d t0)) (lift k0 (s k e) (lift h (s k d) t1))) (\lambda (t2: T).(eq T (THead 
k (lift h (plus k0 d) (lift k0 e t0)) (lift h (s k (plus k0 d)) (lift k0 (s k 
e) t1))) t2)) (eq_ind_r nat (plus k0 (s k d)) (\lambda (n: nat).(eq T (THead 
k (lift h (plus k0 d) (lift k0 e t0)) (lift h n (lift k0 (s k e) t1))) (THead 
k (lift k0 e (lift h d t0)) (lift k0 (s k e) (lift h (s k d) t1))))) 
(f_equal3 K T T T THead k k (lift h (plus k0 d) (lift k0 e t0)) (lift k0 e 
(lift h d t0)) (lift h (plus k0 (s k d)) (lift k0 (s k e) t1)) (lift k0 (s k 
e) (lift h (s k d) t1)) (refl_equal K k) (H h k0 d e H1) (H0 h k0 (s k d) (s 
k e) (s_le k e d H1))) (s k (plus k0 d)) (s_plus_sym k k0 d)) (lift k0 e 
(THead k (lift h d t0) (lift h (s k d) t1))) (lift_head k (lift h d t0) (lift 
h (s k d) t1) k0 e)) (lift h d (THead k t0 t1)) (lift_head k t0 t1 h d)) 
(lift h (plus k0 d) (THead k (lift k0 e t0) (lift k0 (s k e) t1))) (lift_head 
k (lift k0 e t0) (lift k0 (s k e) t1) h (plus k0 d))) (lift k0 e (THead k t0 
t1)) (lift_head k t0 t1 k0 e)))))))))))) t).

