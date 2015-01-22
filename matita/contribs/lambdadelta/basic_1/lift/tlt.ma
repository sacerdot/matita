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

include "Basic-1/tlt/props.ma".

theorem lift_weight_map:
 \forall (t: T).(\forall (h: nat).(\forall (d: nat).(\forall (f: ((nat \to 
nat))).(((\forall (m: nat).((le d m) \to (eq nat (f m) O)))) \to (eq nat 
(weight_map f (lift h d t)) (weight_map f t))))))
\def
 \lambda (t: T).(T_ind (\lambda (t0: T).(\forall (h: nat).(\forall (d: 
nat).(\forall (f: ((nat \to nat))).(((\forall (m: nat).((le d m) \to (eq nat 
(f m) O)))) \to (eq nat (weight_map f (lift h d t0)) (weight_map f t0))))))) 
(\lambda (n: nat).(\lambda (_: nat).(\lambda (d: nat).(\lambda (f: ((nat \to 
nat))).(\lambda (_: ((\forall (m: nat).((le d m) \to (eq nat (f m) 
O))))).(refl_equal nat (weight_map f (TSort n)))))))) (\lambda (n: 
nat).(\lambda (h: nat).(\lambda (d: nat).(\lambda (f: ((nat \to 
nat))).(\lambda (H: ((\forall (m: nat).((le d m) \to (eq nat (f m) 
O))))).(lt_le_e n d (eq nat (weight_map f (lift h d (TLRef n))) (weight_map f 
(TLRef n))) (\lambda (H0: (lt n d)).(eq_ind_r T (TLRef n) (\lambda (t0: 
T).(eq nat (weight_map f t0) (weight_map f (TLRef n)))) (refl_equal nat 
(weight_map f (TLRef n))) (lift h d (TLRef n)) (lift_lref_lt n h d H0))) 
(\lambda (H0: (le d n)).(eq_ind_r T (TLRef (plus n h)) (\lambda (t0: T).(eq 
nat (weight_map f t0) (weight_map f (TLRef n)))) (eq_ind_r nat O (\lambda 
(n0: nat).(eq nat (f (plus n h)) n0)) (H (plus n h) (le_plus_trans d n h H0)) 
(f n) (H n H0)) (lift h d (TLRef n)) (lift_lref_ge n h d H0))))))))) (\lambda 
(k: K).(\lambda (t0: T).(\lambda (H: ((\forall (h: nat).(\forall (d: 
nat).(\forall (f: ((nat \to nat))).(((\forall (m: nat).((le d m) \to (eq nat 
(f m) O)))) \to (eq nat (weight_map f (lift h d t0)) (weight_map f 
t0)))))))).(\lambda (t1: T).(\lambda (H0: ((\forall (h: nat).(\forall (d: 
nat).(\forall (f: ((nat \to nat))).(((\forall (m: nat).((le d m) \to (eq nat 
(f m) O)))) \to (eq nat (weight_map f (lift h d t1)) (weight_map f 
t1)))))))).(\lambda (h: nat).(\lambda (d: nat).(\lambda (f: ((nat \to 
nat))).(\lambda (H1: ((\forall (m: nat).((le d m) \to (eq nat (f m) 
O))))).(K_ind (\lambda (k0: K).(eq nat (weight_map f (lift h d (THead k0 t0 
t1))) (weight_map f (THead k0 t0 t1)))) (\lambda (b: B).(eq_ind_r T (THead 
(Bind b) (lift h d t0) (lift h (s (Bind b) d) t1)) (\lambda (t2: T).(eq nat 
(weight_map f t2) (weight_map f (THead (Bind b) t0 t1)))) (B_ind (\lambda 
(b0: B).(eq nat (match b0 with [Abbr \Rightarrow (S (plus (weight_map f (lift 
h d t0)) (weight_map (wadd f (S (weight_map f (lift h d t0)))) (lift h (S d) 
t1)))) | Abst \Rightarrow (S (plus (weight_map f (lift h d t0)) (weight_map 
(wadd f O) (lift h (S d) t1)))) | Void \Rightarrow (S (plus (weight_map f 
(lift h d t0)) (weight_map (wadd f O) (lift h (S d) t1))))]) (match b0 with 
[Abbr \Rightarrow (S (plus (weight_map f t0) (weight_map (wadd f (S 
(weight_map f t0))) t1))) | Abst \Rightarrow (S (plus (weight_map f t0) 
(weight_map (wadd f O) t1))) | Void \Rightarrow (S (plus (weight_map f t0) 
(weight_map (wadd f O) t1)))]))) (eq_ind_r nat (weight_map f t0) (\lambda (n: 
nat).(eq nat (S (plus n (weight_map (wadd f (S n)) (lift h (S d) t1)))) (S 
(plus (weight_map f t0) (weight_map (wadd f (S (weight_map f t0))) t1))))) 
(eq_ind_r nat (weight_map (wadd f (S (weight_map f t0))) t1) (\lambda (n: 
nat).(eq nat (S (plus (weight_map f t0) n)) (S (plus (weight_map f t0) 
(weight_map (wadd f (S (weight_map f t0))) t1))))) (refl_equal nat (S (plus 
(weight_map f t0) (weight_map (wadd f (S (weight_map f t0))) t1)))) 
(weight_map (wadd f (S (weight_map f t0))) (lift h (S d) t1)) (H0 h (S d) 
(wadd f (S (weight_map f t0))) (\lambda (m: nat).(\lambda (H2: (le (S d) 
m)).(ex2_ind nat (\lambda (n: nat).(eq nat m (S n))) (\lambda (n: nat).(le d 
n)) (eq nat (wadd f (S (weight_map f t0)) m) O) (\lambda (x: nat).(\lambda 
(H3: (eq nat m (S x))).(\lambda (H4: (le d x)).(eq_ind_r nat (S x) (\lambda 
(n: nat).(eq nat (wadd f (S (weight_map f t0)) n) O)) (H1 x H4) m H3)))) 
(le_gen_S d m H2)))))) (weight_map f (lift h d t0)) (H h d f H1)) (eq_ind_r 
nat (weight_map (wadd f O) t1) (\lambda (n: nat).(eq nat (S (plus (weight_map 
f (lift h d t0)) n)) (S (plus (weight_map f t0) (weight_map (wadd f O) 
t1))))) (f_equal nat nat S (plus (weight_map f (lift h d t0)) (weight_map 
(wadd f O) t1)) (plus (weight_map f t0) (weight_map (wadd f O) t1)) (f_equal2 
nat nat nat plus (weight_map f (lift h d t0)) (weight_map f t0) (weight_map 
(wadd f O) t1) (weight_map (wadd f O) t1) (H h d f H1) (refl_equal nat 
(weight_map (wadd f O) t1)))) (weight_map (wadd f O) (lift h (S d) t1)) (H0 h 
(S d) (wadd f O) (\lambda (m: nat).(\lambda (H2: (le (S d) m)).(ex2_ind nat 
(\lambda (n: nat).(eq nat m (S n))) (\lambda (n: nat).(le d n)) (eq nat (wadd 
f O m) O) (\lambda (x: nat).(\lambda (H3: (eq nat m (S x))).(\lambda (H4: (le 
d x)).(eq_ind_r nat (S x) (\lambda (n: nat).(eq nat (wadd f O n) O)) (H1 x 
H4) m H3)))) (le_gen_S d m H2)))))) (eq_ind_r nat (weight_map (wadd f O) t1) 
(\lambda (n: nat).(eq nat (S (plus (weight_map f (lift h d t0)) n)) (S (plus 
(weight_map f t0) (weight_map (wadd f O) t1))))) (f_equal nat nat S (plus 
(weight_map f (lift h d t0)) (weight_map (wadd f O) t1)) (plus (weight_map f 
t0) (weight_map (wadd f O) t1)) (f_equal2 nat nat nat plus (weight_map f 
(lift h d t0)) (weight_map f t0) (weight_map (wadd f O) t1) (weight_map (wadd 
f O) t1) (H h d f H1) (refl_equal nat (weight_map (wadd f O) t1)))) 
(weight_map (wadd f O) (lift h (S d) t1)) (H0 h (S d) (wadd f O) (\lambda (m: 
nat).(\lambda (H2: (le (S d) m)).(ex2_ind nat (\lambda (n: nat).(eq nat m (S 
n))) (\lambda (n: nat).(le d n)) (eq nat (wadd f O m) O) (\lambda (x: 
nat).(\lambda (H3: (eq nat m (S x))).(\lambda (H4: (le d x)).(eq_ind_r nat (S 
x) (\lambda (n: nat).(eq nat (wadd f O n) O)) (H1 x H4) m H3)))) (le_gen_S d 
m H2)))))) b) (lift h d (THead (Bind b) t0 t1)) (lift_head (Bind b) t0 t1 h 
d))) (\lambda (f0: F).(eq_ind_r T (THead (Flat f0) (lift h d t0) (lift h (s 
(Flat f0) d) t1)) (\lambda (t2: T).(eq nat (weight_map f t2) (weight_map f 
(THead (Flat f0) t0 t1)))) (f_equal nat nat S (plus (weight_map f (lift h d 
t0)) (weight_map f (lift h d t1))) (plus (weight_map f t0) (weight_map f t1)) 
(f_equal2 nat nat nat plus (weight_map f (lift h d t0)) (weight_map f t0) 
(weight_map f (lift h d t1)) (weight_map f t1) (H h d f H1) (H0 h d f H1))) 
(lift h d (THead (Flat f0) t0 t1)) (lift_head (Flat f0) t0 t1 h d))) 
k)))))))))) t).
(* COMMENTS
Initial nodes: 1969
END *)

theorem lift_weight:
 \forall (t: T).(\forall (h: nat).(\forall (d: nat).(eq nat (weight (lift h d 
t)) (weight t))))
\def
 \lambda (t: T).(\lambda (h: nat).(\lambda (d: nat).(lift_weight_map t h d 
(\lambda (_: nat).O) (\lambda (m: nat).(\lambda (_: (le d m)).(refl_equal nat 
O)))))).
(* COMMENTS
Initial nodes: 31
END *)

theorem lift_weight_add:
 \forall (w: nat).(\forall (t: T).(\forall (h: nat).(\forall (d: 
nat).(\forall (f: ((nat \to nat))).(\forall (g: ((nat \to nat))).(((\forall 
(m: nat).((lt m d) \to (eq nat (g m) (f m))))) \to ((eq nat (g d) w) \to 
(((\forall (m: nat).((le d m) \to (eq nat (g (S m)) (f m))))) \to (eq nat 
(weight_map f (lift h d t)) (weight_map g (lift (S h) d t)))))))))))
\def
 \lambda (w: nat).(\lambda (t: T).(T_ind (\lambda (t0: T).(\forall (h: 
nat).(\forall (d: nat).(\forall (f: ((nat \to nat))).(\forall (g: ((nat \to 
nat))).(((\forall (m: nat).((lt m d) \to (eq nat (g m) (f m))))) \to ((eq nat 
(g d) w) \to (((\forall (m: nat).((le d m) \to (eq nat (g (S m)) (f m))))) 
\to (eq nat (weight_map f (lift h d t0)) (weight_map g (lift (S h) d 
t0))))))))))) (\lambda (n: nat).(\lambda (h: nat).(\lambda (d: nat).(\lambda 
(f: ((nat \to nat))).(\lambda (g: ((nat \to nat))).(\lambda (_: ((\forall (m: 
nat).((lt m d) \to (eq nat (g m) (f m)))))).(\lambda (_: (eq nat (g d) 
w)).(\lambda (_: ((\forall (m: nat).((le d m) \to (eq nat (g (S m)) (f 
m)))))).(refl_equal nat (weight_map g (lift (S h) d (TSort n)))))))))))) 
(\lambda (n: nat).(\lambda (h: nat).(\lambda (d: nat).(\lambda (f: ((nat \to 
nat))).(\lambda (g: ((nat \to nat))).(\lambda (H: ((\forall (m: nat).((lt m 
d) \to (eq nat (g m) (f m)))))).(\lambda (_: (eq nat (g d) w)).(\lambda (H1: 
((\forall (m: nat).((le d m) \to (eq nat (g (S m)) (f m)))))).(lt_le_e n d 
(eq nat (weight_map f (lift h d (TLRef n))) (weight_map g (lift (S h) d 
(TLRef n)))) (\lambda (H2: (lt n d)).(eq_ind_r T (TLRef n) (\lambda (t0: 
T).(eq nat (weight_map f t0) (weight_map g (lift (S h) d (TLRef n))))) 
(eq_ind_r T (TLRef n) (\lambda (t0: T).(eq nat (weight_map f (TLRef n)) 
(weight_map g t0))) (sym_eq nat (g n) (f n) (H n H2)) (lift (S h) d (TLRef 
n)) (lift_lref_lt n (S h) d H2)) (lift h d (TLRef n)) (lift_lref_lt n h d 
H2))) (\lambda (H2: (le d n)).(eq_ind_r T (TLRef (plus n h)) (\lambda (t0: 
T).(eq nat (weight_map f t0) (weight_map g (lift (S h) d (TLRef n))))) 
(eq_ind_r T (TLRef (plus n (S h))) (\lambda (t0: T).(eq nat (weight_map f 
(TLRef (plus n h))) (weight_map g t0))) (eq_ind nat (S (plus n h)) (\lambda 
(n0: nat).(eq nat (f (plus n h)) (g n0))) (sym_eq nat (g (S (plus n h))) (f 
(plus n h)) (H1 (plus n h) (le_plus_trans d n h H2))) (plus n (S h)) 
(plus_n_Sm n h)) (lift (S h) d (TLRef n)) (lift_lref_ge n (S h) d H2)) (lift 
h d (TLRef n)) (lift_lref_ge n h d H2)))))))))))) (\lambda (k: K).(\lambda 
(t0: T).(\lambda (H: ((\forall (h: nat).(\forall (d: nat).(\forall (f: ((nat 
\to nat))).(\forall (g: ((nat \to nat))).(((\forall (m: nat).((lt m d) \to 
(eq nat (g m) (f m))))) \to ((eq nat (g d) w) \to (((\forall (m: nat).((le d 
m) \to (eq nat (g (S m)) (f m))))) \to (eq nat (weight_map f (lift h d t0)) 
(weight_map g (lift (S h) d t0)))))))))))).(\lambda (t1: T).(\lambda (H0: 
((\forall (h: nat).(\forall (d: nat).(\forall (f: ((nat \to nat))).(\forall 
(g: ((nat \to nat))).(((\forall (m: nat).((lt m d) \to (eq nat (g m) (f 
m))))) \to ((eq nat (g d) w) \to (((\forall (m: nat).((le d m) \to (eq nat (g 
(S m)) (f m))))) \to (eq nat (weight_map f (lift h d t1)) (weight_map g (lift 
(S h) d t1)))))))))))).(\lambda (h: nat).(\lambda (d: nat).(\lambda (f: ((nat 
\to nat))).(\lambda (g: ((nat \to nat))).(\lambda (H1: ((\forall (m: 
nat).((lt m d) \to (eq nat (g m) (f m)))))).(\lambda (H2: (eq nat (g d) 
w)).(\lambda (H3: ((\forall (m: nat).((le d m) \to (eq nat (g (S m)) (f 
m)))))).(K_ind (\lambda (k0: K).(eq nat (weight_map f (lift h d (THead k0 t0 
t1))) (weight_map g (lift (S h) d (THead k0 t0 t1))))) (\lambda (b: 
B).(eq_ind_r T (THead (Bind b) (lift h d t0) (lift h (s (Bind b) d) t1)) 
(\lambda (t2: T).(eq nat (weight_map f t2) (weight_map g (lift (S h) d (THead 
(Bind b) t0 t1))))) (eq_ind_r T (THead (Bind b) (lift (S h) d t0) (lift (S h) 
(s (Bind b) d) t1)) (\lambda (t2: T).(eq nat (weight_map f (THead (Bind b) 
(lift h d t0) (lift h (s (Bind b) d) t1))) (weight_map g t2))) (B_ind 
(\lambda (b0: B).(eq nat (match b0 with [Abbr \Rightarrow (S (plus 
(weight_map f (lift h d t0)) (weight_map (wadd f (S (weight_map f (lift h d 
t0)))) (lift h (S d) t1)))) | Abst \Rightarrow (S (plus (weight_map f (lift h 
d t0)) (weight_map (wadd f O) (lift h (S d) t1)))) | Void \Rightarrow (S 
(plus (weight_map f (lift h d t0)) (weight_map (wadd f O) (lift h (S d) 
t1))))]) (match b0 with [Abbr \Rightarrow (S (plus (weight_map g (lift (S h) 
d t0)) (weight_map (wadd g (S (weight_map g (lift (S h) d t0)))) (lift (S h) 
(S d) t1)))) | Abst \Rightarrow (S (plus (weight_map g (lift (S h) d t0)) 
(weight_map (wadd g O) (lift (S h) (S d) t1)))) | Void \Rightarrow (S (plus 
(weight_map g (lift (S h) d t0)) (weight_map (wadd g O) (lift (S h) (S d) 
t1))))]))) (f_equal nat nat S (plus (weight_map f (lift h d t0)) (weight_map 
(wadd f (S (weight_map f (lift h d t0)))) (lift h (S d) t1))) (plus 
(weight_map g (lift (S h) d t0)) (weight_map (wadd g (S (weight_map g (lift 
(S h) d t0)))) (lift (S h) (S d) t1))) (f_equal2 nat nat nat plus (weight_map 
f (lift h d t0)) (weight_map g (lift (S h) d t0)) (weight_map (wadd f (S 
(weight_map f (lift h d t0)))) (lift h (S d) t1)) (weight_map (wadd g (S 
(weight_map g (lift (S h) d t0)))) (lift (S h) (S d) t1)) (H h d f g H1 H2 
H3) (H0 h (S d) (wadd f (S (weight_map f (lift h d t0)))) (wadd g (S 
(weight_map g (lift (S h) d t0)))) (\lambda (m: nat).(\lambda (H4: (lt m (S 
d))).(or_ind (eq nat m O) (ex2 nat (\lambda (m0: nat).(eq nat m (S m0))) 
(\lambda (m0: nat).(lt m0 d))) (eq nat (wadd g (S (weight_map g (lift (S h) d 
t0))) m) (wadd f (S (weight_map f (lift h d t0))) m)) (\lambda (H5: (eq nat m 
O)).(eq_ind_r nat O (\lambda (n: nat).(eq nat (wadd g (S (weight_map g (lift 
(S h) d t0))) n) (wadd f (S (weight_map f (lift h d t0))) n))) (f_equal nat 
nat S (weight_map g (lift (S h) d t0)) (weight_map f (lift h d t0)) (sym_eq 
nat (weight_map f (lift h d t0)) (weight_map g (lift (S h) d t0)) (H h d f g 
H1 H2 H3))) m H5)) (\lambda (H5: (ex2 nat (\lambda (m0: nat).(eq nat m (S 
m0))) (\lambda (m0: nat).(lt m0 d)))).(ex2_ind nat (\lambda (m0: nat).(eq nat 
m (S m0))) (\lambda (m0: nat).(lt m0 d)) (eq nat (wadd g (S (weight_map g 
(lift (S h) d t0))) m) (wadd f (S (weight_map f (lift h d t0))) m)) (\lambda 
(x: nat).(\lambda (H6: (eq nat m (S x))).(\lambda (H7: (lt x d)).(eq_ind_r 
nat (S x) (\lambda (n: nat).(eq nat (wadd g (S (weight_map g (lift (S h) d 
t0))) n) (wadd f (S (weight_map f (lift h d t0))) n))) (H1 x H7) m H6)))) 
H5)) (lt_gen_xS m d H4)))) H2 (\lambda (m: nat).(\lambda (H4: (le (S d) 
m)).(ex2_ind nat (\lambda (n: nat).(eq nat m (S n))) (\lambda (n: nat).(le d 
n)) (eq nat (g m) (wadd f (S (weight_map f (lift h d t0))) m)) (\lambda (x: 
nat).(\lambda (H5: (eq nat m (S x))).(\lambda (H6: (le d x)).(eq_ind_r nat (S 
x) (\lambda (n: nat).(eq nat (g n) (wadd f (S (weight_map f (lift h d t0))) 
n))) (H3 x H6) m H5)))) (le_gen_S d m H4))))))) (f_equal nat nat S (plus 
(weight_map f (lift h d t0)) (weight_map (wadd f O) (lift h (S d) t1))) (plus 
(weight_map g (lift (S h) d t0)) (weight_map (wadd g O) (lift (S h) (S d) 
t1))) (f_equal2 nat nat nat plus (weight_map f (lift h d t0)) (weight_map g 
(lift (S h) d t0)) (weight_map (wadd f O) (lift h (S d) t1)) (weight_map 
(wadd g O) (lift (S h) (S d) t1)) (H h d f g H1 H2 H3) (H0 h (S d) (wadd f O) 
(wadd g O) (\lambda (m: nat).(\lambda (H4: (lt m (S d))).(or_ind (eq nat m O) 
(ex2 nat (\lambda (m0: nat).(eq nat m (S m0))) (\lambda (m0: nat).(lt m0 d))) 
(eq nat (wadd g O m) (wadd f O m)) (\lambda (H5: (eq nat m O)).(eq_ind_r nat 
O (\lambda (n: nat).(eq nat (wadd g O n) (wadd f O n))) (refl_equal nat O) m 
H5)) (\lambda (H5: (ex2 nat (\lambda (m0: nat).(eq nat m (S m0))) (\lambda 
(m0: nat).(lt m0 d)))).(ex2_ind nat (\lambda (m0: nat).(eq nat m (S m0))) 
(\lambda (m0: nat).(lt m0 d)) (eq nat (wadd g O m) (wadd f O m)) (\lambda (x: 
nat).(\lambda (H6: (eq nat m (S x))).(\lambda (H7: (lt x d)).(eq_ind_r nat (S 
x) (\lambda (n: nat).(eq nat (wadd g O n) (wadd f O n))) (H1 x H7) m H6)))) 
H5)) (lt_gen_xS m d H4)))) H2 (\lambda (m: nat).(\lambda (H4: (le (S d) 
m)).(ex2_ind nat (\lambda (n: nat).(eq nat m (S n))) (\lambda (n: nat).(le d 
n)) (eq nat (g m) (wadd f O m)) (\lambda (x: nat).(\lambda (H5: (eq nat m (S 
x))).(\lambda (H6: (le d x)).(eq_ind_r nat (S x) (\lambda (n: nat).(eq nat (g 
n) (wadd f O n))) (H3 x H6) m H5)))) (le_gen_S d m H4))))))) (f_equal nat nat 
S (plus (weight_map f (lift h d t0)) (weight_map (wadd f O) (lift h (S d) 
t1))) (plus (weight_map g (lift (S h) d t0)) (weight_map (wadd g O) (lift (S 
h) (S d) t1))) (f_equal2 nat nat nat plus (weight_map f (lift h d t0)) 
(weight_map g (lift (S h) d t0)) (weight_map (wadd f O) (lift h (S d) t1)) 
(weight_map (wadd g O) (lift (S h) (S d) t1)) (H h d f g H1 H2 H3) (H0 h (S 
d) (wadd f O) (wadd g O) (\lambda (m: nat).(\lambda (H4: (lt m (S 
d))).(or_ind (eq nat m O) (ex2 nat (\lambda (m0: nat).(eq nat m (S m0))) 
(\lambda (m0: nat).(lt m0 d))) (eq nat (wadd g O m) (wadd f O m)) (\lambda 
(H5: (eq nat m O)).(eq_ind_r nat O (\lambda (n: nat).(eq nat (wadd g O n) 
(wadd f O n))) (refl_equal nat O) m H5)) (\lambda (H5: (ex2 nat (\lambda (m0: 
nat).(eq nat m (S m0))) (\lambda (m0: nat).(lt m0 d)))).(ex2_ind nat (\lambda 
(m0: nat).(eq nat m (S m0))) (\lambda (m0: nat).(lt m0 d)) (eq nat (wadd g O 
m) (wadd f O m)) (\lambda (x: nat).(\lambda (H6: (eq nat m (S x))).(\lambda 
(H7: (lt x d)).(eq_ind_r nat (S x) (\lambda (n: nat).(eq nat (wadd g O n) 
(wadd f O n))) (H1 x H7) m H6)))) H5)) (lt_gen_xS m d H4)))) H2 (\lambda (m: 
nat).(\lambda (H4: (le (S d) m)).(ex2_ind nat (\lambda (n: nat).(eq nat m (S 
n))) (\lambda (n: nat).(le d n)) (eq nat (g m) (wadd f O m)) (\lambda (x: 
nat).(\lambda (H5: (eq nat m (S x))).(\lambda (H6: (le d x)).(eq_ind_r nat (S 
x) (\lambda (n: nat).(eq nat (g n) (wadd f O n))) (H3 x H6) m H5)))) 
(le_gen_S d m H4))))))) b) (lift (S h) d (THead (Bind b) t0 t1)) (lift_head 
(Bind b) t0 t1 (S h) d)) (lift h d (THead (Bind b) t0 t1)) (lift_head (Bind 
b) t0 t1 h d))) (\lambda (f0: F).(eq_ind_r T (THead (Flat f0) (lift h d t0) 
(lift h (s (Flat f0) d) t1)) (\lambda (t2: T).(eq nat (weight_map f t2) 
(weight_map g (lift (S h) d (THead (Flat f0) t0 t1))))) (eq_ind_r T (THead 
(Flat f0) (lift (S h) d t0) (lift (S h) (s (Flat f0) d) t1)) (\lambda (t2: 
T).(eq nat (weight_map f (THead (Flat f0) (lift h d t0) (lift h (s (Flat f0) 
d) t1))) (weight_map g t2))) (f_equal nat nat S (plus (weight_map f (lift h d 
t0)) (weight_map f (lift h d t1))) (plus (weight_map g (lift (S h) d t0)) 
(weight_map g (lift (S h) d t1))) (f_equal2 nat nat nat plus (weight_map f 
(lift h d t0)) (weight_map g (lift (S h) d t0)) (weight_map f (lift h d t1)) 
(weight_map g (lift (S h) d t1)) (H h d f g H1 H2 H3) (H0 h d f g H1 H2 H3))) 
(lift (S h) d (THead (Flat f0) t0 t1)) (lift_head (Flat f0) t0 t1 (S h) d)) 
(lift h d (THead (Flat f0) t0 t1)) (lift_head (Flat f0) t0 t1 h d))) 
k))))))))))))) t)).
(* COMMENTS
Initial nodes: 3697
END *)

theorem lift_weight_add_O:
 \forall (w: nat).(\forall (t: T).(\forall (h: nat).(\forall (f: ((nat \to 
nat))).(eq nat (weight_map f (lift h O t)) (weight_map (wadd f w) (lift (S h) 
O t))))))
\def
 \lambda (w: nat).(\lambda (t: T).(\lambda (h: nat).(\lambda (f: ((nat \to 
nat))).(lift_weight_add (plus (wadd f w O) O) t h O f (wadd f w) (\lambda (m: 
nat).(\lambda (H: (lt m O)).(lt_x_O m H (eq nat (wadd f w m) (f m))))) 
(plus_n_O (wadd f w O)) (\lambda (m: nat).(\lambda (_: (le O m)).(refl_equal 
nat (f m)))))))).
(* COMMENTS
Initial nodes: 93
END *)

theorem lift_tlt_dx:
 \forall (k: K).(\forall (u: T).(\forall (t: T).(\forall (h: nat).(\forall 
(d: nat).(tlt t (THead k u (lift h d t)))))))
\def
 \lambda (k: K).(\lambda (u: T).(\lambda (t: T).(\lambda (h: nat).(\lambda 
(d: nat).(eq_ind nat (weight (lift h d t)) (\lambda (n: nat).(lt n (weight 
(THead k u (lift h d t))))) (tlt_head_dx k u (lift h d t)) (weight t) 
(lift_weight t h d)))))).
(* COMMENTS
Initial nodes: 71
END *)

