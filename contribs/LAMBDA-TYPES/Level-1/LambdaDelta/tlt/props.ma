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

set "baseuri" "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/tlt/props".

include "tlt/defs.ma".

theorem wadd_le:
 \forall (f: ((nat \to nat))).(\forall (g: ((nat \to nat))).(((\forall (n: 
nat).(le (f n) (g n)))) \to (\forall (v: nat).(\forall (w: nat).((le v w) \to 
(\forall (n: nat).(le (wadd f v n) (wadd g w n))))))))
\def
 \lambda (f: ((nat \to nat))).(\lambda (g: ((nat \to nat))).(\lambda (H: 
((\forall (n: nat).(le (f n) (g n))))).(\lambda (v: nat).(\lambda (w: 
nat).(\lambda (H0: (le v w)).(\lambda (n: nat).(nat_ind (\lambda (n0: 
nat).(le (wadd f v n0) (wadd g w n0))) H0 (\lambda (n0: nat).(\lambda (_: (le 
(wadd f v n0) (wadd g w n0))).(H n0))) n))))))).

theorem wadd_lt:
 \forall (f: ((nat \to nat))).(\forall (g: ((nat \to nat))).(((\forall (n: 
nat).(le (f n) (g n)))) \to (\forall (v: nat).(\forall (w: nat).((lt v w) \to 
(\forall (n: nat).(le (wadd f v n) (wadd g w n))))))))
\def
 \lambda (f: ((nat \to nat))).(\lambda (g: ((nat \to nat))).(\lambda (H: 
((\forall (n: nat).(le (f n) (g n))))).(\lambda (v: nat).(\lambda (w: 
nat).(\lambda (H0: (lt v w)).(\lambda (n: nat).(nat_ind (\lambda (n0: 
nat).(le (wadd f v n0) (wadd g w n0))) (le_S_n v w (le_S (S v) w H0)) 
(\lambda (n0: nat).(\lambda (_: (le (wadd f v n0) (wadd g w n0))).(H n0))) 
n))))))).

theorem wadd_O:
 \forall (n: nat).(eq nat (wadd (\lambda (_: nat).O) O n) O)
\def
 \lambda (n: nat).(nat_ind (\lambda (n0: nat).(eq nat (wadd (\lambda (_: 
nat).O) O n0) O)) (refl_equal nat O) (\lambda (n0: nat).(\lambda (_: (eq nat 
(wadd (\lambda (_: nat).O) O n0) O)).(refl_equal nat O))) n).

theorem weight_le:
 \forall (t: T).(\forall (f: ((nat \to nat))).(\forall (g: ((nat \to 
nat))).(((\forall (n: nat).(le (f n) (g n)))) \to (le (weight_map f t) 
(weight_map g t)))))
\def
 \lambda (t: T).(T_ind (\lambda (t0: T).(\forall (f: ((nat \to 
nat))).(\forall (g: ((nat \to nat))).(((\forall (n: nat).(le (f n) (g n)))) 
\to (le (weight_map f t0) (weight_map g t0)))))) (\lambda (n: nat).(\lambda 
(f: ((nat \to nat))).(\lambda (g: ((nat \to nat))).(\lambda (_: ((\forall (n: 
nat).(le (f n) (g n))))).(le_n (weight_map g (TSort n))))))) (\lambda (n: 
nat).(\lambda (f: ((nat \to nat))).(\lambda (g: ((nat \to nat))).(\lambda (H: 
((\forall (n: nat).(le (f n) (g n))))).(H n))))) (\lambda (k: K).(K_ind 
(\lambda (k0: K).(\forall (t0: T).(((\forall (f: ((nat \to nat))).(\forall 
(g: ((nat \to nat))).(((\forall (n: nat).(le (f n) (g n)))) \to (le 
(weight_map f t0) (weight_map g t0)))))) \to (\forall (t1: T).(((\forall (f: 
((nat \to nat))).(\forall (g: ((nat \to nat))).(((\forall (n: nat).(le (f n) 
(g n)))) \to (le (weight_map f t1) (weight_map g t1)))))) \to (\forall (f: 
((nat \to nat))).(\forall (g: ((nat \to nat))).(((\forall (n: nat).(le (f n) 
(g n)))) \to (le (weight_map f (THead k0 t0 t1)) (weight_map g (THead k0 t0 
t1))))))))))) (\lambda (b: B).(B_ind (\lambda (b0: B).(\forall (t0: 
T).(((\forall (f: ((nat \to nat))).(\forall (g: ((nat \to nat))).(((\forall 
(n: nat).(le (f n) (g n)))) \to (le (weight_map f t0) (weight_map g t0)))))) 
\to (\forall (t1: T).(((\forall (f: ((nat \to nat))).(\forall (g: ((nat \to 
nat))).(((\forall (n: nat).(le (f n) (g n)))) \to (le (weight_map f t1) 
(weight_map g t1)))))) \to (\forall (f: ((nat \to nat))).(\forall (g: ((nat 
\to nat))).(((\forall (n: nat).(le (f n) (g n)))) \to (le (match b0 with 
[Abbr \Rightarrow (S (plus (weight_map f t0) (weight_map (wadd f (S 
(weight_map f t0))) t1))) | Abst \Rightarrow (S (plus (weight_map f t0) 
(weight_map (wadd f O) t1))) | Void \Rightarrow (S (plus (weight_map f t0) 
(weight_map (wadd f O) t1)))]) (match b0 with [Abbr \Rightarrow (S (plus 
(weight_map g t0) (weight_map (wadd g (S (weight_map g t0))) t1))) | Abst 
\Rightarrow (S (plus (weight_map g t0) (weight_map (wadd g O) t1))) | Void 
\Rightarrow (S (plus (weight_map g t0) (weight_map (wadd g O) 
t1)))])))))))))) (\lambda (t0: T).(\lambda (H: ((\forall (f: ((nat \to 
nat))).(\forall (g: ((nat \to nat))).(((\forall (n: nat).(le (f n) (g n)))) 
\to (le (weight_map f t0) (weight_map g t0))))))).(\lambda (t1: T).(\lambda 
(H0: ((\forall (f: ((nat \to nat))).(\forall (g: ((nat \to nat))).(((\forall 
(n: nat).(le (f n) (g n)))) \to (le (weight_map f t1) (weight_map g 
t1))))))).(\lambda (f: ((nat \to nat))).(\lambda (g: ((nat \to 
nat))).(\lambda (H1: ((\forall (n: nat).(le (f n) (g n))))).(le_n_S (plus 
(weight_map f t0) (weight_map (wadd f (S (weight_map f t0))) t1)) (plus 
(weight_map g t0) (weight_map (wadd g (S (weight_map g t0))) t1)) 
(plus_le_compat (weight_map f t0) (weight_map g t0) (weight_map (wadd f (S 
(weight_map f t0))) t1) (weight_map (wadd g (S (weight_map g t0))) t1) (H f g 
H1) (H0 (wadd f (S (weight_map f t0))) (wadd g (S (weight_map g t0))) 
(\lambda (n: nat).(wadd_le f g H1 (S (weight_map f t0)) (S (weight_map g t0)) 
(le_n_S (weight_map f t0) (weight_map g t0) (H f g H1)) n)))))))))))) 
(\lambda (t0: T).(\lambda (H: ((\forall (f: ((nat \to nat))).(\forall (g: 
((nat \to nat))).(((\forall (n: nat).(le (f n) (g n)))) \to (le (weight_map f 
t0) (weight_map g t0))))))).(\lambda (t1: T).(\lambda (H0: ((\forall (f: 
((nat \to nat))).(\forall (g: ((nat \to nat))).(((\forall (n: nat).(le (f n) 
(g n)))) \to (le (weight_map f t1) (weight_map g t1))))))).(\lambda (f: ((nat 
\to nat))).(\lambda (g: ((nat \to nat))).(\lambda (H1: ((\forall (n: nat).(le 
(f n) (g n))))).(le_S_n (S (plus (weight_map f t0) (weight_map (wadd f O) 
t1))) (S (plus (weight_map g t0) (weight_map (wadd g O) t1))) (le_n_S (S 
(plus (weight_map f t0) (weight_map (wadd f O) t1))) (S (plus (weight_map g 
t0) (weight_map (wadd g O) t1))) (le_n_S (plus (weight_map f t0) (weight_map 
(wadd f O) t1)) (plus (weight_map g t0) (weight_map (wadd g O) t1)) 
(plus_le_compat (weight_map f t0) (weight_map g t0) (weight_map (wadd f O) 
t1) (weight_map (wadd g O) t1) (H f g H1) (H0 (wadd f O) (wadd g O) (\lambda 
(n: nat).(wadd_le f g H1 O O (le_n O) n)))))))))))))) (\lambda (t0: 
T).(\lambda (H: ((\forall (f: ((nat \to nat))).(\forall (g: ((nat \to 
nat))).(((\forall (n: nat).(le (f n) (g n)))) \to (le (weight_map f t0) 
(weight_map g t0))))))).(\lambda (t1: T).(\lambda (H0: ((\forall (f: ((nat 
\to nat))).(\forall (g: ((nat \to nat))).(((\forall (n: nat).(le (f n) (g 
n)))) \to (le (weight_map f t1) (weight_map g t1))))))).(\lambda (f: ((nat 
\to nat))).(\lambda (g: ((nat \to nat))).(\lambda (H1: ((\forall (n: nat).(le 
(f n) (g n))))).(le_S_n (S (plus (weight_map f t0) (weight_map (wadd f O) 
t1))) (S (plus (weight_map g t0) (weight_map (wadd g O) t1))) (le_n_S (S 
(plus (weight_map f t0) (weight_map (wadd f O) t1))) (S (plus (weight_map g 
t0) (weight_map (wadd g O) t1))) (le_n_S (plus (weight_map f t0) (weight_map 
(wadd f O) t1)) (plus (weight_map g t0) (weight_map (wadd g O) t1)) 
(plus_le_compat (weight_map f t0) (weight_map g t0) (weight_map (wadd f O) 
t1) (weight_map (wadd g O) t1) (H f g H1) (H0 (wadd f O) (wadd g O) (\lambda 
(n: nat).(wadd_le f g H1 O O (le_n O) n)))))))))))))) b)) (\lambda (_: 
F).(\lambda (t0: T).(\lambda (H: ((\forall (f: ((nat \to nat))).(\forall (g: 
((nat \to nat))).(((\forall (n: nat).(le (f n) (g n)))) \to (le (weight_map f 
t0) (weight_map g t0))))))).(\lambda (t1: T).(\lambda (H0: ((\forall (f: 
((nat \to nat))).(\forall (g: ((nat \to nat))).(((\forall (n: nat).(le (f n) 
(g n)))) \to (le (weight_map f t1) (weight_map g t1))))))).(\lambda (f0: 
((nat \to nat))).(\lambda (g: ((nat \to nat))).(\lambda (H1: ((\forall (n: 
nat).(le (f0 n) (g n))))).(lt_le_S (plus (weight_map f0 t0) (weight_map f0 
t1)) (S (plus (weight_map g t0) (weight_map g t1))) (le_lt_n_Sm (plus 
(weight_map f0 t0) (weight_map f0 t1)) (plus (weight_map g t0) (weight_map g 
t1)) (plus_le_compat (weight_map f0 t0) (weight_map g t0) (weight_map f0 t1) 
(weight_map g t1) (H f0 g H1) (H0 f0 g H1)))))))))))) k)) t).

theorem weight_eq:
 \forall (t: T).(\forall (f: ((nat \to nat))).(\forall (g: ((nat \to 
nat))).(((\forall (n: nat).(eq nat (f n) (g n)))) \to (eq nat (weight_map f 
t) (weight_map g t)))))
\def
 \lambda (t: T).(\lambda (f: ((nat \to nat))).(\lambda (g: ((nat \to 
nat))).(\lambda (H: ((\forall (n: nat).(eq nat (f n) (g n))))).(le_antisym 
(weight_map f t) (weight_map g t) (weight_le t f g (\lambda (n: 
nat).(eq_ind_r nat (g n) (\lambda (n0: nat).(le n0 (g n))) (le_n (g n)) (f n) 
(H n)))) (weight_le t g f (\lambda (n: nat).(eq_ind_r nat (g n) (\lambda (n0: 
nat).(le (g n) n0)) (le_n (g n)) (f n) (H n)))))))).

theorem weight_add_O:
 \forall (t: T).(eq nat (weight_map (wadd (\lambda (_: nat).O) O) t) 
(weight_map (\lambda (_: nat).O) t))
\def
 \lambda (t: T).(weight_eq t (wadd (\lambda (_: nat).O) O) (\lambda (_: 
nat).O) (\lambda (n: nat).(wadd_O n))).

theorem weight_add_S:
 \forall (t: T).(\forall (m: nat).(le (weight_map (wadd (\lambda (_: nat).O) 
O) t) (weight_map (wadd (\lambda (_: nat).O) (S m)) t)))
\def
 \lambda (t: T).(\lambda (m: nat).(weight_le t (wadd (\lambda (_: nat).O) O) 
(wadd (\lambda (_: nat).O) (S m)) (\lambda (n: nat).(le_S_n (wadd (\lambda 
(_: nat).O) O n) (wadd (\lambda (_: nat).O) (S m) n) (le_n_S (wadd (\lambda 
(_: nat).O) O n) (wadd (\lambda (_: nat).O) (S m) n) (wadd_le (\lambda (_: 
nat).O) (\lambda (_: nat).O) (\lambda (_: nat).(le_n O)) O (S m) (le_O_n (S 
m)) n)))))).

theorem tlt_trans:
 \forall (v: T).(\forall (u: T).(\forall (t: T).((tlt u v) \to ((tlt v t) \to 
(tlt u t)))))
\def
 \lambda (v: T).(\lambda (u: T).(\lambda (t: T).(\lambda (H: (lt (weight u) 
(weight v))).(\lambda (H0: (lt (weight v) (weight t))).(lt_trans (weight u) 
(weight v) (weight t) H H0))))).

theorem tlt_head_sx:
 \forall (k: K).(\forall (u: T).(\forall (t: T).(tlt u (THead k u t))))
\def
 \lambda (k: K).(K_ind (\lambda (k0: K).(\forall (u: T).(\forall (t: T).(lt 
(weight_map (\lambda (_: nat).O) u) (weight_map (\lambda (_: nat).O) (THead 
k0 u t)))))) (\lambda (b: B).(B_ind (\lambda (b0: B).(\forall (u: T).(\forall 
(t: T).(lt (weight_map (\lambda (_: nat).O) u) (match b0 with [Abbr 
\Rightarrow (S (plus (weight_map (\lambda (_: nat).O) u) (weight_map (wadd 
(\lambda (_: nat).O) (S (weight_map (\lambda (_: nat).O) u))) t))) | Abst 
\Rightarrow (S (plus (weight_map (\lambda (_: nat).O) u) (weight_map (wadd 
(\lambda (_: nat).O) O) t))) | Void \Rightarrow (S (plus (weight_map (\lambda 
(_: nat).O) u) (weight_map (wadd (\lambda (_: nat).O) O) t)))]))))) (\lambda 
(u: T).(\lambda (t: T).(le_S_n (S (weight_map (\lambda (_: nat).O) u)) (S 
(plus (weight_map (\lambda (_: nat).O) u) (weight_map (wadd (\lambda (_: 
nat).O) (S (weight_map (\lambda (_: nat).O) u))) t))) (le_n_S (S (weight_map 
(\lambda (_: nat).O) u)) (S (plus (weight_map (\lambda (_: nat).O) u) 
(weight_map (wadd (\lambda (_: nat).O) (S (weight_map (\lambda (_: nat).O) 
u))) t))) (le_n_S (weight_map (\lambda (_: nat).O) u) (plus (weight_map 
(\lambda (_: nat).O) u) (weight_map (wadd (\lambda (_: nat).O) (S (weight_map 
(\lambda (_: nat).O) u))) t)) (le_plus_l (weight_map (\lambda (_: nat).O) u) 
(weight_map (wadd (\lambda (_: nat).O) (S (weight_map (\lambda (_: nat).O) 
u))) t))))))) (\lambda (u: T).(\lambda (t: T).(le_S_n (S (weight_map (\lambda 
(_: nat).O) u)) (S (plus (weight_map (\lambda (_: nat).O) u) (weight_map 
(wadd (\lambda (_: nat).O) O) t))) (le_n_S (S (weight_map (\lambda (_: 
nat).O) u)) (S (plus (weight_map (\lambda (_: nat).O) u) (weight_map (wadd 
(\lambda (_: nat).O) O) t))) (le_n_S (weight_map (\lambda (_: nat).O) u) 
(plus (weight_map (\lambda (_: nat).O) u) (weight_map (wadd (\lambda (_: 
nat).O) O) t)) (le_plus_l (weight_map (\lambda (_: nat).O) u) (weight_map 
(wadd (\lambda (_: nat).O) O) t))))))) (\lambda (u: T).(\lambda (t: 
T).(le_S_n (S (weight_map (\lambda (_: nat).O) u)) (S (plus (weight_map 
(\lambda (_: nat).O) u) (weight_map (wadd (\lambda (_: nat).O) O) t))) 
(le_n_S (S (weight_map (\lambda (_: nat).O) u)) (S (plus (weight_map (\lambda 
(_: nat).O) u) (weight_map (wadd (\lambda (_: nat).O) O) t))) (le_n_S 
(weight_map (\lambda (_: nat).O) u) (plus (weight_map (\lambda (_: nat).O) u) 
(weight_map (wadd (\lambda (_: nat).O) O) t)) (le_plus_l (weight_map (\lambda 
(_: nat).O) u) (weight_map (wadd (\lambda (_: nat).O) O) t))))))) b)) 
(\lambda (_: F).(\lambda (u: T).(\lambda (t: T).(le_S_n (S (weight_map 
(\lambda (_: nat).O) u)) (S (plus (weight_map (\lambda (_: nat).O) u) 
(weight_map (\lambda (_: nat).O) t))) (le_n_S (S (weight_map (\lambda (_: 
nat).O) u)) (S (plus (weight_map (\lambda (_: nat).O) u) (weight_map (\lambda 
(_: nat).O) t))) (le_n_S (weight_map (\lambda (_: nat).O) u) (plus 
(weight_map (\lambda (_: nat).O) u) (weight_map (\lambda (_: nat).O) t)) 
(le_plus_l (weight_map (\lambda (_: nat).O) u) (weight_map (\lambda (_: 
nat).O) t)))))))) k).

theorem tlt_head_dx:
 \forall (k: K).(\forall (u: T).(\forall (t: T).(tlt t (THead k u t))))
\def
 \lambda (k: K).(K_ind (\lambda (k0: K).(\forall (u: T).(\forall (t: T).(lt 
(weight_map (\lambda (_: nat).O) t) (weight_map (\lambda (_: nat).O) (THead 
k0 u t)))))) (\lambda (b: B).(B_ind (\lambda (b0: B).(\forall (u: T).(\forall 
(t: T).(lt (weight_map (\lambda (_: nat).O) t) (match b0 with [Abbr 
\Rightarrow (S (plus (weight_map (\lambda (_: nat).O) u) (weight_map (wadd 
(\lambda (_: nat).O) (S (weight_map (\lambda (_: nat).O) u))) t))) | Abst 
\Rightarrow (S (plus (weight_map (\lambda (_: nat).O) u) (weight_map (wadd 
(\lambda (_: nat).O) O) t))) | Void \Rightarrow (S (plus (weight_map (\lambda 
(_: nat).O) u) (weight_map (wadd (\lambda (_: nat).O) O) t)))]))))) (\lambda 
(u: T).(\lambda (t: T).(lt_le_trans (weight_map (\lambda (_: nat).O) t) (S 
(weight_map (\lambda (_: nat).O) t)) (S (plus (weight_map (\lambda (_: 
nat).O) u) (weight_map (wadd (\lambda (_: nat).O) (S (weight_map (\lambda (_: 
nat).O) u))) t))) (lt_n_Sn (weight_map (\lambda (_: nat).O) t)) (le_n_S 
(weight_map (\lambda (_: nat).O) t) (plus (weight_map (\lambda (_: nat).O) u) 
(weight_map (wadd (\lambda (_: nat).O) (S (weight_map (\lambda (_: nat).O) 
u))) t)) (le_trans (weight_map (\lambda (_: nat).O) t) (weight_map (wadd 
(\lambda (_: nat).O) (S (weight_map (\lambda (_: nat).O) u))) t) (plus 
(weight_map (\lambda (_: nat).O) u) (weight_map (wadd (\lambda (_: nat).O) (S 
(weight_map (\lambda (_: nat).O) u))) t)) (eq_ind nat (weight_map (wadd 
(\lambda (_: nat).O) O) t) (\lambda (n: nat).(le n (weight_map (wadd (\lambda 
(_: nat).O) (S (weight_map (\lambda (_: nat).O) u))) t))) (weight_add_S t 
(weight_map (\lambda (_: nat).O) u)) (weight_map (\lambda (_: nat).O) t) 
(weight_add_O t)) (le_plus_r (weight_map (\lambda (_: nat).O) u) (weight_map 
(wadd (\lambda (_: nat).O) (S (weight_map (\lambda (_: nat).O) u))) t))))))) 
(\lambda (u: T).(\lambda (t: T).(eq_ind_r nat (weight_map (\lambda (_: 
nat).O) t) (\lambda (n: nat).(lt (weight_map (\lambda (_: nat).O) t) (S (plus 
(weight_map (\lambda (_: nat).O) u) n)))) (le_S_n (S (weight_map (\lambda (_: 
nat).O) t)) (S (plus (weight_map (\lambda (_: nat).O) u) (weight_map (\lambda 
(_: nat).O) t))) (le_n_S (S (weight_map (\lambda (_: nat).O) t)) (S (plus 
(weight_map (\lambda (_: nat).O) u) (weight_map (\lambda (_: nat).O) t))) 
(le_n_S (weight_map (\lambda (_: nat).O) t) (plus (weight_map (\lambda (_: 
nat).O) u) (weight_map (\lambda (_: nat).O) t)) (le_plus_r (weight_map 
(\lambda (_: nat).O) u) (weight_map (\lambda (_: nat).O) t))))) (weight_map 
(wadd (\lambda (_: nat).O) O) t) (weight_add_O t)))) (\lambda (u: T).(\lambda 
(t: T).(eq_ind_r nat (weight_map (\lambda (_: nat).O) t) (\lambda (n: 
nat).(lt (weight_map (\lambda (_: nat).O) t) (S (plus (weight_map (\lambda 
(_: nat).O) u) n)))) (le_S_n (S (weight_map (\lambda (_: nat).O) t)) (S (plus 
(weight_map (\lambda (_: nat).O) u) (weight_map (\lambda (_: nat).O) t))) 
(le_n_S (S (weight_map (\lambda (_: nat).O) t)) (S (plus (weight_map (\lambda 
(_: nat).O) u) (weight_map (\lambda (_: nat).O) t))) (le_n_S (weight_map 
(\lambda (_: nat).O) t) (plus (weight_map (\lambda (_: nat).O) u) (weight_map 
(\lambda (_: nat).O) t)) (le_plus_r (weight_map (\lambda (_: nat).O) u) 
(weight_map (\lambda (_: nat).O) t))))) (weight_map (wadd (\lambda (_: 
nat).O) O) t) (weight_add_O t)))) b)) (\lambda (_: F).(\lambda (u: 
T).(\lambda (t: T).(le_S_n (S (weight_map (\lambda (_: nat).O) t)) (S (plus 
(weight_map (\lambda (_: nat).O) u) (weight_map (\lambda (_: nat).O) t))) 
(le_n_S (S (weight_map (\lambda (_: nat).O) t)) (S (plus (weight_map (\lambda 
(_: nat).O) u) (weight_map (\lambda (_: nat).O) t))) (le_n_S (weight_map 
(\lambda (_: nat).O) t) (plus (weight_map (\lambda (_: nat).O) u) (weight_map 
(\lambda (_: nat).O) t)) (le_plus_r (weight_map (\lambda (_: nat).O) u) 
(weight_map (\lambda (_: nat).O) t)))))))) k).

theorem tlt_wf__q_ind:
 \forall (P: ((T \to Prop))).(((\forall (n: nat).((\lambda (P: ((T \to 
Prop))).(\lambda (n0: nat).(\forall (t: T).((eq nat (weight t) n0) \to (P 
t))))) P n))) \to (\forall (t: T).(P t)))
\def
 let Q \def (\lambda (P: ((T \to Prop))).(\lambda (n: nat).(\forall (t: 
T).((eq nat (weight t) n) \to (P t))))) in (\lambda (P: ((T \to 
Prop))).(\lambda (H: ((\forall (n: nat).(\forall (t: T).((eq nat (weight t) 
n) \to (P t)))))).(\lambda (t: T).(H (weight t) t (refl_equal nat (weight 
t)))))).

theorem tlt_wf_ind:
 \forall (P: ((T \to Prop))).(((\forall (t: T).(((\forall (v: T).((tlt v t) 
\to (P v)))) \to (P t)))) \to (\forall (t: T).(P t)))
\def
 let Q \def (\lambda (P: ((T \to Prop))).(\lambda (n: nat).(\forall (t: 
T).((eq nat (weight t) n) \to (P t))))) in (\lambda (P: ((T \to 
Prop))).(\lambda (H: ((\forall (t: T).(((\forall (v: T).((lt (weight v) 
(weight t)) \to (P v)))) \to (P t))))).(\lambda (t: T).(tlt_wf__q_ind 
(\lambda (t0: T).(P t0)) (\lambda (n: nat).(lt_wf_ind n (Q (\lambda (t0: 
T).(P t0))) (\lambda (n0: nat).(\lambda (H0: ((\forall (m: nat).((lt m n0) 
\to (Q (\lambda (t: T).(P t)) m))))).(\lambda (t0: T).(\lambda (H1: (eq nat 
(weight t0) n0)).(let H2 \def (eq_ind_r nat n0 (\lambda (n: nat).(\forall (m: 
nat).((lt m n) \to (\forall (t: T).((eq nat (weight t) m) \to (P t)))))) H0 
(weight t0) H1) in (H t0 (\lambda (v: T).(\lambda (H3: (lt (weight v) (weight 
t0))).(H2 (weight v) H3 v (refl_equal nat (weight v))))))))))))) t)))).

