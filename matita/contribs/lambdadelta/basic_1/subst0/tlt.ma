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

include "Basic-1/subst0/defs.ma".

include "Basic-1/lift/props.ma".

include "Basic-1/lift/tlt.ma".

theorem subst0_weight_le:
 \forall (u: T).(\forall (t: T).(\forall (z: T).(\forall (d: nat).((subst0 d 
u t z) \to (\forall (f: ((nat \to nat))).(\forall (g: ((nat \to 
nat))).(((\forall (m: nat).(le (f m) (g m)))) \to ((lt (weight_map f (lift (S 
d) O u)) (g d)) \to (le (weight_map f z) (weight_map g t))))))))))
\def
 \lambda (u: T).(\lambda (t: T).(\lambda (z: T).(\lambda (d: nat).(\lambda 
(H: (subst0 d u t z)).(subst0_ind (\lambda (n: nat).(\lambda (t0: T).(\lambda 
(t1: T).(\lambda (t2: T).(\forall (f: ((nat \to nat))).(\forall (g: ((nat \to 
nat))).(((\forall (m: nat).(le (f m) (g m)))) \to ((lt (weight_map f (lift (S 
n) O t0)) (g n)) \to (le (weight_map f t2) (weight_map g t1)))))))))) 
(\lambda (v: T).(\lambda (i: nat).(\lambda (f: ((nat \to nat))).(\lambda (g: 
((nat \to nat))).(\lambda (_: ((\forall (m: nat).(le (f m) (g m))))).(\lambda 
(H1: (lt (weight_map f (lift (S i) O v)) (g i))).(le_S_n (weight_map f (lift 
(S i) O v)) (weight_map g (TLRef i)) (le_S (S (weight_map f (lift (S i) O 
v))) (weight_map g (TLRef i)) H1)))))))) (\lambda (v: T).(\lambda (u2: 
T).(\lambda (u1: T).(\lambda (i: nat).(\lambda (_: (subst0 i v u1 
u2)).(\lambda (H1: ((\forall (f: ((nat \to nat))).(\forall (g: ((nat \to 
nat))).(((\forall (m: nat).(le (f m) (g m)))) \to ((lt (weight_map f (lift (S 
i) O v)) (g i)) \to (le (weight_map f u2) (weight_map g u1)))))))).(\lambda 
(t0: T).(\lambda (k: K).(K_ind (\lambda (k0: K).(\forall (f: ((nat \to 
nat))).(\forall (g: ((nat \to nat))).(((\forall (m: nat).(le (f m) (g m)))) 
\to ((lt (weight_map f (lift (S i) O v)) (g i)) \to (le (weight_map f (THead 
k0 u2 t0)) (weight_map g (THead k0 u1 t0)))))))) (\lambda (b: B).(B_ind 
(\lambda (b0: B).(\forall (f: ((nat \to nat))).(\forall (g: ((nat \to 
nat))).(((\forall (m: nat).(le (f m) (g m)))) \to ((lt (weight_map f (lift (S 
i) O v)) (g i)) \to (le (weight_map f (THead (Bind b0) u2 t0)) (weight_map g 
(THead (Bind b0) u1 t0)))))))) (\lambda (f: ((nat \to nat))).(\lambda (g: 
((nat \to nat))).(\lambda (H2: ((\forall (m: nat).(le (f m) (g 
m))))).(\lambda (H3: (lt (weight_map f (lift (S i) O v)) (g i))).(le_n_S 
(plus (weight_map f u2) (weight_map (wadd f (S (weight_map f u2))) t0)) (plus 
(weight_map g u1) (weight_map (wadd g (S (weight_map g u1))) t0)) 
(le_plus_plus (weight_map f u2) (weight_map g u1) (weight_map (wadd f (S 
(weight_map f u2))) t0) (weight_map (wadd g (S (weight_map g u1))) t0) (H1 f 
g H2 H3) (weight_le t0 (wadd f (S (weight_map f u2))) (wadd g (S (weight_map 
g u1))) (\lambda (n: nat).(wadd_le f g H2 (S (weight_map f u2)) (S 
(weight_map g u1)) (le_n_S (weight_map f u2) (weight_map g u1) (H1 f g H2 
H3)) n))))))))) (\lambda (f: ((nat \to nat))).(\lambda (g: ((nat \to 
nat))).(\lambda (H2: ((\forall (m: nat).(le (f m) (g m))))).(\lambda (H3: (lt 
(weight_map f (lift (S i) O v)) (g i))).(le_n_S (plus (weight_map f u2) 
(weight_map (wadd f O) t0)) (plus (weight_map g u1) (weight_map (wadd g O) 
t0)) (le_plus_plus (weight_map f u2) (weight_map g u1) (weight_map (wadd f O) 
t0) (weight_map (wadd g O) t0) (H1 f g H2 H3) (weight_le t0 (wadd f O) (wadd 
g O) (\lambda (n: nat).(wadd_le f g H2 O O (le_n O) n))))))))) (\lambda (f: 
((nat \to nat))).(\lambda (g: ((nat \to nat))).(\lambda (H2: ((\forall (m: 
nat).(le (f m) (g m))))).(\lambda (H3: (lt (weight_map f (lift (S i) O v)) (g 
i))).(le_n_S (plus (weight_map f u2) (weight_map (wadd f O) t0)) (plus 
(weight_map g u1) (weight_map (wadd g O) t0)) (le_plus_plus (weight_map f u2) 
(weight_map g u1) (weight_map (wadd f O) t0) (weight_map (wadd g O) t0) (H1 f 
g H2 H3) (weight_le t0 (wadd f O) (wadd g O) (\lambda (n: nat).(wadd_le f g 
H2 O O (le_n O) n))))))))) b)) (\lambda (_: F).(\lambda (f0: ((nat \to 
nat))).(\lambda (g: ((nat \to nat))).(\lambda (H2: ((\forall (m: nat).(le (f0 
m) (g m))))).(\lambda (H3: (lt (weight_map f0 (lift (S i) O v)) (g 
i))).(le_n_S (plus (weight_map f0 u2) (weight_map f0 t0)) (plus (weight_map g 
u1) (weight_map g t0)) (le_plus_plus (weight_map f0 u2) (weight_map g u1) 
(weight_map f0 t0) (weight_map g t0) (H1 f0 g H2 H3) (weight_le t0 f0 g 
H2)))))))) k))))))))) (\lambda (k: K).(K_ind (\lambda (k0: K).(\forall (v: 
T).(\forall (t2: T).(\forall (t1: T).(\forall (i: nat).((subst0 (s k0 i) v t1 
t2) \to (((\forall (f: ((nat \to nat))).(\forall (g: ((nat \to 
nat))).(((\forall (m: nat).(le (f m) (g m)))) \to ((lt (weight_map f (lift (S 
(s k0 i)) O v)) (g (s k0 i))) \to (le (weight_map f t2) (weight_map g 
t1))))))) \to (\forall (u0: T).(\forall (f: ((nat \to nat))).(\forall (g: 
((nat \to nat))).(((\forall (m: nat).(le (f m) (g m)))) \to ((lt (weight_map 
f (lift (S i) O v)) (g i)) \to (le (weight_map f (THead k0 u0 t2)) 
(weight_map g (THead k0 u0 t1))))))))))))))) (\lambda (b: B).(B_ind (\lambda 
(b0: B).(\forall (v: T).(\forall (t2: T).(\forall (t1: T).(\forall (i: 
nat).((subst0 (s (Bind b0) i) v t1 t2) \to (((\forall (f: ((nat \to 
nat))).(\forall (g: ((nat \to nat))).(((\forall (m: nat).(le (f m) (g m)))) 
\to ((lt (weight_map f (lift (S (s (Bind b0) i)) O v)) (g (s (Bind b0) i))) 
\to (le (weight_map f t2) (weight_map g t1))))))) \to (\forall (u0: 
T).(\forall (f: ((nat \to nat))).(\forall (g: ((nat \to nat))).(((\forall (m: 
nat).(le (f m) (g m)))) \to ((lt (weight_map f (lift (S i) O v)) (g i)) \to 
(le (weight_map f (THead (Bind b0) u0 t2)) (weight_map g (THead (Bind b0) u0 
t1))))))))))))))) (\lambda (v: T).(\lambda (t2: T).(\lambda (t1: T).(\lambda 
(i: nat).(\lambda (_: (subst0 (S i) v t1 t2)).(\lambda (H1: ((\forall (f: 
((nat \to nat))).(\forall (g: ((nat \to nat))).(((\forall (m: nat).(le (f m) 
(g m)))) \to ((lt (weight_map f (lift (S (S i)) O v)) (g (S i))) \to (le 
(weight_map f t2) (weight_map g t1)))))))).(\lambda (u0: T).(\lambda (f: 
((nat \to nat))).(\lambda (g: ((nat \to nat))).(\lambda (H2: ((\forall (m: 
nat).(le (f m) (g m))))).(\lambda (H3: (lt (weight_map f (lift (S i) O v)) (g 
i))).(le_n_S (plus (weight_map f u0) (weight_map (wadd f (S (weight_map f 
u0))) t2)) (plus (weight_map g u0) (weight_map (wadd g (S (weight_map g u0))) 
t1)) (le_plus_plus (weight_map f u0) (weight_map g u0) (weight_map (wadd f (S 
(weight_map f u0))) t2) (weight_map (wadd g (S (weight_map g u0))) t1) 
(weight_le u0 f g H2) (H1 (wadd f (S (weight_map f u0))) (wadd g (S 
(weight_map g u0))) (\lambda (m: nat).(wadd_le f g H2 (S (weight_map f u0)) 
(S (weight_map g u0)) (le_n_S (weight_map f u0) (weight_map g u0) (weight_le 
u0 f g H2)) m)) (eq_ind nat (weight_map f (lift (S i) O v)) (\lambda (n: 
nat).(lt n (g i))) H3 (weight_map (wadd f (S (weight_map f u0))) (lift (S (S 
i)) O v)) (lift_weight_add_O (S (weight_map f u0)) v (S i) f)))))))))))))))) 
(\lambda (v: T).(\lambda (t2: T).(\lambda (t1: T).(\lambda (i: nat).(\lambda 
(_: (subst0 (S i) v t1 t2)).(\lambda (H1: ((\forall (f: ((nat \to 
nat))).(\forall (g: ((nat \to nat))).(((\forall (m: nat).(le (f m) (g m)))) 
\to ((lt (weight_map f (lift (S (S i)) O v)) (g (S i))) \to (le (weight_map f 
t2) (weight_map g t1)))))))).(\lambda (u0: T).(\lambda (f: ((nat \to 
nat))).(\lambda (g: ((nat \to nat))).(\lambda (H2: ((\forall (m: nat).(le (f 
m) (g m))))).(\lambda (H3: (lt (weight_map f (lift (S i) O v)) (g 
i))).(le_n_S (plus (weight_map f u0) (weight_map (wadd f O) t2)) (plus 
(weight_map g u0) (weight_map (wadd g O) t1)) (le_plus_plus (weight_map f u0) 
(weight_map g u0) (weight_map (wadd f O) t2) (weight_map (wadd g O) t1) 
(weight_le u0 f g H2) (H1 (wadd f O) (wadd g O) (\lambda (m: nat).(wadd_le f 
g H2 O O (le_n O) m)) (eq_ind nat (weight_map f (lift (S i) O v)) (\lambda 
(n: nat).(lt n (g i))) H3 (weight_map (wadd f O) (lift (S (S i)) O v)) 
(lift_weight_add_O O v (S i) f)))))))))))))))) (\lambda (v: T).(\lambda (t2: 
T).(\lambda (t1: T).(\lambda (i: nat).(\lambda (_: (subst0 (S i) v t1 
t2)).(\lambda (H1: ((\forall (f: ((nat \to nat))).(\forall (g: ((nat \to 
nat))).(((\forall (m: nat).(le (f m) (g m)))) \to ((lt (weight_map f (lift (S 
(S i)) O v)) (g (S i))) \to (le (weight_map f t2) (weight_map g 
t1)))))))).(\lambda (u0: T).(\lambda (f: ((nat \to nat))).(\lambda (g: ((nat 
\to nat))).(\lambda (H2: ((\forall (m: nat).(le (f m) (g m))))).(\lambda (H3: 
(lt (weight_map f (lift (S i) O v)) (g i))).(le_n_S (plus (weight_map f u0) 
(weight_map (wadd f O) t2)) (plus (weight_map g u0) (weight_map (wadd g O) 
t1)) (le_plus_plus (weight_map f u0) (weight_map g u0) (weight_map (wadd f O) 
t2) (weight_map (wadd g O) t1) (weight_le u0 f g H2) (H1 (wadd f O) (wadd g 
O) (\lambda (m: nat).(wadd_le f g H2 O O (le_n O) m)) (eq_ind nat (weight_map 
f (lift (S i) O v)) (\lambda (n: nat).(lt n (g i))) H3 (weight_map (wadd f O) 
(lift (S (S i)) O v)) (lift_weight_add_O O v (S i) f)))))))))))))))) b)) 
(\lambda (_: F).(\lambda (v: T).(\lambda (t2: T).(\lambda (t1: T).(\lambda 
(i: nat).(\lambda (_: (subst0 i v t1 t2)).(\lambda (H1: ((\forall (f0: ((nat 
\to nat))).(\forall (g: ((nat \to nat))).(((\forall (m: nat).(le (f0 m) (g 
m)))) \to ((lt (weight_map f0 (lift (S i) O v)) (g i)) \to (le (weight_map f0 
t2) (weight_map g t1)))))))).(\lambda (u0: T).(\lambda (f0: ((nat \to 
nat))).(\lambda (g: ((nat \to nat))).(\lambda (H2: ((\forall (m: nat).(le (f0 
m) (g m))))).(\lambda (H3: (lt (weight_map f0 (lift (S i) O v)) (g 
i))).(le_n_S (plus (weight_map f0 u0) (weight_map f0 t2)) (plus (weight_map g 
u0) (weight_map g t1)) (le_plus_plus (weight_map f0 u0) (weight_map g u0) 
(weight_map f0 t2) (weight_map g t1) (weight_le u0 f0 g H2) (H1 f0 g H2 
H3))))))))))))))) k)) (\lambda (v: T).(\lambda (u1: T).(\lambda (u2: 
T).(\lambda (i: nat).(\lambda (_: (subst0 i v u1 u2)).(\lambda (H1: ((\forall 
(f: ((nat \to nat))).(\forall (g: ((nat \to nat))).(((\forall (m: nat).(le (f 
m) (g m)))) \to ((lt (weight_map f (lift (S i) O v)) (g i)) \to (le 
(weight_map f u2) (weight_map g u1)))))))).(\lambda (k: K).(K_ind (\lambda 
(k0: K).(\forall (t1: T).(\forall (t2: T).((subst0 (s k0 i) v t1 t2) \to 
(((\forall (f: ((nat \to nat))).(\forall (g: ((nat \to nat))).(((\forall (m: 
nat).(le (f m) (g m)))) \to ((lt (weight_map f (lift (S (s k0 i)) O v)) (g (s 
k0 i))) \to (le (weight_map f t2) (weight_map g t1))))))) \to (\forall (f: 
((nat \to nat))).(\forall (g: ((nat \to nat))).(((\forall (m: nat).(le (f m) 
(g m)))) \to ((lt (weight_map f (lift (S i) O v)) (g i)) \to (le (weight_map 
f (THead k0 u2 t2)) (weight_map g (THead k0 u1 t1)))))))))))) (\lambda (b: 
B).(B_ind (\lambda (b0: B).(\forall (t1: T).(\forall (t2: T).((subst0 (s 
(Bind b0) i) v t1 t2) \to (((\forall (f: ((nat \to nat))).(\forall (g: ((nat 
\to nat))).(((\forall (m: nat).(le (f m) (g m)))) \to ((lt (weight_map f 
(lift (S (s (Bind b0) i)) O v)) (g (s (Bind b0) i))) \to (le (weight_map f 
t2) (weight_map g t1))))))) \to (\forall (f: ((nat \to nat))).(\forall (g: 
((nat \to nat))).(((\forall (m: nat).(le (f m) (g m)))) \to ((lt (weight_map 
f (lift (S i) O v)) (g i)) \to (le (weight_map f (THead (Bind b0) u2 t2)) 
(weight_map g (THead (Bind b0) u1 t1)))))))))))) (\lambda (t1: T).(\lambda 
(t2: T).(\lambda (_: (subst0 (S i) v t1 t2)).(\lambda (H3: ((\forall (f: 
((nat \to nat))).(\forall (g: ((nat \to nat))).(((\forall (m: nat).(le (f m) 
(g m)))) \to ((lt (weight_map f (lift (S (S i)) O v)) (g (S i))) \to (le 
(weight_map f t2) (weight_map g t1)))))))).(\lambda (f: ((nat \to 
nat))).(\lambda (g: ((nat \to nat))).(\lambda (H4: ((\forall (m: nat).(le (f 
m) (g m))))).(\lambda (H5: (lt (weight_map f (lift (S i) O v)) (g 
i))).(le_n_S (plus (weight_map f u2) (weight_map (wadd f (S (weight_map f 
u2))) t2)) (plus (weight_map g u1) (weight_map (wadd g (S (weight_map g u1))) 
t1)) (le_plus_plus (weight_map f u2) (weight_map g u1) (weight_map (wadd f (S 
(weight_map f u2))) t2) (weight_map (wadd g (S (weight_map g u1))) t1) (H1 f 
g H4 H5) (H3 (wadd f (S (weight_map f u2))) (wadd g (S (weight_map g u1))) 
(\lambda (m: nat).(wadd_le f g H4 (S (weight_map f u2)) (S (weight_map g u1)) 
(le_n_S (weight_map f u2) (weight_map g u1) (H1 f g H4 H5)) m)) (eq_ind nat 
(weight_map f (lift (S i) O v)) (\lambda (n: nat).(lt n (g i))) H5 
(weight_map (wadd f (S (weight_map f u2))) (lift (S (S i)) O v)) 
(lift_weight_add_O (S (weight_map f u2)) v (S i) f))))))))))))) (\lambda (t1: 
T).(\lambda (t2: T).(\lambda (_: (subst0 (S i) v t1 t2)).(\lambda (H3: 
((\forall (f: ((nat \to nat))).(\forall (g: ((nat \to nat))).(((\forall (m: 
nat).(le (f m) (g m)))) \to ((lt (weight_map f (lift (S (S i)) O v)) (g (S 
i))) \to (le (weight_map f t2) (weight_map g t1)))))))).(\lambda (f: ((nat 
\to nat))).(\lambda (g: ((nat \to nat))).(\lambda (H4: ((\forall (m: nat).(le 
(f m) (g m))))).(\lambda (H5: (lt (weight_map f (lift (S i) O v)) (g 
i))).(le_n_S (plus (weight_map f u2) (weight_map (wadd f O) t2)) (plus 
(weight_map g u1) (weight_map (wadd g O) t1)) (le_plus_plus (weight_map f u2) 
(weight_map g u1) (weight_map (wadd f O) t2) (weight_map (wadd g O) t1) (H1 f 
g H4 H5) (H3 (wadd f O) (wadd g O) (\lambda (m: nat).(wadd_le f g H4 O O 
(le_n O) m)) (eq_ind nat (weight_map f (lift (S i) O v)) (\lambda (n: 
nat).(lt n (g i))) H5 (weight_map (wadd f O) (lift (S (S i)) O v)) 
(lift_weight_add_O O v (S i) f))))))))))))) (\lambda (t1: T).(\lambda (t2: 
T).(\lambda (_: (subst0 (S i) v t1 t2)).(\lambda (H3: ((\forall (f: ((nat \to 
nat))).(\forall (g: ((nat \to nat))).(((\forall (m: nat).(le (f m) (g m)))) 
\to ((lt (weight_map f (lift (S (S i)) O v)) (g (S i))) \to (le (weight_map f 
t2) (weight_map g t1)))))))).(\lambda (f: ((nat \to nat))).(\lambda (g: ((nat 
\to nat))).(\lambda (H4: ((\forall (m: nat).(le (f m) (g m))))).(\lambda (H5: 
(lt (weight_map f (lift (S i) O v)) (g i))).(le_n_S (plus (weight_map f u2) 
(weight_map (wadd f O) t2)) (plus (weight_map g u1) (weight_map (wadd g O) 
t1)) (le_plus_plus (weight_map f u2) (weight_map g u1) (weight_map (wadd f O) 
t2) (weight_map (wadd g O) t1) (H1 f g H4 H5) (H3 (wadd f O) (wadd g O) 
(\lambda (m: nat).(wadd_le f g H4 O O (le_n O) m)) (eq_ind nat (weight_map f 
(lift (S i) O v)) (\lambda (n: nat).(lt n (g i))) H5 (weight_map (wadd f O) 
(lift (S (S i)) O v)) (lift_weight_add_O O v (S i) f))))))))))))) b)) 
(\lambda (_: F).(\lambda (t1: T).(\lambda (t2: T).(\lambda (_: (subst0 i v t1 
t2)).(\lambda (H3: ((\forall (f0: ((nat \to nat))).(\forall (g: ((nat \to 
nat))).(((\forall (m: nat).(le (f0 m) (g m)))) \to ((lt (weight_map f0 (lift 
(S i) O v)) (g i)) \to (le (weight_map f0 t2) (weight_map g 
t1)))))))).(\lambda (f0: ((nat \to nat))).(\lambda (g: ((nat \to 
nat))).(\lambda (H4: ((\forall (m: nat).(le (f0 m) (g m))))).(\lambda (H5: 
(lt (weight_map f0 (lift (S i) O v)) (g i))).(le_n_S (plus (weight_map f0 u2) 
(weight_map f0 t2)) (plus (weight_map g u1) (weight_map g t1)) (le_plus_plus 
(weight_map f0 u2) (weight_map g u1) (weight_map f0 t2) (weight_map g t1) (H1 
f0 g H4 H5) (H3 f0 g H4 H5)))))))))))) k)))))))) d u t z H))))).
(* COMMENTS
Initial nodes: 4101
END *)

theorem subst0_weight_lt:
 \forall (u: T).(\forall (t: T).(\forall (z: T).(\forall (d: nat).((subst0 d 
u t z) \to (\forall (f: ((nat \to nat))).(\forall (g: ((nat \to 
nat))).(((\forall (m: nat).(le (f m) (g m)))) \to ((lt (weight_map f (lift (S 
d) O u)) (g d)) \to (lt (weight_map f z) (weight_map g t))))))))))
\def
 \lambda (u: T).(\lambda (t: T).(\lambda (z: T).(\lambda (d: nat).(\lambda 
(H: (subst0 d u t z)).(subst0_ind (\lambda (n: nat).(\lambda (t0: T).(\lambda 
(t1: T).(\lambda (t2: T).(\forall (f: ((nat \to nat))).(\forall (g: ((nat \to 
nat))).(((\forall (m: nat).(le (f m) (g m)))) \to ((lt (weight_map f (lift (S 
n) O t0)) (g n)) \to (lt (weight_map f t2) (weight_map g t1)))))))))) 
(\lambda (v: T).(\lambda (i: nat).(\lambda (f: ((nat \to nat))).(\lambda (g: 
((nat \to nat))).(\lambda (_: ((\forall (m: nat).(le (f m) (g m))))).(\lambda 
(H1: (lt (weight_map f (lift (S i) O v)) (g i))).H1)))))) (\lambda (v: 
T).(\lambda (u2: T).(\lambda (u1: T).(\lambda (i: nat).(\lambda (_: (subst0 i 
v u1 u2)).(\lambda (H1: ((\forall (f: ((nat \to nat))).(\forall (g: ((nat \to 
nat))).(((\forall (m: nat).(le (f m) (g m)))) \to ((lt (weight_map f (lift (S 
i) O v)) (g i)) \to (lt (weight_map f u2) (weight_map g u1)))))))).(\lambda 
(t0: T).(\lambda (k: K).(K_ind (\lambda (k0: K).(\forall (f: ((nat \to 
nat))).(\forall (g: ((nat \to nat))).(((\forall (m: nat).(le (f m) (g m)))) 
\to ((lt (weight_map f (lift (S i) O v)) (g i)) \to (lt (weight_map f (THead 
k0 u2 t0)) (weight_map g (THead k0 u1 t0)))))))) (\lambda (b: B).(B_ind 
(\lambda (b0: B).(\forall (f: ((nat \to nat))).(\forall (g: ((nat \to 
nat))).(((\forall (m: nat).(le (f m) (g m)))) \to ((lt (weight_map f (lift (S 
i) O v)) (g i)) \to (lt (weight_map f (THead (Bind b0) u2 t0)) (weight_map g 
(THead (Bind b0) u1 t0)))))))) (\lambda (f: ((nat \to nat))).(\lambda (g: 
((nat \to nat))).(\lambda (H2: ((\forall (m: nat).(le (f m) (g 
m))))).(\lambda (H3: (lt (weight_map f (lift (S i) O v)) (g i))).(lt_n_S 
(plus (weight_map f u2) (weight_map (wadd f (S (weight_map f u2))) t0)) (plus 
(weight_map g u1) (weight_map (wadd g (S (weight_map g u1))) t0)) 
(lt_le_plus_plus (weight_map f u2) (weight_map g u1) (weight_map (wadd f (S 
(weight_map f u2))) t0) (weight_map (wadd g (S (weight_map g u1))) t0) (H1 f 
g H2 H3) (weight_le t0 (wadd f (S (weight_map f u2))) (wadd g (S (weight_map 
g u1))) (\lambda (n: nat).(wadd_lt f g H2 (S (weight_map f u2)) (S 
(weight_map g u1)) (lt_n_S (weight_map f u2) (weight_map g u1) (H1 f g H2 
H3)) n))))))))) (\lambda (f: ((nat \to nat))).(\lambda (g: ((nat \to 
nat))).(\lambda (H2: ((\forall (m: nat).(le (f m) (g m))))).(\lambda (H3: (lt 
(weight_map f (lift (S i) O v)) (g i))).(lt_n_S (plus (weight_map f u2) 
(weight_map (wadd f O) t0)) (plus (weight_map g u1) (weight_map (wadd g O) 
t0)) (lt_le_plus_plus (weight_map f u2) (weight_map g u1) (weight_map (wadd f 
O) t0) (weight_map (wadd g O) t0) (H1 f g H2 H3) (weight_le t0 (wadd f O) 
(wadd g O) (\lambda (n: nat).(le_S_n (wadd f O n) (wadd g O n) (le_n_S (wadd 
f O n) (wadd g O n) (wadd_le f g H2 O O (le_n O) n))))))))))) (\lambda (f: 
((nat \to nat))).(\lambda (g: ((nat \to nat))).(\lambda (H2: ((\forall (m: 
nat).(le (f m) (g m))))).(\lambda (H3: (lt (weight_map f (lift (S i) O v)) (g 
i))).(lt_n_S (plus (weight_map f u2) (weight_map (wadd f O) t0)) (plus 
(weight_map g u1) (weight_map (wadd g O) t0)) (lt_le_plus_plus (weight_map f 
u2) (weight_map g u1) (weight_map (wadd f O) t0) (weight_map (wadd g O) t0) 
(H1 f g H2 H3) (weight_le t0 (wadd f O) (wadd g O) (\lambda (n: nat).(le_S_n 
(wadd f O n) (wadd g O n) (le_n_S (wadd f O n) (wadd g O n) (wadd_le f g H2 O 
O (le_n O) n))))))))))) b)) (\lambda (_: F).(\lambda (f0: ((nat \to 
nat))).(\lambda (g: ((nat \to nat))).(\lambda (H2: ((\forall (m: nat).(le (f0 
m) (g m))))).(\lambda (H3: (lt (weight_map f0 (lift (S i) O v)) (g 
i))).(lt_n_S (plus (weight_map f0 u2) (weight_map f0 t0)) (plus (weight_map g 
u1) (weight_map g t0)) (lt_le_plus_plus (weight_map f0 u2) (weight_map g u1) 
(weight_map f0 t0) (weight_map g t0) (H1 f0 g H2 H3) (weight_le t0 f0 g 
H2)))))))) k))))))))) (\lambda (k: K).(K_ind (\lambda (k0: K).(\forall (v: 
T).(\forall (t2: T).(\forall (t1: T).(\forall (i: nat).((subst0 (s k0 i) v t1 
t2) \to (((\forall (f: ((nat \to nat))).(\forall (g: ((nat \to 
nat))).(((\forall (m: nat).(le (f m) (g m)))) \to ((lt (weight_map f (lift (S 
(s k0 i)) O v)) (g (s k0 i))) \to (lt (weight_map f t2) (weight_map g 
t1))))))) \to (\forall (u0: T).(\forall (f: ((nat \to nat))).(\forall (g: 
((nat \to nat))).(((\forall (m: nat).(le (f m) (g m)))) \to ((lt (weight_map 
f (lift (S i) O v)) (g i)) \to (lt (weight_map f (THead k0 u0 t2)) 
(weight_map g (THead k0 u0 t1))))))))))))))) (\lambda (b: B).(B_ind (\lambda 
(b0: B).(\forall (v: T).(\forall (t2: T).(\forall (t1: T).(\forall (i: 
nat).((subst0 (s (Bind b0) i) v t1 t2) \to (((\forall (f: ((nat \to 
nat))).(\forall (g: ((nat \to nat))).(((\forall (m: nat).(le (f m) (g m)))) 
\to ((lt (weight_map f (lift (S (s (Bind b0) i)) O v)) (g (s (Bind b0) i))) 
\to (lt (weight_map f t2) (weight_map g t1))))))) \to (\forall (u0: 
T).(\forall (f: ((nat \to nat))).(\forall (g: ((nat \to nat))).(((\forall (m: 
nat).(le (f m) (g m)))) \to ((lt (weight_map f (lift (S i) O v)) (g i)) \to 
(lt (weight_map f (THead (Bind b0) u0 t2)) (weight_map g (THead (Bind b0) u0 
t1))))))))))))))) (\lambda (v: T).(\lambda (t2: T).(\lambda (t1: T).(\lambda 
(i: nat).(\lambda (_: (subst0 (S i) v t1 t2)).(\lambda (H1: ((\forall (f: 
((nat \to nat))).(\forall (g: ((nat \to nat))).(((\forall (m: nat).(le (f m) 
(g m)))) \to ((lt (weight_map f (lift (S (S i)) O v)) (g (S i))) \to (lt 
(weight_map f t2) (weight_map g t1)))))))).(\lambda (u0: T).(\lambda (f: 
((nat \to nat))).(\lambda (g: ((nat \to nat))).(\lambda (H2: ((\forall (m: 
nat).(le (f m) (g m))))).(\lambda (H3: (lt (weight_map f (lift (S i) O v)) (g 
i))).(lt_n_S (plus (weight_map f u0) (weight_map (wadd f (S (weight_map f 
u0))) t2)) (plus (weight_map g u0) (weight_map (wadd g (S (weight_map g u0))) 
t1)) (le_lt_plus_plus (weight_map f u0) (weight_map g u0) (weight_map (wadd f 
(S (weight_map f u0))) t2) (weight_map (wadd g (S (weight_map g u0))) t1) 
(weight_le u0 f g H2) (H1 (wadd f (S (weight_map f u0))) (wadd g (S 
(weight_map g u0))) (\lambda (m: nat).(wadd_le f g H2 (S (weight_map f u0)) 
(S (weight_map g u0)) (le_n_S (weight_map f u0) (weight_map g u0) (weight_le 
u0 f g H2)) m)) (eq_ind nat (weight_map f (lift (S i) O v)) (\lambda (n: 
nat).(lt n (g i))) H3 (weight_map (wadd f (S (weight_map f u0))) (lift (S (S 
i)) O v)) (lift_weight_add_O (S (weight_map f u0)) v (S i) f)))))))))))))))) 
(\lambda (v: T).(\lambda (t2: T).(\lambda (t1: T).(\lambda (i: nat).(\lambda 
(_: (subst0 (S i) v t1 t2)).(\lambda (H1: ((\forall (f: ((nat \to 
nat))).(\forall (g: ((nat \to nat))).(((\forall (m: nat).(le (f m) (g m)))) 
\to ((lt (weight_map f (lift (S (S i)) O v)) (g (S i))) \to (lt (weight_map f 
t2) (weight_map g t1)))))))).(\lambda (u0: T).(\lambda (f: ((nat \to 
nat))).(\lambda (g: ((nat \to nat))).(\lambda (H2: ((\forall (m: nat).(le (f 
m) (g m))))).(\lambda (H3: (lt (weight_map f (lift (S i) O v)) (g 
i))).(lt_n_S (plus (weight_map f u0) (weight_map (wadd f O) t2)) (plus 
(weight_map g u0) (weight_map (wadd g O) t1)) (le_lt_plus_plus (weight_map f 
u0) (weight_map g u0) (weight_map (wadd f O) t2) (weight_map (wadd g O) t1) 
(weight_le u0 f g H2) (H1 (wadd f O) (wadd g O) (\lambda (m: nat).(wadd_le f 
g H2 O O (le_n O) m)) (eq_ind nat (weight_map f (lift (S i) O v)) (\lambda 
(n: nat).(lt n (g i))) H3 (weight_map (wadd f O) (lift (S (S i)) O v)) 
(lift_weight_add_O O v (S i) f)))))))))))))))) (\lambda (v: T).(\lambda (t2: 
T).(\lambda (t1: T).(\lambda (i: nat).(\lambda (_: (subst0 (S i) v t1 
t2)).(\lambda (H1: ((\forall (f: ((nat \to nat))).(\forall (g: ((nat \to 
nat))).(((\forall (m: nat).(le (f m) (g m)))) \to ((lt (weight_map f (lift (S 
(S i)) O v)) (g (S i))) \to (lt (weight_map f t2) (weight_map g 
t1)))))))).(\lambda (u0: T).(\lambda (f: ((nat \to nat))).(\lambda (g: ((nat 
\to nat))).(\lambda (H2: ((\forall (m: nat).(le (f m) (g m))))).(\lambda (H3: 
(lt (weight_map f (lift (S i) O v)) (g i))).(lt_n_S (plus (weight_map f u0) 
(weight_map (wadd f O) t2)) (plus (weight_map g u0) (weight_map (wadd g O) 
t1)) (le_lt_plus_plus (weight_map f u0) (weight_map g u0) (weight_map (wadd f 
O) t2) (weight_map (wadd g O) t1) (weight_le u0 f g H2) (H1 (wadd f O) (wadd 
g O) (\lambda (m: nat).(wadd_le f g H2 O O (le_n O) m)) (eq_ind nat 
(weight_map f (lift (S i) O v)) (\lambda (n: nat).(lt n (g i))) H3 
(weight_map (wadd f O) (lift (S (S i)) O v)) (lift_weight_add_O O v (S i) 
f)))))))))))))))) b)) (\lambda (_: F).(\lambda (v: T).(\lambda (t2: 
T).(\lambda (t1: T).(\lambda (i: nat).(\lambda (_: (subst0 i v t1 
t2)).(\lambda (H1: ((\forall (f0: ((nat \to nat))).(\forall (g: ((nat \to 
nat))).(((\forall (m: nat).(le (f0 m) (g m)))) \to ((lt (weight_map f0 (lift 
(S i) O v)) (g i)) \to (lt (weight_map f0 t2) (weight_map g 
t1)))))))).(\lambda (u0: T).(\lambda (f0: ((nat \to nat))).(\lambda (g: ((nat 
\to nat))).(\lambda (H2: ((\forall (m: nat).(le (f0 m) (g m))))).(\lambda 
(H3: (lt (weight_map f0 (lift (S i) O v)) (g i))).(lt_n_S (plus (weight_map 
f0 u0) (weight_map f0 t2)) (plus (weight_map g u0) (weight_map g t1)) 
(le_lt_plus_plus (weight_map f0 u0) (weight_map g u0) (weight_map f0 t2) 
(weight_map g t1) (weight_le u0 f0 g H2) (H1 f0 g H2 H3))))))))))))))) k)) 
(\lambda (v: T).(\lambda (u1: T).(\lambda (u2: T).(\lambda (i: nat).(\lambda 
(_: (subst0 i v u1 u2)).(\lambda (H1: ((\forall (f: ((nat \to nat))).(\forall 
(g: ((nat \to nat))).(((\forall (m: nat).(le (f m) (g m)))) \to ((lt 
(weight_map f (lift (S i) O v)) (g i)) \to (lt (weight_map f u2) (weight_map 
g u1)))))))).(\lambda (k: K).(K_ind (\lambda (k0: K).(\forall (t1: 
T).(\forall (t2: T).((subst0 (s k0 i) v t1 t2) \to (((\forall (f: ((nat \to 
nat))).(\forall (g: ((nat \to nat))).(((\forall (m: nat).(le (f m) (g m)))) 
\to ((lt (weight_map f (lift (S (s k0 i)) O v)) (g (s k0 i))) \to (lt 
(weight_map f t2) (weight_map g t1))))))) \to (\forall (f: ((nat \to 
nat))).(\forall (g: ((nat \to nat))).(((\forall (m: nat).(le (f m) (g m)))) 
\to ((lt (weight_map f (lift (S i) O v)) (g i)) \to (lt (weight_map f (THead 
k0 u2 t2)) (weight_map g (THead k0 u1 t1)))))))))))) (\lambda (b: B).(B_ind 
(\lambda (b0: B).(\forall (t1: T).(\forall (t2: T).((subst0 (s (Bind b0) i) v 
t1 t2) \to (((\forall (f: ((nat \to nat))).(\forall (g: ((nat \to 
nat))).(((\forall (m: nat).(le (f m) (g m)))) \to ((lt (weight_map f (lift (S 
(s (Bind b0) i)) O v)) (g (s (Bind b0) i))) \to (lt (weight_map f t2) 
(weight_map g t1))))))) \to (\forall (f: ((nat \to nat))).(\forall (g: ((nat 
\to nat))).(((\forall (m: nat).(le (f m) (g m)))) \to ((lt (weight_map f 
(lift (S i) O v)) (g i)) \to (lt (weight_map f (THead (Bind b0) u2 t2)) 
(weight_map g (THead (Bind b0) u1 t1)))))))))))) (\lambda (t1: T).(\lambda 
(t2: T).(\lambda (H2: (subst0 (S i) v t1 t2)).(\lambda (_: ((\forall (f: 
((nat \to nat))).(\forall (g: ((nat \to nat))).(((\forall (m: nat).(le (f m) 
(g m)))) \to ((lt (weight_map f (lift (S (S i)) O v)) (g (S i))) \to (lt 
(weight_map f t2) (weight_map g t1)))))))).(\lambda (f: ((nat \to 
nat))).(\lambda (g: ((nat \to nat))).(\lambda (H4: ((\forall (m: nat).(le (f 
m) (g m))))).(\lambda (H5: (lt (weight_map f (lift (S i) O v)) (g 
i))).(lt_n_S (plus (weight_map f u2) (weight_map (wadd f (S (weight_map f 
u2))) t2)) (plus (weight_map g u1) (weight_map (wadd g (S (weight_map g u1))) 
t1)) (lt_le_plus_plus (weight_map f u2) (weight_map g u1) (weight_map (wadd f 
(S (weight_map f u2))) t2) (weight_map (wadd g (S (weight_map g u1))) t1) (H1 
f g H4 H5) (subst0_weight_le v t1 t2 (S i) H2 (wadd f (S (weight_map f u2))) 
(wadd g (S (weight_map g u1))) (\lambda (m: nat).(wadd_lt f g H4 (S 
(weight_map f u2)) (S (weight_map g u1)) (lt_n_S (weight_map f u2) 
(weight_map g u1) (H1 f g H4 H5)) m)) (eq_ind nat (weight_map f (lift (S i) O 
v)) (\lambda (n: nat).(lt n (g i))) H5 (weight_map (wadd f (S (weight_map f 
u2))) (lift (S (S i)) O v)) (lift_weight_add_O (S (weight_map f u2)) v (S i) 
f))))))))))))) (\lambda (t1: T).(\lambda (t2: T).(\lambda (_: (subst0 (S i) v 
t1 t2)).(\lambda (H3: ((\forall (f: ((nat \to nat))).(\forall (g: ((nat \to 
nat))).(((\forall (m: nat).(le (f m) (g m)))) \to ((lt (weight_map f (lift (S 
(S i)) O v)) (g (S i))) \to (lt (weight_map f t2) (weight_map g 
t1)))))))).(\lambda (f: ((nat \to nat))).(\lambda (g: ((nat \to 
nat))).(\lambda (H4: ((\forall (m: nat).(le (f m) (g m))))).(\lambda (H5: (lt 
(weight_map f (lift (S i) O v)) (g i))).(lt_n_S (plus (weight_map f u2) 
(weight_map (wadd f O) t2)) (plus (weight_map g u1) (weight_map (wadd g O) 
t1)) (lt_plus_plus (weight_map f u2) (weight_map g u1) (weight_map (wadd f O) 
t2) (weight_map (wadd g O) t1) (H1 f g H4 H5) (H3 (wadd f O) (wadd g O) 
(\lambda (m: nat).(le_S_n (wadd f O m) (wadd g O m) (le_n_S (wadd f O m) 
(wadd g O m) (wadd_le f g H4 O O (le_n O) m)))) (eq_ind nat (weight_map f 
(lift (S i) O v)) (\lambda (n: nat).(lt n (g i))) H5 (weight_map (wadd f O) 
(lift (S (S i)) O v)) (lift_weight_add_O O v (S i) f))))))))))))) (\lambda 
(t1: T).(\lambda (t2: T).(\lambda (_: (subst0 (S i) v t1 t2)).(\lambda (H3: 
((\forall (f: ((nat \to nat))).(\forall (g: ((nat \to nat))).(((\forall (m: 
nat).(le (f m) (g m)))) \to ((lt (weight_map f (lift (S (S i)) O v)) (g (S 
i))) \to (lt (weight_map f t2) (weight_map g t1)))))))).(\lambda (f: ((nat 
\to nat))).(\lambda (g: ((nat \to nat))).(\lambda (H4: ((\forall (m: nat).(le 
(f m) (g m))))).(\lambda (H5: (lt (weight_map f (lift (S i) O v)) (g 
i))).(lt_n_S (plus (weight_map f u2) (weight_map (wadd f O) t2)) (plus 
(weight_map g u1) (weight_map (wadd g O) t1)) (lt_plus_plus (weight_map f u2) 
(weight_map g u1) (weight_map (wadd f O) t2) (weight_map (wadd g O) t1) (H1 f 
g H4 H5) (H3 (wadd f O) (wadd g O) (\lambda (m: nat).(le_S_n (wadd f O m) 
(wadd g O m) (le_n_S (wadd f O m) (wadd g O m) (wadd_le f g H4 O O (le_n O) 
m)))) (eq_ind nat (weight_map f (lift (S i) O v)) (\lambda (n: nat).(lt n (g 
i))) H5 (weight_map (wadd f O) (lift (S (S i)) O v)) (lift_weight_add_O O v 
(S i) f))))))))))))) b)) (\lambda (_: F).(\lambda (t1: T).(\lambda (t2: 
T).(\lambda (_: (subst0 i v t1 t2)).(\lambda (H3: ((\forall (f0: ((nat \to 
nat))).(\forall (g: ((nat \to nat))).(((\forall (m: nat).(le (f0 m) (g m)))) 
\to ((lt (weight_map f0 (lift (S i) O v)) (g i)) \to (lt (weight_map f0 t2) 
(weight_map g t1)))))))).(\lambda (f0: ((nat \to nat))).(\lambda (g: ((nat 
\to nat))).(\lambda (H4: ((\forall (m: nat).(le (f0 m) (g m))))).(\lambda 
(H5: (lt (weight_map f0 (lift (S i) O v)) (g i))).(lt_n_S (plus (weight_map 
f0 u2) (weight_map f0 t2)) (plus (weight_map g u1) (weight_map g t1)) 
(lt_plus_plus (weight_map f0 u2) (weight_map g u1) (weight_map f0 t2) 
(weight_map g t1) (H1 f0 g H4 H5) (H3 f0 g H4 H5)))))))))))) k)))))))) d u t 
z H))))).
(* COMMENTS
Initial nodes: 4207
END *)

theorem subst0_tlt_head:
 \forall (u: T).(\forall (t: T).(\forall (z: T).((subst0 O u t z) \to (tlt 
(THead (Bind Abbr) u z) (THead (Bind Abbr) u t)))))
\def
 \lambda (u: T).(\lambda (t: T).(\lambda (z: T).(\lambda (H: (subst0 O u t 
z)).(lt_n_S (plus (weight_map (\lambda (_: nat).O) u) (weight_map (wadd 
(\lambda (_: nat).O) (S (weight_map (\lambda (_: nat).O) u))) z)) (plus 
(weight_map (\lambda (_: nat).O) u) (weight_map (wadd (\lambda (_: nat).O) (S 
(weight_map (\lambda (_: nat).O) u))) t)) (le_lt_plus_plus (weight_map 
(\lambda (_: nat).O) u) (weight_map (\lambda (_: nat).O) u) (weight_map (wadd 
(\lambda (_: nat).O) (S (weight_map (\lambda (_: nat).O) u))) z) (weight_map 
(wadd (\lambda (_: nat).O) (S (weight_map (\lambda (_: nat).O) u))) t) (le_n 
(weight_map (\lambda (_: nat).O) u)) (subst0_weight_lt u t z O H (wadd 
(\lambda (_: nat).O) (S (weight_map (\lambda (_: nat).O) u))) (wadd (\lambda 
(_: nat).O) (S (weight_map (\lambda (_: nat).O) u))) (\lambda (m: nat).(le_n 
(wadd (\lambda (_: nat).O) (S (weight_map (\lambda (_: nat).O) u)) m))) 
(eq_ind nat (weight_map (\lambda (_: nat).O) (lift O O u)) (\lambda (n: 
nat).(lt n (S (weight_map (\lambda (_: nat).O) u)))) (eq_ind_r T u (\lambda 
(t0: T).(lt (weight_map (\lambda (_: nat).O) t0) (S (weight_map (\lambda (_: 
nat).O) u)))) (le_n (S (weight_map (\lambda (_: nat).O) u))) (lift O O u) 
(lift_r u O)) (weight_map (wadd (\lambda (_: nat).O) (S (weight_map (\lambda 
(_: nat).O) u))) (lift (S O) O u)) (lift_weight_add_O (S (weight_map (\lambda 
(_: nat).O) u)) u O (\lambda (_: nat).O))))))))).
(* COMMENTS
Initial nodes: 347
END *)

theorem subst0_tlt:
 \forall (u: T).(\forall (t: T).(\forall (z: T).((subst0 O u t z) \to (tlt z 
(THead (Bind Abbr) u t)))))
\def
 \lambda (u: T).(\lambda (t: T).(\lambda (z: T).(\lambda (H: (subst0 O u t 
z)).(tlt_trans (THead (Bind Abbr) u z) z (THead (Bind Abbr) u t) (tlt_head_dx 
(Bind Abbr) u z) (subst0_tlt_head u t z H))))).
(* COMMENTS
Initial nodes: 59
END *)

