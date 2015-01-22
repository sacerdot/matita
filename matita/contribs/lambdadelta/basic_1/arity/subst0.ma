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

include "Basic-1/arity/props.ma".

include "Basic-1/fsubst0/fwd.ma".

include "Basic-1/csubst0/getl.ma".

include "Basic-1/subst0/dec.ma".

include "Basic-1/subst0/fwd.ma".

include "Basic-1/getl/getl.ma".

theorem arity_gen_cvoid_subst0:
 \forall (g: G).(\forall (c: C).(\forall (t: T).(\forall (a: A).((arity g c t 
a) \to (\forall (d: C).(\forall (u: T).(\forall (i: nat).((getl i c (CHead d 
(Bind Void) u)) \to (\forall (w: T).(\forall (v: T).((subst0 i w t v) \to 
(\forall (P: Prop).P))))))))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (t: T).(\lambda (a: A).(\lambda (H: 
(arity g c t a)).(arity_ind g (\lambda (c0: C).(\lambda (t0: T).(\lambda (_: 
A).(\forall (d: C).(\forall (u: T).(\forall (i: nat).((getl i c0 (CHead d 
(Bind Void) u)) \to (\forall (w: T).(\forall (v: T).((subst0 i w t0 v) \to 
(\forall (P: Prop).P))))))))))) (\lambda (c0: C).(\lambda (n: nat).(\lambda 
(d: C).(\lambda (u: T).(\lambda (i: nat).(\lambda (_: (getl i c0 (CHead d 
(Bind Void) u))).(\lambda (w: T).(\lambda (v: T).(\lambda (H1: (subst0 i w 
(TSort n) v)).(\lambda (P: Prop).(subst0_gen_sort w v i n H1 P))))))))))) 
(\lambda (c0: C).(\lambda (d: C).(\lambda (u: T).(\lambda (i: nat).(\lambda 
(H0: (getl i c0 (CHead d (Bind Abbr) u))).(\lambda (a0: A).(\lambda (_: 
(arity g d u a0)).(\lambda (_: ((\forall (d0: C).(\forall (u0: T).(\forall 
(i0: nat).((getl i0 d (CHead d0 (Bind Void) u0)) \to (\forall (w: T).(\forall 
(v: T).((subst0 i0 w u v) \to (\forall (P: Prop).P)))))))))).(\lambda (d0: 
C).(\lambda (u0: T).(\lambda (i0: nat).(\lambda (H3: (getl i0 c0 (CHead d0 
(Bind Void) u0))).(\lambda (w: T).(\lambda (v: T).(\lambda (H4: (subst0 i0 w 
(TLRef i) v)).(\lambda (P: Prop).(land_ind (eq nat i i0) (eq T v (lift (S i) 
O w)) P (\lambda (H5: (eq nat i i0)).(\lambda (_: (eq T v (lift (S i) O 
w))).(let H7 \def (eq_ind_r nat i0 (\lambda (n: nat).(getl n c0 (CHead d0 
(Bind Void) u0))) H3 i H5) in (let H8 \def (eq_ind C (CHead d (Bind Abbr) u) 
(\lambda (c1: C).(getl i c0 c1)) H0 (CHead d0 (Bind Void) u0) (getl_mono c0 
(CHead d (Bind Abbr) u) i H0 (CHead d0 (Bind Void) u0) H7)) in (let H9 \def 
(eq_ind C (CHead d (Bind Abbr) u) (\lambda (ee: C).(match ee in C return 
(\lambda (_: C).Prop) with [(CSort _) \Rightarrow False | (CHead _ k _) 
\Rightarrow (match k in K return (\lambda (_: K).Prop) with [(Bind b) 
\Rightarrow (match b in B return (\lambda (_: B).Prop) with [Abbr \Rightarrow 
True | Abst \Rightarrow False | Void \Rightarrow False]) | (Flat _) 
\Rightarrow False])])) I (CHead d0 (Bind Void) u0) (getl_mono c0 (CHead d 
(Bind Abbr) u) i H0 (CHead d0 (Bind Void) u0) H7)) in (False_ind P H9)))))) 
(subst0_gen_lref w v i0 i H4)))))))))))))))))) (\lambda (c0: C).(\lambda (d: 
C).(\lambda (u: T).(\lambda (i: nat).(\lambda (H0: (getl i c0 (CHead d (Bind 
Abst) u))).(\lambda (a0: A).(\lambda (_: (arity g d u (asucc g a0))).(\lambda 
(_: ((\forall (d0: C).(\forall (u0: T).(\forall (i0: nat).((getl i0 d (CHead 
d0 (Bind Void) u0)) \to (\forall (w: T).(\forall (v: T).((subst0 i0 w u v) 
\to (\forall (P: Prop).P)))))))))).(\lambda (d0: C).(\lambda (u0: T).(\lambda 
(i0: nat).(\lambda (H3: (getl i0 c0 (CHead d0 (Bind Void) u0))).(\lambda (w: 
T).(\lambda (v: T).(\lambda (H4: (subst0 i0 w (TLRef i) v)).(\lambda (P: 
Prop).(land_ind (eq nat i i0) (eq T v (lift (S i) O w)) P (\lambda (H5: (eq 
nat i i0)).(\lambda (_: (eq T v (lift (S i) O w))).(let H7 \def (eq_ind_r nat 
i0 (\lambda (n: nat).(getl n c0 (CHead d0 (Bind Void) u0))) H3 i H5) in (let 
H8 \def (eq_ind C (CHead d (Bind Abst) u) (\lambda (c1: C).(getl i c0 c1)) H0 
(CHead d0 (Bind Void) u0) (getl_mono c0 (CHead d (Bind Abst) u) i H0 (CHead 
d0 (Bind Void) u0) H7)) in (let H9 \def (eq_ind C (CHead d (Bind Abst) u) 
(\lambda (ee: C).(match ee in C return (\lambda (_: C).Prop) with [(CSort _) 
\Rightarrow False | (CHead _ k _) \Rightarrow (match k in K return (\lambda 
(_: K).Prop) with [(Bind b) \Rightarrow (match b in B return (\lambda (_: 
B).Prop) with [Abbr \Rightarrow False | Abst \Rightarrow True | Void 
\Rightarrow False]) | (Flat _) \Rightarrow False])])) I (CHead d0 (Bind Void) 
u0) (getl_mono c0 (CHead d (Bind Abst) u) i H0 (CHead d0 (Bind Void) u0) H7)) 
in (False_ind P H9)))))) (subst0_gen_lref w v i0 i H4)))))))))))))))))) 
(\lambda (b: B).(\lambda (_: (not (eq B b Abst))).(\lambda (c0: C).(\lambda 
(u: T).(\lambda (a1: A).(\lambda (_: (arity g c0 u a1)).(\lambda (H2: 
((\forall (d: C).(\forall (u0: T).(\forall (i: nat).((getl i c0 (CHead d 
(Bind Void) u0)) \to (\forall (w: T).(\forall (v: T).((subst0 i w u v) \to 
(\forall (P: Prop).P)))))))))).(\lambda (t0: T).(\lambda (a2: A).(\lambda (_: 
(arity g (CHead c0 (Bind b) u) t0 a2)).(\lambda (H4: ((\forall (d: 
C).(\forall (u0: T).(\forall (i: nat).((getl i (CHead c0 (Bind b) u) (CHead d 
(Bind Void) u0)) \to (\forall (w: T).(\forall (v: T).((subst0 i w t0 v) \to 
(\forall (P: Prop).P)))))))))).(\lambda (d: C).(\lambda (u0: T).(\lambda (i: 
nat).(\lambda (H5: (getl i c0 (CHead d (Bind Void) u0))).(\lambda (w: 
T).(\lambda (v: T).(\lambda (H6: (subst0 i w (THead (Bind b) u t0) 
v)).(\lambda (P: Prop).(or3_ind (ex2 T (\lambda (u2: T).(eq T v (THead (Bind 
b) u2 t0))) (\lambda (u2: T).(subst0 i w u u2))) (ex2 T (\lambda (t2: T).(eq 
T v (THead (Bind b) u t2))) (\lambda (t2: T).(subst0 (s (Bind b) i) w t0 
t2))) (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T v (THead (Bind b) u2 
t2)))) (\lambda (u2: T).(\lambda (_: T).(subst0 i w u u2))) (\lambda (_: 
T).(\lambda (t2: T).(subst0 (s (Bind b) i) w t0 t2)))) P (\lambda (H7: (ex2 T 
(\lambda (u2: T).(eq T v (THead (Bind b) u2 t0))) (\lambda (u2: T).(subst0 i 
w u u2)))).(ex2_ind T (\lambda (u2: T).(eq T v (THead (Bind b) u2 t0))) 
(\lambda (u2: T).(subst0 i w u u2)) P (\lambda (x: T).(\lambda (_: (eq T v 
(THead (Bind b) x t0))).(\lambda (H9: (subst0 i w u x)).(H2 d u0 i H5 w x H9 
P)))) H7)) (\lambda (H7: (ex2 T (\lambda (t2: T).(eq T v (THead (Bind b) u 
t2))) (\lambda (t2: T).(subst0 (s (Bind b) i) w t0 t2)))).(ex2_ind T (\lambda 
(t2: T).(eq T v (THead (Bind b) u t2))) (\lambda (t2: T).(subst0 (s (Bind b) 
i) w t0 t2)) P (\lambda (x: T).(\lambda (_: (eq T v (THead (Bind b) u 
x))).(\lambda (H9: (subst0 (s (Bind b) i) w t0 x)).(H4 d u0 (S i) 
(getl_clear_bind b (CHead c0 (Bind b) u) c0 u (clear_bind b c0 u) (CHead d 
(Bind Void) u0) i H5) w x H9 P)))) H7)) (\lambda (H7: (ex3_2 T T (\lambda 
(u2: T).(\lambda (t2: T).(eq T v (THead (Bind b) u2 t2)))) (\lambda (u2: 
T).(\lambda (_: T).(subst0 i w u u2))) (\lambda (_: T).(\lambda (t2: 
T).(subst0 (s (Bind b) i) w t0 t2))))).(ex3_2_ind T T (\lambda (u2: 
T).(\lambda (t2: T).(eq T v (THead (Bind b) u2 t2)))) (\lambda (u2: 
T).(\lambda (_: T).(subst0 i w u u2))) (\lambda (_: T).(\lambda (t2: 
T).(subst0 (s (Bind b) i) w t0 t2))) P (\lambda (x0: T).(\lambda (x1: 
T).(\lambda (_: (eq T v (THead (Bind b) x0 x1))).(\lambda (H9: (subst0 i w u 
x0)).(\lambda (_: (subst0 (s (Bind b) i) w t0 x1)).(H2 d u0 i H5 w x0 H9 
P)))))) H7)) (subst0_gen_head (Bind b) w u t0 v i H6))))))))))))))))))))) 
(\lambda (c0: C).(\lambda (u: T).(\lambda (a1: A).(\lambda (_: (arity g c0 u 
(asucc g a1))).(\lambda (H1: ((\forall (d: C).(\forall (u0: T).(\forall (i: 
nat).((getl i c0 (CHead d (Bind Void) u0)) \to (\forall (w: T).(\forall (v: 
T).((subst0 i w u v) \to (\forall (P: Prop).P)))))))))).(\lambda (t0: 
T).(\lambda (a2: A).(\lambda (_: (arity g (CHead c0 (Bind Abst) u) t0 
a2)).(\lambda (H3: ((\forall (d: C).(\forall (u0: T).(\forall (i: nat).((getl 
i (CHead c0 (Bind Abst) u) (CHead d (Bind Void) u0)) \to (\forall (w: 
T).(\forall (v: T).((subst0 i w t0 v) \to (\forall (P: 
Prop).P)))))))))).(\lambda (d: C).(\lambda (u0: T).(\lambda (i: nat).(\lambda 
(H4: (getl i c0 (CHead d (Bind Void) u0))).(\lambda (w: T).(\lambda (v: 
T).(\lambda (H5: (subst0 i w (THead (Bind Abst) u t0) v)).(\lambda (P: 
Prop).(or3_ind (ex2 T (\lambda (u2: T).(eq T v (THead (Bind Abst) u2 t0))) 
(\lambda (u2: T).(subst0 i w u u2))) (ex2 T (\lambda (t2: T).(eq T v (THead 
(Bind Abst) u t2))) (\lambda (t2: T).(subst0 (s (Bind Abst) i) w t0 t2))) 
(ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T v (THead (Bind Abst) u2 
t2)))) (\lambda (u2: T).(\lambda (_: T).(subst0 i w u u2))) (\lambda (_: 
T).(\lambda (t2: T).(subst0 (s (Bind Abst) i) w t0 t2)))) P (\lambda (H6: 
(ex2 T (\lambda (u2: T).(eq T v (THead (Bind Abst) u2 t0))) (\lambda (u2: 
T).(subst0 i w u u2)))).(ex2_ind T (\lambda (u2: T).(eq T v (THead (Bind 
Abst) u2 t0))) (\lambda (u2: T).(subst0 i w u u2)) P (\lambda (x: T).(\lambda 
(_: (eq T v (THead (Bind Abst) x t0))).(\lambda (H8: (subst0 i w u x)).(H1 d 
u0 i H4 w x H8 P)))) H6)) (\lambda (H6: (ex2 T (\lambda (t2: T).(eq T v 
(THead (Bind Abst) u t2))) (\lambda (t2: T).(subst0 (s (Bind Abst) i) w t0 
t2)))).(ex2_ind T (\lambda (t2: T).(eq T v (THead (Bind Abst) u t2))) 
(\lambda (t2: T).(subst0 (s (Bind Abst) i) w t0 t2)) P (\lambda (x: 
T).(\lambda (_: (eq T v (THead (Bind Abst) u x))).(\lambda (H8: (subst0 (s 
(Bind Abst) i) w t0 x)).(H3 d u0 (S i) (getl_clear_bind Abst (CHead c0 (Bind 
Abst) u) c0 u (clear_bind Abst c0 u) (CHead d (Bind Void) u0) i H4) w x H8 
P)))) H6)) (\lambda (H6: (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T v 
(THead (Bind Abst) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(subst0 i w u 
u2))) (\lambda (_: T).(\lambda (t2: T).(subst0 (s (Bind Abst) i) w t0 
t2))))).(ex3_2_ind T T (\lambda (u2: T).(\lambda (t2: T).(eq T v (THead (Bind 
Abst) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(subst0 i w u u2))) (\lambda 
(_: T).(\lambda (t2: T).(subst0 (s (Bind Abst) i) w t0 t2))) P (\lambda (x0: 
T).(\lambda (x1: T).(\lambda (_: (eq T v (THead (Bind Abst) x0 x1))).(\lambda 
(H8: (subst0 i w u x0)).(\lambda (_: (subst0 (s (Bind Abst) i) w t0 x1)).(H1 
d u0 i H4 w x0 H8 P)))))) H6)) (subst0_gen_head (Bind Abst) w u t0 v i 
H5))))))))))))))))))) (\lambda (c0: C).(\lambda (u: T).(\lambda (a1: 
A).(\lambda (_: (arity g c0 u a1)).(\lambda (H1: ((\forall (d: C).(\forall 
(u0: T).(\forall (i: nat).((getl i c0 (CHead d (Bind Void) u0)) \to (\forall 
(w: T).(\forall (v: T).((subst0 i w u v) \to (\forall (P: 
Prop).P)))))))))).(\lambda (t0: T).(\lambda (a2: A).(\lambda (_: (arity g c0 
t0 (AHead a1 a2))).(\lambda (H3: ((\forall (d: C).(\forall (u0: T).(\forall 
(i: nat).((getl i c0 (CHead d (Bind Void) u0)) \to (\forall (w: T).(\forall 
(v: T).((subst0 i w t0 v) \to (\forall (P: Prop).P)))))))))).(\lambda (d: 
C).(\lambda (u0: T).(\lambda (i: nat).(\lambda (H4: (getl i c0 (CHead d (Bind 
Void) u0))).(\lambda (w: T).(\lambda (v: T).(\lambda (H5: (subst0 i w (THead 
(Flat Appl) u t0) v)).(\lambda (P: Prop).(or3_ind (ex2 T (\lambda (u2: T).(eq 
T v (THead (Flat Appl) u2 t0))) (\lambda (u2: T).(subst0 i w u u2))) (ex2 T 
(\lambda (t2: T).(eq T v (THead (Flat Appl) u t2))) (\lambda (t2: T).(subst0 
(s (Flat Appl) i) w t0 t2))) (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq 
T v (THead (Flat Appl) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(subst0 i w 
u u2))) (\lambda (_: T).(\lambda (t2: T).(subst0 (s (Flat Appl) i) w t0 
t2)))) P (\lambda (H6: (ex2 T (\lambda (u2: T).(eq T v (THead (Flat Appl) u2 
t0))) (\lambda (u2: T).(subst0 i w u u2)))).(ex2_ind T (\lambda (u2: T).(eq T 
v (THead (Flat Appl) u2 t0))) (\lambda (u2: T).(subst0 i w u u2)) P (\lambda 
(x: T).(\lambda (_: (eq T v (THead (Flat Appl) x t0))).(\lambda (H8: (subst0 
i w u x)).(H1 d u0 i H4 w x H8 P)))) H6)) (\lambda (H6: (ex2 T (\lambda (t2: 
T).(eq T v (THead (Flat Appl) u t2))) (\lambda (t2: T).(subst0 (s (Flat Appl) 
i) w t0 t2)))).(ex2_ind T (\lambda (t2: T).(eq T v (THead (Flat Appl) u t2))) 
(\lambda (t2: T).(subst0 (s (Flat Appl) i) w t0 t2)) P (\lambda (x: 
T).(\lambda (_: (eq T v (THead (Flat Appl) u x))).(\lambda (H8: (subst0 (s 
(Flat Appl) i) w t0 x)).(H3 d u0 i H4 w x H8 P)))) H6)) (\lambda (H6: (ex3_2 
T T (\lambda (u2: T).(\lambda (t2: T).(eq T v (THead (Flat Appl) u2 t2)))) 
(\lambda (u2: T).(\lambda (_: T).(subst0 i w u u2))) (\lambda (_: T).(\lambda 
(t2: T).(subst0 (s (Flat Appl) i) w t0 t2))))).(ex3_2_ind T T (\lambda (u2: 
T).(\lambda (t2: T).(eq T v (THead (Flat Appl) u2 t2)))) (\lambda (u2: 
T).(\lambda (_: T).(subst0 i w u u2))) (\lambda (_: T).(\lambda (t2: 
T).(subst0 (s (Flat Appl) i) w t0 t2))) P (\lambda (x0: T).(\lambda (x1: 
T).(\lambda (_: (eq T v (THead (Flat Appl) x0 x1))).(\lambda (H8: (subst0 i w 
u x0)).(\lambda (_: (subst0 (s (Flat Appl) i) w t0 x1)).(H1 d u0 i H4 w x0 H8 
P)))))) H6)) (subst0_gen_head (Flat Appl) w u t0 v i H5))))))))))))))))))) 
(\lambda (c0: C).(\lambda (u: T).(\lambda (a0: A).(\lambda (_: (arity g c0 u 
(asucc g a0))).(\lambda (H1: ((\forall (d: C).(\forall (u0: T).(\forall (i: 
nat).((getl i c0 (CHead d (Bind Void) u0)) \to (\forall (w: T).(\forall (v: 
T).((subst0 i w u v) \to (\forall (P: Prop).P)))))))))).(\lambda (t0: 
T).(\lambda (_: (arity g c0 t0 a0)).(\lambda (H3: ((\forall (d: C).(\forall 
(u0: T).(\forall (i: nat).((getl i c0 (CHead d (Bind Void) u0)) \to (\forall 
(w: T).(\forall (v: T).((subst0 i w t0 v) \to (\forall (P: 
Prop).P)))))))))).(\lambda (d: C).(\lambda (u0: T).(\lambda (i: nat).(\lambda 
(H4: (getl i c0 (CHead d (Bind Void) u0))).(\lambda (w: T).(\lambda (v: 
T).(\lambda (H5: (subst0 i w (THead (Flat Cast) u t0) v)).(\lambda (P: 
Prop).(or3_ind (ex2 T (\lambda (u2: T).(eq T v (THead (Flat Cast) u2 t0))) 
(\lambda (u2: T).(subst0 i w u u2))) (ex2 T (\lambda (t2: T).(eq T v (THead 
(Flat Cast) u t2))) (\lambda (t2: T).(subst0 (s (Flat Cast) i) w t0 t2))) 
(ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T v (THead (Flat Cast) u2 
t2)))) (\lambda (u2: T).(\lambda (_: T).(subst0 i w u u2))) (\lambda (_: 
T).(\lambda (t2: T).(subst0 (s (Flat Cast) i) w t0 t2)))) P (\lambda (H6: 
(ex2 T (\lambda (u2: T).(eq T v (THead (Flat Cast) u2 t0))) (\lambda (u2: 
T).(subst0 i w u u2)))).(ex2_ind T (\lambda (u2: T).(eq T v (THead (Flat 
Cast) u2 t0))) (\lambda (u2: T).(subst0 i w u u2)) P (\lambda (x: T).(\lambda 
(_: (eq T v (THead (Flat Cast) x t0))).(\lambda (H8: (subst0 i w u x)).(H1 d 
u0 i H4 w x H8 P)))) H6)) (\lambda (H6: (ex2 T (\lambda (t2: T).(eq T v 
(THead (Flat Cast) u t2))) (\lambda (t2: T).(subst0 (s (Flat Cast) i) w t0 
t2)))).(ex2_ind T (\lambda (t2: T).(eq T v (THead (Flat Cast) u t2))) 
(\lambda (t2: T).(subst0 (s (Flat Cast) i) w t0 t2)) P (\lambda (x: 
T).(\lambda (_: (eq T v (THead (Flat Cast) u x))).(\lambda (H8: (subst0 (s 
(Flat Cast) i) w t0 x)).(H3 d u0 i H4 w x H8 P)))) H6)) (\lambda (H6: (ex3_2 
T T (\lambda (u2: T).(\lambda (t2: T).(eq T v (THead (Flat Cast) u2 t2)))) 
(\lambda (u2: T).(\lambda (_: T).(subst0 i w u u2))) (\lambda (_: T).(\lambda 
(t2: T).(subst0 (s (Flat Cast) i) w t0 t2))))).(ex3_2_ind T T (\lambda (u2: 
T).(\lambda (t2: T).(eq T v (THead (Flat Cast) u2 t2)))) (\lambda (u2: 
T).(\lambda (_: T).(subst0 i w u u2))) (\lambda (_: T).(\lambda (t2: 
T).(subst0 (s (Flat Cast) i) w t0 t2))) P (\lambda (x0: T).(\lambda (x1: 
T).(\lambda (_: (eq T v (THead (Flat Cast) x0 x1))).(\lambda (H8: (subst0 i w 
u x0)).(\lambda (_: (subst0 (s (Flat Cast) i) w t0 x1)).(H1 d u0 i H4 w x0 H8 
P)))))) H6)) (subst0_gen_head (Flat Cast) w u t0 v i H5)))))))))))))))))) 
(\lambda (c0: C).(\lambda (t0: T).(\lambda (a1: A).(\lambda (_: (arity g c0 
t0 a1)).(\lambda (H1: ((\forall (d: C).(\forall (u: T).(\forall (i: 
nat).((getl i c0 (CHead d (Bind Void) u)) \to (\forall (w: T).(\forall (v: 
T).((subst0 i w t0 v) \to (\forall (P: Prop).P)))))))))).(\lambda (a2: 
A).(\lambda (_: (leq g a1 a2)).(\lambda (d: C).(\lambda (u: T).(\lambda (i: 
nat).(\lambda (H3: (getl i c0 (CHead d (Bind Void) u))).(\lambda (w: 
T).(\lambda (v: T).(\lambda (H4: (subst0 i w t0 v)).(\lambda (P: Prop).(H1 d 
u i H3 w v H4 P)))))))))))))))) c t a H))))).
(* COMMENTS
Initial nodes: 4131
END *)

theorem arity_gen_cvoid:
 \forall (g: G).(\forall (c: C).(\forall (t: T).(\forall (a: A).((arity g c t 
a) \to (\forall (d: C).(\forall (u: T).(\forall (i: nat).((getl i c (CHead d 
(Bind Void) u)) \to (ex T (\lambda (v: T).(eq T t (lift (S O) i v))))))))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (t: T).(\lambda (a: A).(\lambda (H: 
(arity g c t a)).(\lambda (d: C).(\lambda (u: T).(\lambda (i: nat).(\lambda 
(H0: (getl i c (CHead d (Bind Void) u))).(let H_x \def (dnf_dec u t i) in 
(let H1 \def H_x in (ex_ind T (\lambda (v: T).(or (subst0 i u t (lift (S O) i 
v)) (eq T t (lift (S O) i v)))) (ex T (\lambda (v: T).(eq T t (lift (S O) i 
v)))) (\lambda (x: T).(\lambda (H2: (or (subst0 i u t (lift (S O) i x)) (eq T 
t (lift (S O) i x)))).(or_ind (subst0 i u t (lift (S O) i x)) (eq T t (lift 
(S O) i x)) (ex T (\lambda (v: T).(eq T t (lift (S O) i v)))) (\lambda (H3: 
(subst0 i u t (lift (S O) i x))).(arity_gen_cvoid_subst0 g c t a H d u i H0 u 
(lift (S O) i x) H3 (ex T (\lambda (v: T).(eq T t (lift (S O) i v)))))) 
(\lambda (H3: (eq T t (lift (S O) i x))).(let H4 \def (eq_ind T t (\lambda 
(t0: T).(arity g c t0 a)) H (lift (S O) i x) H3) in (eq_ind_r T (lift (S O) i 
x) (\lambda (t0: T).(ex T (\lambda (v: T).(eq T t0 (lift (S O) i v))))) 
(ex_intro T (\lambda (v: T).(eq T (lift (S O) i x) (lift (S O) i v))) x 
(refl_equal T (lift (S O) i x))) t H3))) H2))) H1))))))))))).
(* COMMENTS
Initial nodes: 423
END *)

theorem arity_fsubst0:
 \forall (g: G).(\forall (c1: C).(\forall (t1: T).(\forall (a: A).((arity g 
c1 t1 a) \to (\forall (d1: C).(\forall (u: T).(\forall (i: nat).((getl i c1 
(CHead d1 (Bind Abbr) u)) \to (\forall (c2: C).(\forall (t2: T).((fsubst0 i u 
c1 t1 c2 t2) \to (arity g c2 t2 a))))))))))))
\def
 \lambda (g: G).(\lambda (c1: C).(\lambda (t1: T).(\lambda (a: A).(\lambda 
(H: (arity g c1 t1 a)).(arity_ind g (\lambda (c: C).(\lambda (t: T).(\lambda 
(a0: A).(\forall (d1: C).(\forall (u: T).(\forall (i: nat).((getl i c (CHead 
d1 (Bind Abbr) u)) \to (\forall (c2: C).(\forall (t2: T).((fsubst0 i u c t c2 
t2) \to (arity g c2 t2 a0))))))))))) (\lambda (c: C).(\lambda (n: 
nat).(\lambda (d1: C).(\lambda (u: T).(\lambda (i: nat).(\lambda (_: (getl i 
c (CHead d1 (Bind Abbr) u))).(\lambda (c2: C).(\lambda (t2: T).(\lambda (H1: 
(fsubst0 i u c (TSort n) c2 t2)).(let H_x \def (fsubst0_gen_base c c2 (TSort 
n) t2 u i H1) in (let H2 \def H_x in (or3_ind (land (eq C c c2) (subst0 i u 
(TSort n) t2)) (land (eq T (TSort n) t2) (csubst0 i u c c2)) (land (subst0 i 
u (TSort n) t2) (csubst0 i u c c2)) (arity g c2 t2 (ASort O n)) (\lambda (H3: 
(land (eq C c c2) (subst0 i u (TSort n) t2))).(land_ind (eq C c c2) (subst0 i 
u (TSort n) t2) (arity g c2 t2 (ASort O n)) (\lambda (H4: (eq C c 
c2)).(\lambda (H5: (subst0 i u (TSort n) t2)).(eq_ind C c (\lambda (c0: 
C).(arity g c0 t2 (ASort O n))) (subst0_gen_sort u t2 i n H5 (arity g c t2 
(ASort O n))) c2 H4))) H3)) (\lambda (H3: (land (eq T (TSort n) t2) (csubst0 
i u c c2))).(land_ind (eq T (TSort n) t2) (csubst0 i u c c2) (arity g c2 t2 
(ASort O n)) (\lambda (H4: (eq T (TSort n) t2)).(\lambda (_: (csubst0 i u c 
c2)).(eq_ind T (TSort n) (\lambda (t: T).(arity g c2 t (ASort O n))) 
(arity_sort g c2 n) t2 H4))) H3)) (\lambda (H3: (land (subst0 i u (TSort n) 
t2) (csubst0 i u c c2))).(land_ind (subst0 i u (TSort n) t2) (csubst0 i u c 
c2) (arity g c2 t2 (ASort O n)) (\lambda (H4: (subst0 i u (TSort n) 
t2)).(\lambda (_: (csubst0 i u c c2)).(subst0_gen_sort u t2 i n H4 (arity g 
c2 t2 (ASort O n))))) H3)) H2)))))))))))) (\lambda (c: C).(\lambda (d: 
C).(\lambda (u: T).(\lambda (i: nat).(\lambda (H0: (getl i c (CHead d (Bind 
Abbr) u))).(\lambda (a0: A).(\lambda (H1: (arity g d u a0)).(\lambda (H2: 
((\forall (d1: C).(\forall (u0: T).(\forall (i0: nat).((getl i0 d (CHead d1 
(Bind Abbr) u0)) \to (\forall (c2: C).(\forall (t2: T).((fsubst0 i0 u0 d u c2 
t2) \to (arity g c2 t2 a0)))))))))).(\lambda (d1: C).(\lambda (u0: 
T).(\lambda (i0: nat).(\lambda (H3: (getl i0 c (CHead d1 (Bind Abbr) 
u0))).(\lambda (c2: C).(\lambda (t2: T).(\lambda (H4: (fsubst0 i0 u0 c (TLRef 
i) c2 t2)).(let H_x \def (fsubst0_gen_base c c2 (TLRef i) t2 u0 i0 H4) in 
(let H5 \def H_x in (or3_ind (land (eq C c c2) (subst0 i0 u0 (TLRef i) t2)) 
(land (eq T (TLRef i) t2) (csubst0 i0 u0 c c2)) (land (subst0 i0 u0 (TLRef i) 
t2) (csubst0 i0 u0 c c2)) (arity g c2 t2 a0) (\lambda (H6: (land (eq C c c2) 
(subst0 i0 u0 (TLRef i) t2))).(land_ind (eq C c c2) (subst0 i0 u0 (TLRef i) 
t2) (arity g c2 t2 a0) (\lambda (H7: (eq C c c2)).(\lambda (H8: (subst0 i0 u0 
(TLRef i) t2)).(eq_ind C c (\lambda (c0: C).(arity g c0 t2 a0)) (land_ind (eq 
nat i i0) (eq T t2 (lift (S i) O u0)) (arity g c t2 a0) (\lambda (H9: (eq nat 
i i0)).(\lambda (H10: (eq T t2 (lift (S i) O u0))).(eq_ind_r T (lift (S i) O 
u0) (\lambda (t: T).(arity g c t a0)) (let H11 \def (eq_ind_r nat i0 (\lambda 
(n: nat).(getl n c (CHead d1 (Bind Abbr) u0))) H3 i H9) in (let H12 \def 
(eq_ind C (CHead d (Bind Abbr) u) (\lambda (c0: C).(getl i c c0)) H0 (CHead 
d1 (Bind Abbr) u0) (getl_mono c (CHead d (Bind Abbr) u) i H0 (CHead d1 (Bind 
Abbr) u0) H11)) in (let H13 \def (f_equal C C (\lambda (e: C).(match e in C 
return (\lambda (_: C).C) with [(CSort _) \Rightarrow d | (CHead c0 _ _) 
\Rightarrow c0])) (CHead d (Bind Abbr) u) (CHead d1 (Bind Abbr) u0) 
(getl_mono c (CHead d (Bind Abbr) u) i H0 (CHead d1 (Bind Abbr) u0) H11)) in 
((let H14 \def (f_equal C T (\lambda (e: C).(match e in C return (\lambda (_: 
C).T) with [(CSort _) \Rightarrow u | (CHead _ _ t) \Rightarrow t])) (CHead d 
(Bind Abbr) u) (CHead d1 (Bind Abbr) u0) (getl_mono c (CHead d (Bind Abbr) u) 
i H0 (CHead d1 (Bind Abbr) u0) H11)) in (\lambda (H15: (eq C d d1)).(let H16 
\def (eq_ind_r T u0 (\lambda (t: T).(getl i c (CHead d1 (Bind Abbr) t))) H12 
u H14) in (eq_ind T u (\lambda (t: T).(arity g c (lift (S i) O t) a0)) (let 
H17 \def (eq_ind_r C d1 (\lambda (c0: C).(getl i c (CHead c0 (Bind Abbr) u))) 
H16 d H15) in (arity_lift g d u a0 H1 c (S i) O (getl_drop Abbr c d u i 
H17))) u0 H14)))) H13)))) t2 H10))) (subst0_gen_lref u0 t2 i0 i H8)) c2 H7))) 
H6)) (\lambda (H6: (land (eq T (TLRef i) t2) (csubst0 i0 u0 c c2))).(land_ind 
(eq T (TLRef i) t2) (csubst0 i0 u0 c c2) (arity g c2 t2 a0) (\lambda (H7: (eq 
T (TLRef i) t2)).(\lambda (H8: (csubst0 i0 u0 c c2)).(eq_ind T (TLRef i) 
(\lambda (t: T).(arity g c2 t a0)) (lt_le_e i i0 (arity g c2 (TLRef i) a0) 
(\lambda (H9: (lt i i0)).(let H10 \def (csubst0_getl_lt i0 i H9 c c2 u0 H8 
(CHead d (Bind Abbr) u) H0) in (or4_ind (getl i c2 (CHead d (Bind Abbr) u)) 
(ex3_4 B C T T (\lambda (b: B).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: 
T).(eq C (CHead d (Bind Abbr) u) (CHead e0 (Bind b) u1)))))) (\lambda (b: 
B).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(getl i c2 (CHead e0 
(Bind b) w)))))) (\lambda (_: B).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(w: T).(subst0 (minus i0 (S i)) u0 u1 w)))))) (ex3_4 B C C T (\lambda (b: 
B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(eq C (CHead d (Bind 
Abbr) u) (CHead e1 (Bind b) u1)))))) (\lambda (b: B).(\lambda (_: C).(\lambda 
(e2: C).(\lambda (u1: T).(getl i c2 (CHead e2 (Bind b) u1)))))) (\lambda (_: 
B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus i0 (S 
i)) u0 e1 e2)))))) (ex4_5 B C C T T (\lambda (b: B).(\lambda (e1: C).(\lambda 
(_: C).(\lambda (u1: T).(\lambda (_: T).(eq C (CHead d (Bind Abbr) u) (CHead 
e1 (Bind b) u1))))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(getl i c2 (CHead e2 (Bind b) w))))))) 
(\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (w: 
T).(subst0 (minus i0 (S i)) u0 u1 w)))))) (\lambda (_: B).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus i0 (S i)) 
u0 e1 e2))))))) (arity g c2 (TLRef i) a0) (\lambda (H11: (getl i c2 (CHead d 
(Bind Abbr) u))).(let H12 \def (eq_ind nat (minus i0 i) (\lambda (n: 
nat).(getl n (CHead d (Bind Abbr) u) (CHead d1 (Bind Abbr) u0))) 
(getl_conf_le i0 (CHead d1 (Bind Abbr) u0) c H3 (CHead d (Bind Abbr) u) i H0 
(le_S_n i i0 (le_S (S i) i0 H9))) (S (minus i0 (S i))) (minus_x_Sy i0 i H9)) 
in (arity_abbr g c2 d u i H11 a0 H1))) (\lambda (H11: (ex3_4 B C T T (\lambda 
(b: B).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: T).(eq C (CHead d (Bind 
Abbr) u) (CHead e0 (Bind b) u1)))))) (\lambda (b: B).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (w: T).(getl i c2 (CHead e0 (Bind b) w)))))) 
(\lambda (_: B).(\lambda (_: C).(\lambda (u1: T).(\lambda (w: T).(subst0 
(minus i0 (S i)) u0 u1 w))))))).(ex3_4_ind B C T T (\lambda (b: B).(\lambda 
(e0: C).(\lambda (u1: T).(\lambda (_: T).(eq C (CHead d (Bind Abbr) u) (CHead 
e0 (Bind b) u1)))))) (\lambda (b: B).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(getl i c2 (CHead e0 (Bind b) w)))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (u1: T).(\lambda (w: T).(subst0 (minus i0 (S i)) 
u0 u1 w))))) (arity g c2 (TLRef i) a0) (\lambda (x0: B).(\lambda (x1: 
C).(\lambda (x2: T).(\lambda (x3: T).(\lambda (H12: (eq C (CHead d (Bind 
Abbr) u) (CHead x1 (Bind x0) x2))).(\lambda (H13: (getl i c2 (CHead x1 (Bind 
x0) x3))).(\lambda (H14: (subst0 (minus i0 (S i)) u0 x2 x3)).(let H15 \def 
(eq_ind nat (minus i0 i) (\lambda (n: nat).(getl n (CHead d (Bind Abbr) u) 
(CHead d1 (Bind Abbr) u0))) (getl_conf_le i0 (CHead d1 (Bind Abbr) u0) c H3 
(CHead d (Bind Abbr) u) i H0 (le_S_n i i0 (le_S (S i) i0 H9))) (S (minus i0 
(S i))) (minus_x_Sy i0 i H9)) in (let H16 \def (f_equal C C (\lambda (e: 
C).(match e in C return (\lambda (_: C).C) with [(CSort _) \Rightarrow d | 
(CHead c0 _ _) \Rightarrow c0])) (CHead d (Bind Abbr) u) (CHead x1 (Bind x0) 
x2) H12) in ((let H17 \def (f_equal C B (\lambda (e: C).(match e in C return 
(\lambda (_: C).B) with [(CSort _) \Rightarrow Abbr | (CHead _ k _) 
\Rightarrow (match k in K return (\lambda (_: K).B) with [(Bind b) 
\Rightarrow b | (Flat _) \Rightarrow Abbr])])) (CHead d (Bind Abbr) u) (CHead 
x1 (Bind x0) x2) H12) in ((let H18 \def (f_equal C T (\lambda (e: C).(match e 
in C return (\lambda (_: C).T) with [(CSort _) \Rightarrow u | (CHead _ _ t) 
\Rightarrow t])) (CHead d (Bind Abbr) u) (CHead x1 (Bind x0) x2) H12) in 
(\lambda (H19: (eq B Abbr x0)).(\lambda (H20: (eq C d x1)).(let H21 \def 
(eq_ind_r T x2 (\lambda (t: T).(subst0 (minus i0 (S i)) u0 t x3)) H14 u H18) 
in (let H22 \def (eq_ind_r C x1 (\lambda (c0: C).(getl i c2 (CHead c0 (Bind 
x0) x3))) H13 d H20) in (let H23 \def (eq_ind_r B x0 (\lambda (b: B).(getl i 
c2 (CHead d (Bind b) x3))) H22 Abbr H19) in (arity_abbr g c2 d x3 i H23 a0 
(H2 d1 u0 (r (Bind Abbr) (minus i0 (S i))) (getl_gen_S (Bind Abbr) d (CHead 
d1 (Bind Abbr) u0) u (minus i0 (S i)) H15) d x3 (fsubst0_snd (r (Bind Abbr) 
(minus i0 (S i))) u0 d u x3 H21))))))))) H17)) H16)))))))))) H11)) (\lambda 
(H11: (ex3_4 B C C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u1: T).(eq C (CHead d (Bind Abbr) u) (CHead e1 (Bind b) u1)))))) 
(\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u1: T).(getl i c2 
(CHead e2 (Bind b) u1)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 (minus i0 (S i)) u0 e1 e2))))))).(ex3_4_ind B C C 
T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(eq C 
(CHead d (Bind Abbr) u) (CHead e1 (Bind b) u1)))))) (\lambda (b: B).(\lambda 
(_: C).(\lambda (e2: C).(\lambda (u1: T).(getl i c2 (CHead e2 (Bind b) 
u1)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 (minus i0 (S i)) u0 e1 e2))))) (arity g c2 (TLRef i) a0) (\lambda 
(x0: B).(\lambda (x1: C).(\lambda (x2: C).(\lambda (x3: T).(\lambda (H12: (eq 
C (CHead d (Bind Abbr) u) (CHead x1 (Bind x0) x3))).(\lambda (H13: (getl i c2 
(CHead x2 (Bind x0) x3))).(\lambda (H14: (csubst0 (minus i0 (S i)) u0 x1 
x2)).(let H15 \def (eq_ind nat (minus i0 i) (\lambda (n: nat).(getl n (CHead 
d (Bind Abbr) u) (CHead d1 (Bind Abbr) u0))) (getl_conf_le i0 (CHead d1 (Bind 
Abbr) u0) c H3 (CHead d (Bind Abbr) u) i H0 (le_S_n i i0 (le_S (S i) i0 H9))) 
(S (minus i0 (S i))) (minus_x_Sy i0 i H9)) in (let H16 \def (f_equal C C 
(\lambda (e: C).(match e in C return (\lambda (_: C).C) with [(CSort _) 
\Rightarrow d | (CHead c0 _ _) \Rightarrow c0])) (CHead d (Bind Abbr) u) 
(CHead x1 (Bind x0) x3) H12) in ((let H17 \def (f_equal C B (\lambda (e: 
C).(match e in C return (\lambda (_: C).B) with [(CSort _) \Rightarrow Abbr | 
(CHead _ k _) \Rightarrow (match k in K return (\lambda (_: K).B) with [(Bind 
b) \Rightarrow b | (Flat _) \Rightarrow Abbr])])) (CHead d (Bind Abbr) u) 
(CHead x1 (Bind x0) x3) H12) in ((let H18 \def (f_equal C T (\lambda (e: 
C).(match e in C return (\lambda (_: C).T) with [(CSort _) \Rightarrow u | 
(CHead _ _ t) \Rightarrow t])) (CHead d (Bind Abbr) u) (CHead x1 (Bind x0) 
x3) H12) in (\lambda (H19: (eq B Abbr x0)).(\lambda (H20: (eq C d x1)).(let 
H21 \def (eq_ind_r T x3 (\lambda (t: T).(getl i c2 (CHead x2 (Bind x0) t))) 
H13 u H18) in (let H22 \def (eq_ind_r C x1 (\lambda (c0: C).(csubst0 (minus 
i0 (S i)) u0 c0 x2)) H14 d H20) in (let H23 \def (eq_ind_r B x0 (\lambda (b: 
B).(getl i c2 (CHead x2 (Bind b) u))) H21 Abbr H19) in (arity_abbr g c2 x2 u 
i H23 a0 (H2 d1 u0 (r (Bind Abbr) (minus i0 (S i))) (getl_gen_S (Bind Abbr) d 
(CHead d1 (Bind Abbr) u0) u (minus i0 (S i)) H15) x2 u (fsubst0_fst (r (Bind 
Abbr) (minus i0 (S i))) u0 d u x2 H22))))))))) H17)) H16)))))))))) H11)) 
(\lambda (H11: (ex4_5 B C C T T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (_: T).(eq C (CHead d (Bind Abbr) u) (CHead e1 
(Bind b) u1))))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (w: T).(getl i c2 (CHead e2 (Bind b) w))))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (w: T).(subst0 
(minus i0 (S i)) u0 u1 w)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus i0 (S i)) u0 e1 
e2)))))))).(ex4_5_ind B C C T T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (_: T).(eq C (CHead d (Bind Abbr) u) (CHead e1 
(Bind b) u1))))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (w: T).(getl i c2 (CHead e2 (Bind b) w))))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (w: T).(subst0 
(minus i0 (S i)) u0 u1 w)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus i0 (S i)) u0 e1 e2)))))) 
(arity g c2 (TLRef i) a0) (\lambda (x0: B).(\lambda (x1: C).(\lambda (x2: 
C).(\lambda (x3: T).(\lambda (x4: T).(\lambda (H12: (eq C (CHead d (Bind 
Abbr) u) (CHead x1 (Bind x0) x3))).(\lambda (H13: (getl i c2 (CHead x2 (Bind 
x0) x4))).(\lambda (H14: (subst0 (minus i0 (S i)) u0 x3 x4)).(\lambda (H15: 
(csubst0 (minus i0 (S i)) u0 x1 x2)).(let H16 \def (eq_ind nat (minus i0 i) 
(\lambda (n: nat).(getl n (CHead d (Bind Abbr) u) (CHead d1 (Bind Abbr) u0))) 
(getl_conf_le i0 (CHead d1 (Bind Abbr) u0) c H3 (CHead d (Bind Abbr) u) i H0 
(le_S_n i i0 (le_S (S i) i0 H9))) (S (minus i0 (S i))) (minus_x_Sy i0 i H9)) 
in (let H17 \def (f_equal C C (\lambda (e: C).(match e in C return (\lambda 
(_: C).C) with [(CSort _) \Rightarrow d | (CHead c0 _ _) \Rightarrow c0])) 
(CHead d (Bind Abbr) u) (CHead x1 (Bind x0) x3) H12) in ((let H18 \def 
(f_equal C B (\lambda (e: C).(match e in C return (\lambda (_: C).B) with 
[(CSort _) \Rightarrow Abbr | (CHead _ k _) \Rightarrow (match k in K return 
(\lambda (_: K).B) with [(Bind b) \Rightarrow b | (Flat _) \Rightarrow 
Abbr])])) (CHead d (Bind Abbr) u) (CHead x1 (Bind x0) x3) H12) in ((let H19 
\def (f_equal C T (\lambda (e: C).(match e in C return (\lambda (_: C).T) 
with [(CSort _) \Rightarrow u | (CHead _ _ t) \Rightarrow t])) (CHead d (Bind 
Abbr) u) (CHead x1 (Bind x0) x3) H12) in (\lambda (H20: (eq B Abbr 
x0)).(\lambda (H21: (eq C d x1)).(let H22 \def (eq_ind_r T x3 (\lambda (t: 
T).(subst0 (minus i0 (S i)) u0 t x4)) H14 u H19) in (let H23 \def (eq_ind_r C 
x1 (\lambda (c0: C).(csubst0 (minus i0 (S i)) u0 c0 x2)) H15 d H21) in (let 
H24 \def (eq_ind_r B x0 (\lambda (b: B).(getl i c2 (CHead x2 (Bind b) x4))) 
H13 Abbr H20) in (arity_abbr g c2 x2 x4 i H24 a0 (H2 d1 u0 (r (Bind Abbr) 
(minus i0 (S i))) (getl_gen_S (Bind Abbr) d (CHead d1 (Bind Abbr) u0) u 
(minus i0 (S i)) H16) x2 x4 (fsubst0_both (r (Bind Abbr) (minus i0 (S i))) u0 
d u x4 H22 x2 H23))))))))) H18)) H17)))))))))))) H11)) H10))) (\lambda (H9: 
(le i0 i)).(arity_abbr g c2 d u i (csubst0_getl_ge i0 i H9 c c2 u0 H8 (CHead 
d (Bind Abbr) u) H0) a0 H1))) t2 H7))) H6)) (\lambda (H6: (land (subst0 i0 u0 
(TLRef i) t2) (csubst0 i0 u0 c c2))).(land_ind (subst0 i0 u0 (TLRef i) t2) 
(csubst0 i0 u0 c c2) (arity g c2 t2 a0) (\lambda (H7: (subst0 i0 u0 (TLRef i) 
t2)).(\lambda (H8: (csubst0 i0 u0 c c2)).(land_ind (eq nat i i0) (eq T t2 
(lift (S i) O u0)) (arity g c2 t2 a0) (\lambda (H9: (eq nat i i0)).(\lambda 
(H10: (eq T t2 (lift (S i) O u0))).(eq_ind_r T (lift (S i) O u0) (\lambda (t: 
T).(arity g c2 t a0)) (let H11 \def (eq_ind_r nat i0 (\lambda (n: 
nat).(csubst0 n u0 c c2)) H8 i H9) in (let H12 \def (eq_ind_r nat i0 (\lambda 
(n: nat).(getl n c (CHead d1 (Bind Abbr) u0))) H3 i H9) in (let H13 \def 
(eq_ind C (CHead d (Bind Abbr) u) (\lambda (c0: C).(getl i c c0)) H0 (CHead 
d1 (Bind Abbr) u0) (getl_mono c (CHead d (Bind Abbr) u) i H0 (CHead d1 (Bind 
Abbr) u0) H12)) in (let H14 \def (f_equal C C (\lambda (e: C).(match e in C 
return (\lambda (_: C).C) with [(CSort _) \Rightarrow d | (CHead c0 _ _) 
\Rightarrow c0])) (CHead d (Bind Abbr) u) (CHead d1 (Bind Abbr) u0) 
(getl_mono c (CHead d (Bind Abbr) u) i H0 (CHead d1 (Bind Abbr) u0) H12)) in 
((let H15 \def (f_equal C T (\lambda (e: C).(match e in C return (\lambda (_: 
C).T) with [(CSort _) \Rightarrow u | (CHead _ _ t) \Rightarrow t])) (CHead d 
(Bind Abbr) u) (CHead d1 (Bind Abbr) u0) (getl_mono c (CHead d (Bind Abbr) u) 
i H0 (CHead d1 (Bind Abbr) u0) H12)) in (\lambda (H16: (eq C d d1)).(let H17 
\def (eq_ind_r T u0 (\lambda (t: T).(getl i c (CHead d1 (Bind Abbr) t))) H13 
u H15) in (let H18 \def (eq_ind_r T u0 (\lambda (t: T).(csubst0 i t c c2)) 
H11 u H15) in (eq_ind T u (\lambda (t: T).(arity g c2 (lift (S i) O t) a0)) 
(let H19 \def (eq_ind_r C d1 (\lambda (c0: C).(getl i c (CHead c0 (Bind Abbr) 
u))) H17 d H16) in (arity_lift g d u a0 H1 c2 (S i) O (getl_drop Abbr c2 d u 
i (csubst0_getl_ge i i (le_n i) c c2 u H18 (CHead d (Bind Abbr) u) H19)))) u0 
H15))))) H14))))) t2 H10))) (subst0_gen_lref u0 t2 i0 i H7)))) H6)) 
H5)))))))))))))))))) (\lambda (c: C).(\lambda (d: C).(\lambda (u: T).(\lambda 
(i: nat).(\lambda (H0: (getl i c (CHead d (Bind Abst) u))).(\lambda (a0: 
A).(\lambda (H1: (arity g d u (asucc g a0))).(\lambda (H2: ((\forall (d1: 
C).(\forall (u0: T).(\forall (i0: nat).((getl i0 d (CHead d1 (Bind Abbr) u0)) 
\to (\forall (c2: C).(\forall (t2: T).((fsubst0 i0 u0 d u c2 t2) \to (arity g 
c2 t2 (asucc g a0))))))))))).(\lambda (d1: C).(\lambda (u0: T).(\lambda (i0: 
nat).(\lambda (H3: (getl i0 c (CHead d1 (Bind Abbr) u0))).(\lambda (c2: 
C).(\lambda (t2: T).(\lambda (H4: (fsubst0 i0 u0 c (TLRef i) c2 t2)).(let H_x 
\def (fsubst0_gen_base c c2 (TLRef i) t2 u0 i0 H4) in (let H5 \def H_x in 
(or3_ind (land (eq C c c2) (subst0 i0 u0 (TLRef i) t2)) (land (eq T (TLRef i) 
t2) (csubst0 i0 u0 c c2)) (land (subst0 i0 u0 (TLRef i) t2) (csubst0 i0 u0 c 
c2)) (arity g c2 t2 a0) (\lambda (H6: (land (eq C c c2) (subst0 i0 u0 (TLRef 
i) t2))).(land_ind (eq C c c2) (subst0 i0 u0 (TLRef i) t2) (arity g c2 t2 a0) 
(\lambda (H7: (eq C c c2)).(\lambda (H8: (subst0 i0 u0 (TLRef i) t2)).(eq_ind 
C c (\lambda (c0: C).(arity g c0 t2 a0)) (land_ind (eq nat i i0) (eq T t2 
(lift (S i) O u0)) (arity g c t2 a0) (\lambda (H9: (eq nat i i0)).(\lambda 
(H10: (eq T t2 (lift (S i) O u0))).(eq_ind_r T (lift (S i) O u0) (\lambda (t: 
T).(arity g c t a0)) (let H11 \def (eq_ind_r nat i0 (\lambda (n: nat).(getl n 
c (CHead d1 (Bind Abbr) u0))) H3 i H9) in (let H12 \def (eq_ind C (CHead d 
(Bind Abst) u) (\lambda (c0: C).(getl i c c0)) H0 (CHead d1 (Bind Abbr) u0) 
(getl_mono c (CHead d (Bind Abst) u) i H0 (CHead d1 (Bind Abbr) u0) H11)) in 
(let H13 \def (eq_ind C (CHead d (Bind Abst) u) (\lambda (ee: C).(match ee in 
C return (\lambda (_: C).Prop) with [(CSort _) \Rightarrow False | (CHead _ k 
_) \Rightarrow (match k in K return (\lambda (_: K).Prop) with [(Bind b) 
\Rightarrow (match b in B return (\lambda (_: B).Prop) with [Abbr \Rightarrow 
False | Abst \Rightarrow True | Void \Rightarrow False]) | (Flat _) 
\Rightarrow False])])) I (CHead d1 (Bind Abbr) u0) (getl_mono c (CHead d 
(Bind Abst) u) i H0 (CHead d1 (Bind Abbr) u0) H11)) in (False_ind (arity g c 
(lift (S i) O u0) a0) H13)))) t2 H10))) (subst0_gen_lref u0 t2 i0 i H8)) c2 
H7))) H6)) (\lambda (H6: (land (eq T (TLRef i) t2) (csubst0 i0 u0 c 
c2))).(land_ind (eq T (TLRef i) t2) (csubst0 i0 u0 c c2) (arity g c2 t2 a0) 
(\lambda (H7: (eq T (TLRef i) t2)).(\lambda (H8: (csubst0 i0 u0 c 
c2)).(eq_ind T (TLRef i) (\lambda (t: T).(arity g c2 t a0)) (lt_le_e i i0 
(arity g c2 (TLRef i) a0) (\lambda (H9: (lt i i0)).(let H10 \def 
(csubst0_getl_lt i0 i H9 c c2 u0 H8 (CHead d (Bind Abst) u) H0) in (or4_ind 
(getl i c2 (CHead d (Bind Abst) u)) (ex3_4 B C T T (\lambda (b: B).(\lambda 
(e0: C).(\lambda (u1: T).(\lambda (_: T).(eq C (CHead d (Bind Abst) u) (CHead 
e0 (Bind b) u1)))))) (\lambda (b: B).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(getl i c2 (CHead e0 (Bind b) w)))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (u1: T).(\lambda (w: T).(subst0 (minus i0 (S i)) 
u0 u1 w)))))) (ex3_4 B C C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u1: T).(eq C (CHead d (Bind Abst) u) (CHead e1 (Bind b) u1)))))) 
(\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u1: T).(getl i c2 
(CHead e2 (Bind b) u1)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 (minus i0 (S i)) u0 e1 e2)))))) (ex4_5 B C C T T 
(\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(_: T).(eq C (CHead d (Bind Abst) u) (CHead e1 (Bind b) u1))))))) (\lambda 
(b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(getl 
i c2 (CHead e2 (Bind b) w))))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (w: T).(subst0 (minus i0 (S i)) u0 u1 w)))))) 
(\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 (minus i0 (S i)) u0 e1 e2))))))) (arity g c2 (TLRef i) a0) 
(\lambda (H11: (getl i c2 (CHead d (Bind Abst) u))).(let H12 \def (eq_ind nat 
(minus i0 i) (\lambda (n: nat).(getl n (CHead d (Bind Abst) u) (CHead d1 
(Bind Abbr) u0))) (getl_conf_le i0 (CHead d1 (Bind Abbr) u0) c H3 (CHead d 
(Bind Abst) u) i H0 (le_S_n i i0 (le_S (S i) i0 H9))) (S (minus i0 (S i))) 
(minus_x_Sy i0 i H9)) in (arity_abst g c2 d u i H11 a0 H1))) (\lambda (H11: 
(ex3_4 B C T T (\lambda (b: B).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: 
T).(eq C (CHead d (Bind Abst) u) (CHead e0 (Bind b) u1)))))) (\lambda (b: 
B).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(getl i c2 (CHead e0 
(Bind b) w)))))) (\lambda (_: B).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(w: T).(subst0 (minus i0 (S i)) u0 u1 w))))))).(ex3_4_ind B C T T (\lambda 
(b: B).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: T).(eq C (CHead d (Bind 
Abst) u) (CHead e0 (Bind b) u1)))))) (\lambda (b: B).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (w: T).(getl i c2 (CHead e0 (Bind b) w)))))) 
(\lambda (_: B).(\lambda (_: C).(\lambda (u1: T).(\lambda (w: T).(subst0 
(minus i0 (S i)) u0 u1 w))))) (arity g c2 (TLRef i) a0) (\lambda (x0: 
B).(\lambda (x1: C).(\lambda (x2: T).(\lambda (x3: T).(\lambda (H12: (eq C 
(CHead d (Bind Abst) u) (CHead x1 (Bind x0) x2))).(\lambda (H13: (getl i c2 
(CHead x1 (Bind x0) x3))).(\lambda (H14: (subst0 (minus i0 (S i)) u0 x2 
x3)).(let H15 \def (eq_ind nat (minus i0 i) (\lambda (n: nat).(getl n (CHead 
d (Bind Abst) u) (CHead d1 (Bind Abbr) u0))) (getl_conf_le i0 (CHead d1 (Bind 
Abbr) u0) c H3 (CHead d (Bind Abst) u) i H0 (le_S_n i i0 (le_S (S i) i0 H9))) 
(S (minus i0 (S i))) (minus_x_Sy i0 i H9)) in (let H16 \def (f_equal C C 
(\lambda (e: C).(match e in C return (\lambda (_: C).C) with [(CSort _) 
\Rightarrow d | (CHead c0 _ _) \Rightarrow c0])) (CHead d (Bind Abst) u) 
(CHead x1 (Bind x0) x2) H12) in ((let H17 \def (f_equal C B (\lambda (e: 
C).(match e in C return (\lambda (_: C).B) with [(CSort _) \Rightarrow Abst | 
(CHead _ k _) \Rightarrow (match k in K return (\lambda (_: K).B) with [(Bind 
b) \Rightarrow b | (Flat _) \Rightarrow Abst])])) (CHead d (Bind Abst) u) 
(CHead x1 (Bind x0) x2) H12) in ((let H18 \def (f_equal C T (\lambda (e: 
C).(match e in C return (\lambda (_: C).T) with [(CSort _) \Rightarrow u | 
(CHead _ _ t) \Rightarrow t])) (CHead d (Bind Abst) u) (CHead x1 (Bind x0) 
x2) H12) in (\lambda (H19: (eq B Abst x0)).(\lambda (H20: (eq C d x1)).(let 
H21 \def (eq_ind_r T x2 (\lambda (t: T).(subst0 (minus i0 (S i)) u0 t x3)) 
H14 u H18) in (let H22 \def (eq_ind_r C x1 (\lambda (c0: C).(getl i c2 (CHead 
c0 (Bind x0) x3))) H13 d H20) in (let H23 \def (eq_ind_r B x0 (\lambda (b: 
B).(getl i c2 (CHead d (Bind b) x3))) H22 Abst H19) in (arity_abst g c2 d x3 
i H23 a0 (H2 d1 u0 (r (Bind Abst) (minus i0 (S i))) (getl_gen_S (Bind Abst) d 
(CHead d1 (Bind Abbr) u0) u (minus i0 (S i)) H15) d x3 (fsubst0_snd (r (Bind 
Abst) (minus i0 (S i))) u0 d u x3 H21))))))))) H17)) H16)))))))))) H11)) 
(\lambda (H11: (ex3_4 B C C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u1: T).(eq C (CHead d (Bind Abst) u) (CHead e1 (Bind b) u1)))))) 
(\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u1: T).(getl i c2 
(CHead e2 (Bind b) u1)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 (minus i0 (S i)) u0 e1 e2))))))).(ex3_4_ind B C C 
T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(eq C 
(CHead d (Bind Abst) u) (CHead e1 (Bind b) u1)))))) (\lambda (b: B).(\lambda 
(_: C).(\lambda (e2: C).(\lambda (u1: T).(getl i c2 (CHead e2 (Bind b) 
u1)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 (minus i0 (S i)) u0 e1 e2))))) (arity g c2 (TLRef i) a0) (\lambda 
(x0: B).(\lambda (x1: C).(\lambda (x2: C).(\lambda (x3: T).(\lambda (H12: (eq 
C (CHead d (Bind Abst) u) (CHead x1 (Bind x0) x3))).(\lambda (H13: (getl i c2 
(CHead x2 (Bind x0) x3))).(\lambda (H14: (csubst0 (minus i0 (S i)) u0 x1 
x2)).(let H15 \def (eq_ind nat (minus i0 i) (\lambda (n: nat).(getl n (CHead 
d (Bind Abst) u) (CHead d1 (Bind Abbr) u0))) (getl_conf_le i0 (CHead d1 (Bind 
Abbr) u0) c H3 (CHead d (Bind Abst) u) i H0 (le_S_n i i0 (le_S (S i) i0 H9))) 
(S (minus i0 (S i))) (minus_x_Sy i0 i H9)) in (let H16 \def (f_equal C C 
(\lambda (e: C).(match e in C return (\lambda (_: C).C) with [(CSort _) 
\Rightarrow d | (CHead c0 _ _) \Rightarrow c0])) (CHead d (Bind Abst) u) 
(CHead x1 (Bind x0) x3) H12) in ((let H17 \def (f_equal C B (\lambda (e: 
C).(match e in C return (\lambda (_: C).B) with [(CSort _) \Rightarrow Abst | 
(CHead _ k _) \Rightarrow (match k in K return (\lambda (_: K).B) with [(Bind 
b) \Rightarrow b | (Flat _) \Rightarrow Abst])])) (CHead d (Bind Abst) u) 
(CHead x1 (Bind x0) x3) H12) in ((let H18 \def (f_equal C T (\lambda (e: 
C).(match e in C return (\lambda (_: C).T) with [(CSort _) \Rightarrow u | 
(CHead _ _ t) \Rightarrow t])) (CHead d (Bind Abst) u) (CHead x1 (Bind x0) 
x3) H12) in (\lambda (H19: (eq B Abst x0)).(\lambda (H20: (eq C d x1)).(let 
H21 \def (eq_ind_r T x3 (\lambda (t: T).(getl i c2 (CHead x2 (Bind x0) t))) 
H13 u H18) in (let H22 \def (eq_ind_r C x1 (\lambda (c0: C).(csubst0 (minus 
i0 (S i)) u0 c0 x2)) H14 d H20) in (let H23 \def (eq_ind_r B x0 (\lambda (b: 
B).(getl i c2 (CHead x2 (Bind b) u))) H21 Abst H19) in (arity_abst g c2 x2 u 
i H23 a0 (H2 d1 u0 (r (Bind Abst) (minus i0 (S i))) (getl_gen_S (Bind Abst) d 
(CHead d1 (Bind Abbr) u0) u (minus i0 (S i)) H15) x2 u (fsubst0_fst (r (Bind 
Abst) (minus i0 (S i))) u0 d u x2 H22))))))))) H17)) H16)))))))))) H11)) 
(\lambda (H11: (ex4_5 B C C T T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (_: T).(eq C (CHead d (Bind Abst) u) (CHead e1 
(Bind b) u1))))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (w: T).(getl i c2 (CHead e2 (Bind b) w))))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (w: T).(subst0 
(minus i0 (S i)) u0 u1 w)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus i0 (S i)) u0 e1 
e2)))))))).(ex4_5_ind B C C T T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (_: T).(eq C (CHead d (Bind Abst) u) (CHead e1 
(Bind b) u1))))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (w: T).(getl i c2 (CHead e2 (Bind b) w))))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (w: T).(subst0 
(minus i0 (S i)) u0 u1 w)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus i0 (S i)) u0 e1 e2)))))) 
(arity g c2 (TLRef i) a0) (\lambda (x0: B).(\lambda (x1: C).(\lambda (x2: 
C).(\lambda (x3: T).(\lambda (x4: T).(\lambda (H12: (eq C (CHead d (Bind 
Abst) u) (CHead x1 (Bind x0) x3))).(\lambda (H13: (getl i c2 (CHead x2 (Bind 
x0) x4))).(\lambda (H14: (subst0 (minus i0 (S i)) u0 x3 x4)).(\lambda (H15: 
(csubst0 (minus i0 (S i)) u0 x1 x2)).(let H16 \def (eq_ind nat (minus i0 i) 
(\lambda (n: nat).(getl n (CHead d (Bind Abst) u) (CHead d1 (Bind Abbr) u0))) 
(getl_conf_le i0 (CHead d1 (Bind Abbr) u0) c H3 (CHead d (Bind Abst) u) i H0 
(le_S_n i i0 (le_S (S i) i0 H9))) (S (minus i0 (S i))) (minus_x_Sy i0 i H9)) 
in (let H17 \def (f_equal C C (\lambda (e: C).(match e in C return (\lambda 
(_: C).C) with [(CSort _) \Rightarrow d | (CHead c0 _ _) \Rightarrow c0])) 
(CHead d (Bind Abst) u) (CHead x1 (Bind x0) x3) H12) in ((let H18 \def 
(f_equal C B (\lambda (e: C).(match e in C return (\lambda (_: C).B) with 
[(CSort _) \Rightarrow Abst | (CHead _ k _) \Rightarrow (match k in K return 
(\lambda (_: K).B) with [(Bind b) \Rightarrow b | (Flat _) \Rightarrow 
Abst])])) (CHead d (Bind Abst) u) (CHead x1 (Bind x0) x3) H12) in ((let H19 
\def (f_equal C T (\lambda (e: C).(match e in C return (\lambda (_: C).T) 
with [(CSort _) \Rightarrow u | (CHead _ _ t) \Rightarrow t])) (CHead d (Bind 
Abst) u) (CHead x1 (Bind x0) x3) H12) in (\lambda (H20: (eq B Abst 
x0)).(\lambda (H21: (eq C d x1)).(let H22 \def (eq_ind_r T x3 (\lambda (t: 
T).(subst0 (minus i0 (S i)) u0 t x4)) H14 u H19) in (let H23 \def (eq_ind_r C 
x1 (\lambda (c0: C).(csubst0 (minus i0 (S i)) u0 c0 x2)) H15 d H21) in (let 
H24 \def (eq_ind_r B x0 (\lambda (b: B).(getl i c2 (CHead x2 (Bind b) x4))) 
H13 Abst H20) in (arity_abst g c2 x2 x4 i H24 a0 (H2 d1 u0 (r (Bind Abst) 
(minus i0 (S i))) (getl_gen_S (Bind Abst) d (CHead d1 (Bind Abbr) u0) u 
(minus i0 (S i)) H16) x2 x4 (fsubst0_both (r (Bind Abst) (minus i0 (S i))) u0 
d u x4 H22 x2 H23))))))))) H18)) H17)))))))))))) H11)) H10))) (\lambda (H9: 
(le i0 i)).(arity_abst g c2 d u i (csubst0_getl_ge i0 i H9 c c2 u0 H8 (CHead 
d (Bind Abst) u) H0) a0 H1))) t2 H7))) H6)) (\lambda (H6: (land (subst0 i0 u0 
(TLRef i) t2) (csubst0 i0 u0 c c2))).(land_ind (subst0 i0 u0 (TLRef i) t2) 
(csubst0 i0 u0 c c2) (arity g c2 t2 a0) (\lambda (H7: (subst0 i0 u0 (TLRef i) 
t2)).(\lambda (H8: (csubst0 i0 u0 c c2)).(land_ind (eq nat i i0) (eq T t2 
(lift (S i) O u0)) (arity g c2 t2 a0) (\lambda (H9: (eq nat i i0)).(\lambda 
(H10: (eq T t2 (lift (S i) O u0))).(eq_ind_r T (lift (S i) O u0) (\lambda (t: 
T).(arity g c2 t a0)) (let H11 \def (eq_ind_r nat i0 (\lambda (n: 
nat).(csubst0 n u0 c c2)) H8 i H9) in (let H12 \def (eq_ind_r nat i0 (\lambda 
(n: nat).(getl n c (CHead d1 (Bind Abbr) u0))) H3 i H9) in (let H13 \def 
(eq_ind C (CHead d (Bind Abst) u) (\lambda (c0: C).(getl i c c0)) H0 (CHead 
d1 (Bind Abbr) u0) (getl_mono c (CHead d (Bind Abst) u) i H0 (CHead d1 (Bind 
Abbr) u0) H12)) in (let H14 \def (eq_ind C (CHead d (Bind Abst) u) (\lambda 
(ee: C).(match ee in C return (\lambda (_: C).Prop) with [(CSort _) 
\Rightarrow False | (CHead _ k _) \Rightarrow (match k in K return (\lambda 
(_: K).Prop) with [(Bind b) \Rightarrow (match b in B return (\lambda (_: 
B).Prop) with [Abbr \Rightarrow False | Abst \Rightarrow True | Void 
\Rightarrow False]) | (Flat _) \Rightarrow False])])) I (CHead d1 (Bind Abbr) 
u0) (getl_mono c (CHead d (Bind Abst) u) i H0 (CHead d1 (Bind Abbr) u0) H12)) 
in (False_ind (arity g c2 (lift (S i) O u0) a0) H14))))) t2 H10))) 
(subst0_gen_lref u0 t2 i0 i H7)))) H6)) H5)))))))))))))))))) (\lambda (b: 
B).(\lambda (H0: (not (eq B b Abst))).(\lambda (c: C).(\lambda (u: 
T).(\lambda (a1: A).(\lambda (H1: (arity g c u a1)).(\lambda (H2: ((\forall 
(d1: C).(\forall (u0: T).(\forall (i: nat).((getl i c (CHead d1 (Bind Abbr) 
u0)) \to (\forall (c2: C).(\forall (t2: T).((fsubst0 i u0 c u c2 t2) \to 
(arity g c2 t2 a1)))))))))).(\lambda (t: T).(\lambda (a2: A).(\lambda (_: 
(arity g (CHead c (Bind b) u) t a2)).(\lambda (H4: ((\forall (d1: C).(\forall 
(u0: T).(\forall (i: nat).((getl i (CHead c (Bind b) u) (CHead d1 (Bind Abbr) 
u0)) \to (\forall (c2: C).(\forall (t2: T).((fsubst0 i u0 (CHead c (Bind b) 
u) t c2 t2) \to (arity g c2 t2 a2)))))))))).(\lambda (d1: C).(\lambda (u0: 
T).(\lambda (i: nat).(\lambda (H5: (getl i c (CHead d1 (Bind Abbr) 
u0))).(\lambda (c2: C).(\lambda (t2: T).(\lambda (H6: (fsubst0 i u0 c (THead 
(Bind b) u t) c2 t2)).(let H_x \def (fsubst0_gen_base c c2 (THead (Bind b) u 
t) t2 u0 i H6) in (let H7 \def H_x in (or3_ind (land (eq C c c2) (subst0 i u0 
(THead (Bind b) u t) t2)) (land (eq T (THead (Bind b) u t) t2) (csubst0 i u0 
c c2)) (land (subst0 i u0 (THead (Bind b) u t) t2) (csubst0 i u0 c c2)) 
(arity g c2 t2 a2) (\lambda (H8: (land (eq C c c2) (subst0 i u0 (THead (Bind 
b) u t) t2))).(land_ind (eq C c c2) (subst0 i u0 (THead (Bind b) u t) t2) 
(arity g c2 t2 a2) (\lambda (H9: (eq C c c2)).(\lambda (H10: (subst0 i u0 
(THead (Bind b) u t) t2)).(eq_ind C c (\lambda (c0: C).(arity g c0 t2 a2)) 
(or3_ind (ex2 T (\lambda (u2: T).(eq T t2 (THead (Bind b) u2 t))) (\lambda 
(u2: T).(subst0 i u0 u u2))) (ex2 T (\lambda (t3: T).(eq T t2 (THead (Bind b) 
u t3))) (\lambda (t3: T).(subst0 (s (Bind b) i) u0 t t3))) (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind b) u2 t3)))) (\lambda 
(u2: T).(\lambda (_: T).(subst0 i u0 u u2))) (\lambda (_: T).(\lambda (t3: 
T).(subst0 (s (Bind b) i) u0 t t3)))) (arity g c t2 a2) (\lambda (H11: (ex2 T 
(\lambda (u2: T).(eq T t2 (THead (Bind b) u2 t))) (\lambda (u2: T).(subst0 i 
u0 u u2)))).(ex2_ind T (\lambda (u2: T).(eq T t2 (THead (Bind b) u2 t))) 
(\lambda (u2: T).(subst0 i u0 u u2)) (arity g c t2 a2) (\lambda (x: 
T).(\lambda (H12: (eq T t2 (THead (Bind b) x t))).(\lambda (H13: (subst0 i u0 
u x)).(eq_ind_r T (THead (Bind b) x t) (\lambda (t0: T).(arity g c t0 a2)) 
(arity_bind g b H0 c x a1 (H2 d1 u0 i H5 c x (fsubst0_snd i u0 c u x H13)) t 
a2 (H4 d1 u0 (S i) (getl_clear_bind b (CHead c (Bind b) u) c u (clear_bind b 
c u) (CHead d1 (Bind Abbr) u0) i H5) (CHead c (Bind b) x) t (fsubst0_fst (S 
i) u0 (CHead c (Bind b) u) t (CHead c (Bind b) x) (csubst0_snd_bind b i u0 u 
x H13 c)))) t2 H12)))) H11)) (\lambda (H11: (ex2 T (\lambda (t3: T).(eq T t2 
(THead (Bind b) u t3))) (\lambda (t3: T).(subst0 (s (Bind b) i) u0 t 
t3)))).(ex2_ind T (\lambda (t3: T).(eq T t2 (THead (Bind b) u t3))) (\lambda 
(t3: T).(subst0 (s (Bind b) i) u0 t t3)) (arity g c t2 a2) (\lambda (x: 
T).(\lambda (H12: (eq T t2 (THead (Bind b) u x))).(\lambda (H13: (subst0 (s 
(Bind b) i) u0 t x)).(eq_ind_r T (THead (Bind b) u x) (\lambda (t0: T).(arity 
g c t0 a2)) (arity_bind g b H0 c u a1 H1 x a2 (H4 d1 u0 (S i) 
(getl_clear_bind b (CHead c (Bind b) u) c u (clear_bind b c u) (CHead d1 
(Bind Abbr) u0) i H5) (CHead c (Bind b) u) x (fsubst0_snd (S i) u0 (CHead c 
(Bind b) u) t x H13))) t2 H12)))) H11)) (\lambda (H11: (ex3_2 T T (\lambda 
(u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind b) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(subst0 i u0 u u2))) (\lambda (_: T).(\lambda (t3: 
T).(subst0 (s (Bind b) i) u0 t t3))))).(ex3_2_ind T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T t2 (THead (Bind b) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(subst0 i u0 u u2))) (\lambda (_: T).(\lambda (t3: 
T).(subst0 (s (Bind b) i) u0 t t3))) (arity g c t2 a2) (\lambda (x0: 
T).(\lambda (x1: T).(\lambda (H12: (eq T t2 (THead (Bind b) x0 x1))).(\lambda 
(H13: (subst0 i u0 u x0)).(\lambda (H14: (subst0 (s (Bind b) i) u0 t 
x1)).(eq_ind_r T (THead (Bind b) x0 x1) (\lambda (t0: T).(arity g c t0 a2)) 
(arity_bind g b H0 c x0 a1 (H2 d1 u0 i H5 c x0 (fsubst0_snd i u0 c u x0 H13)) 
x1 a2 (H4 d1 u0 (S i) (getl_clear_bind b (CHead c (Bind b) u) c u (clear_bind 
b c u) (CHead d1 (Bind Abbr) u0) i H5) (CHead c (Bind b) x0) x1 (fsubst0_both 
(S i) u0 (CHead c (Bind b) u) t x1 H14 (CHead c (Bind b) x0) 
(csubst0_snd_bind b i u0 u x0 H13 c)))) t2 H12)))))) H11)) (subst0_gen_head 
(Bind b) u0 u t t2 i H10)) c2 H9))) H8)) (\lambda (H8: (land (eq T (THead 
(Bind b) u t) t2) (csubst0 i u0 c c2))).(land_ind (eq T (THead (Bind b) u t) 
t2) (csubst0 i u0 c c2) (arity g c2 t2 a2) (\lambda (H9: (eq T (THead (Bind 
b) u t) t2)).(\lambda (H10: (csubst0 i u0 c c2)).(eq_ind T (THead (Bind b) u 
t) (\lambda (t0: T).(arity g c2 t0 a2)) (arity_bind g b H0 c2 u a1 (H2 d1 u0 
i H5 c2 u (fsubst0_fst i u0 c u c2 H10)) t a2 (H4 d1 u0 (S i) 
(getl_clear_bind b (CHead c (Bind b) u) c u (clear_bind b c u) (CHead d1 
(Bind Abbr) u0) i H5) (CHead c2 (Bind b) u) t (fsubst0_fst (S i) u0 (CHead c 
(Bind b) u) t (CHead c2 (Bind b) u) (csubst0_fst_bind b i c c2 u0 H10 u)))) 
t2 H9))) H8)) (\lambda (H8: (land (subst0 i u0 (THead (Bind b) u t) t2) 
(csubst0 i u0 c c2))).(land_ind (subst0 i u0 (THead (Bind b) u t) t2) 
(csubst0 i u0 c c2) (arity g c2 t2 a2) (\lambda (H9: (subst0 i u0 (THead 
(Bind b) u t) t2)).(\lambda (H10: (csubst0 i u0 c c2)).(or3_ind (ex2 T 
(\lambda (u2: T).(eq T t2 (THead (Bind b) u2 t))) (\lambda (u2: T).(subst0 i 
u0 u u2))) (ex2 T (\lambda (t3: T).(eq T t2 (THead (Bind b) u t3))) (\lambda 
(t3: T).(subst0 (s (Bind b) i) u0 t t3))) (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T t2 (THead (Bind b) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(subst0 i u0 u u2))) (\lambda (_: T).(\lambda (t3: 
T).(subst0 (s (Bind b) i) u0 t t3)))) (arity g c2 t2 a2) (\lambda (H11: (ex2 
T (\lambda (u2: T).(eq T t2 (THead (Bind b) u2 t))) (\lambda (u2: T).(subst0 
i u0 u u2)))).(ex2_ind T (\lambda (u2: T).(eq T t2 (THead (Bind b) u2 t))) 
(\lambda (u2: T).(subst0 i u0 u u2)) (arity g c2 t2 a2) (\lambda (x: 
T).(\lambda (H12: (eq T t2 (THead (Bind b) x t))).(\lambda (H13: (subst0 i u0 
u x)).(eq_ind_r T (THead (Bind b) x t) (\lambda (t0: T).(arity g c2 t0 a2)) 
(arity_bind g b H0 c2 x a1 (H2 d1 u0 i H5 c2 x (fsubst0_both i u0 c u x H13 
c2 H10)) t a2 (H4 d1 u0 (S i) (getl_clear_bind b (CHead c (Bind b) u) c u 
(clear_bind b c u) (CHead d1 (Bind Abbr) u0) i H5) (CHead c2 (Bind b) x) t 
(fsubst0_fst (S i) u0 (CHead c (Bind b) u) t (CHead c2 (Bind b) x) 
(csubst0_both_bind b i u0 u x H13 c c2 H10)))) t2 H12)))) H11)) (\lambda 
(H11: (ex2 T (\lambda (t3: T).(eq T t2 (THead (Bind b) u t3))) (\lambda (t3: 
T).(subst0 (s (Bind b) i) u0 t t3)))).(ex2_ind T (\lambda (t3: T).(eq T t2 
(THead (Bind b) u t3))) (\lambda (t3: T).(subst0 (s (Bind b) i) u0 t t3)) 
(arity g c2 t2 a2) (\lambda (x: T).(\lambda (H12: (eq T t2 (THead (Bind b) u 
x))).(\lambda (H13: (subst0 (s (Bind b) i) u0 t x)).(eq_ind_r T (THead (Bind 
b) u x) (\lambda (t0: T).(arity g c2 t0 a2)) (arity_bind g b H0 c2 u a1 (H2 
d1 u0 i H5 c2 u (fsubst0_fst i u0 c u c2 H10)) x a2 (H4 d1 u0 (S i) 
(getl_clear_bind b (CHead c (Bind b) u) c u (clear_bind b c u) (CHead d1 
(Bind Abbr) u0) i H5) (CHead c2 (Bind b) u) x (fsubst0_both (S i) u0 (CHead c 
(Bind b) u) t x H13 (CHead c2 (Bind b) u) (csubst0_fst_bind b i c c2 u0 H10 
u)))) t2 H12)))) H11)) (\lambda (H11: (ex3_2 T T (\lambda (u2: T).(\lambda 
(t3: T).(eq T t2 (THead (Bind b) u2 t3)))) (\lambda (u2: T).(\lambda (_: 
T).(subst0 i u0 u u2))) (\lambda (_: T).(\lambda (t3: T).(subst0 (s (Bind b) 
i) u0 t t3))))).(ex3_2_ind T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 
(THead (Bind b) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(subst0 i u0 u 
u2))) (\lambda (_: T).(\lambda (t3: T).(subst0 (s (Bind b) i) u0 t t3))) 
(arity g c2 t2 a2) (\lambda (x0: T).(\lambda (x1: T).(\lambda (H12: (eq T t2 
(THead (Bind b) x0 x1))).(\lambda (H13: (subst0 i u0 u x0)).(\lambda (H14: 
(subst0 (s (Bind b) i) u0 t x1)).(eq_ind_r T (THead (Bind b) x0 x1) (\lambda 
(t0: T).(arity g c2 t0 a2)) (arity_bind g b H0 c2 x0 a1 (H2 d1 u0 i H5 c2 x0 
(fsubst0_both i u0 c u x0 H13 c2 H10)) x1 a2 (H4 d1 u0 (S i) (getl_clear_bind 
b (CHead c (Bind b) u) c u (clear_bind b c u) (CHead d1 (Bind Abbr) u0) i H5) 
(CHead c2 (Bind b) x0) x1 (fsubst0_both (S i) u0 (CHead c (Bind b) u) t x1 
H14 (CHead c2 (Bind b) x0) (csubst0_both_bind b i u0 u x0 H13 c c2 H10)))) t2 
H12)))))) H11)) (subst0_gen_head (Bind b) u0 u t t2 i H9)))) H8)) 
H7))))))))))))))))))))) (\lambda (c: C).(\lambda (u: T).(\lambda (a1: 
A).(\lambda (H0: (arity g c u (asucc g a1))).(\lambda (H1: ((\forall (d1: 
C).(\forall (u0: T).(\forall (i: nat).((getl i c (CHead d1 (Bind Abbr) u0)) 
\to (\forall (c2: C).(\forall (t2: T).((fsubst0 i u0 c u c2 t2) \to (arity g 
c2 t2 (asucc g a1))))))))))).(\lambda (t: T).(\lambda (a2: A).(\lambda (_: 
(arity g (CHead c (Bind Abst) u) t a2)).(\lambda (H3: ((\forall (d1: 
C).(\forall (u0: T).(\forall (i: nat).((getl i (CHead c (Bind Abst) u) (CHead 
d1 (Bind Abbr) u0)) \to (\forall (c2: C).(\forall (t2: T).((fsubst0 i u0 
(CHead c (Bind Abst) u) t c2 t2) \to (arity g c2 t2 a2)))))))))).(\lambda 
(d1: C).(\lambda (u0: T).(\lambda (i: nat).(\lambda (H4: (getl i c (CHead d1 
(Bind Abbr) u0))).(\lambda (c2: C).(\lambda (t2: T).(\lambda (H5: (fsubst0 i 
u0 c (THead (Bind Abst) u t) c2 t2)).(let H_x \def (fsubst0_gen_base c c2 
(THead (Bind Abst) u t) t2 u0 i H5) in (let H6 \def H_x in (or3_ind (land (eq 
C c c2) (subst0 i u0 (THead (Bind Abst) u t) t2)) (land (eq T (THead (Bind 
Abst) u t) t2) (csubst0 i u0 c c2)) (land (subst0 i u0 (THead (Bind Abst) u 
t) t2) (csubst0 i u0 c c2)) (arity g c2 t2 (AHead a1 a2)) (\lambda (H7: (land 
(eq C c c2) (subst0 i u0 (THead (Bind Abst) u t) t2))).(land_ind (eq C c c2) 
(subst0 i u0 (THead (Bind Abst) u t) t2) (arity g c2 t2 (AHead a1 a2)) 
(\lambda (H8: (eq C c c2)).(\lambda (H9: (subst0 i u0 (THead (Bind Abst) u t) 
t2)).(eq_ind C c (\lambda (c0: C).(arity g c0 t2 (AHead a1 a2))) (or3_ind 
(ex2 T (\lambda (u2: T).(eq T t2 (THead (Bind Abst) u2 t))) (\lambda (u2: 
T).(subst0 i u0 u u2))) (ex2 T (\lambda (t3: T).(eq T t2 (THead (Bind Abst) u 
t3))) (\lambda (t3: T).(subst0 (s (Bind Abst) i) u0 t t3))) (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind Abst) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(subst0 i u0 u u2))) (\lambda (_: 
T).(\lambda (t3: T).(subst0 (s (Bind Abst) i) u0 t t3)))) (arity g c t2 
(AHead a1 a2)) (\lambda (H10: (ex2 T (\lambda (u2: T).(eq T t2 (THead (Bind 
Abst) u2 t))) (\lambda (u2: T).(subst0 i u0 u u2)))).(ex2_ind T (\lambda (u2: 
T).(eq T t2 (THead (Bind Abst) u2 t))) (\lambda (u2: T).(subst0 i u0 u u2)) 
(arity g c t2 (AHead a1 a2)) (\lambda (x: T).(\lambda (H11: (eq T t2 (THead 
(Bind Abst) x t))).(\lambda (H12: (subst0 i u0 u x)).(eq_ind_r T (THead (Bind 
Abst) x t) (\lambda (t0: T).(arity g c t0 (AHead a1 a2))) (arity_head g c x 
a1 (H1 d1 u0 i H4 c x (fsubst0_snd i u0 c u x H12)) t a2 (H3 d1 u0 (S i) 
(getl_clear_bind Abst (CHead c (Bind Abst) u) c u (clear_bind Abst c u) 
(CHead d1 (Bind Abbr) u0) i H4) (CHead c (Bind Abst) x) t (fsubst0_fst (S i) 
u0 (CHead c (Bind Abst) u) t (CHead c (Bind Abst) x) (csubst0_snd_bind Abst i 
u0 u x H12 c)))) t2 H11)))) H10)) (\lambda (H10: (ex2 T (\lambda (t3: T).(eq 
T t2 (THead (Bind Abst) u t3))) (\lambda (t3: T).(subst0 (s (Bind Abst) i) u0 
t t3)))).(ex2_ind T (\lambda (t3: T).(eq T t2 (THead (Bind Abst) u t3))) 
(\lambda (t3: T).(subst0 (s (Bind Abst) i) u0 t t3)) (arity g c t2 (AHead a1 
a2)) (\lambda (x: T).(\lambda (H11: (eq T t2 (THead (Bind Abst) u 
x))).(\lambda (H12: (subst0 (s (Bind Abst) i) u0 t x)).(eq_ind_r T (THead 
(Bind Abst) u x) (\lambda (t0: T).(arity g c t0 (AHead a1 a2))) (arity_head g 
c u a1 H0 x a2 (H3 d1 u0 (S i) (getl_clear_bind Abst (CHead c (Bind Abst) u) 
c u (clear_bind Abst c u) (CHead d1 (Bind Abbr) u0) i H4) (CHead c (Bind 
Abst) u) x (fsubst0_snd (S i) u0 (CHead c (Bind Abst) u) t x H12))) t2 
H11)))) H10)) (\lambda (H10: (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq 
T t2 (THead (Bind Abst) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(subst0 i 
u0 u u2))) (\lambda (_: T).(\lambda (t3: T).(subst0 (s (Bind Abst) i) u0 t 
t3))))).(ex3_2_ind T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead 
(Bind Abst) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(subst0 i u0 u u2))) 
(\lambda (_: T).(\lambda (t3: T).(subst0 (s (Bind Abst) i) u0 t t3))) (arity 
g c t2 (AHead a1 a2)) (\lambda (x0: T).(\lambda (x1: T).(\lambda (H11: (eq T 
t2 (THead (Bind Abst) x0 x1))).(\lambda (H12: (subst0 i u0 u x0)).(\lambda 
(H13: (subst0 (s (Bind Abst) i) u0 t x1)).(eq_ind_r T (THead (Bind Abst) x0 
x1) (\lambda (t0: T).(arity g c t0 (AHead a1 a2))) (arity_head g c x0 a1 (H1 
d1 u0 i H4 c x0 (fsubst0_snd i u0 c u x0 H12)) x1 a2 (H3 d1 u0 (S i) 
(getl_clear_bind Abst (CHead c (Bind Abst) u) c u (clear_bind Abst c u) 
(CHead d1 (Bind Abbr) u0) i H4) (CHead c (Bind Abst) x0) x1 (fsubst0_both (S 
i) u0 (CHead c (Bind Abst) u) t x1 H13 (CHead c (Bind Abst) x0) 
(csubst0_snd_bind Abst i u0 u x0 H12 c)))) t2 H11)))))) H10)) 
(subst0_gen_head (Bind Abst) u0 u t t2 i H9)) c2 H8))) H7)) (\lambda (H7: 
(land (eq T (THead (Bind Abst) u t) t2) (csubst0 i u0 c c2))).(land_ind (eq T 
(THead (Bind Abst) u t) t2) (csubst0 i u0 c c2) (arity g c2 t2 (AHead a1 a2)) 
(\lambda (H8: (eq T (THead (Bind Abst) u t) t2)).(\lambda (H9: (csubst0 i u0 
c c2)).(eq_ind T (THead (Bind Abst) u t) (\lambda (t0: T).(arity g c2 t0 
(AHead a1 a2))) (arity_head g c2 u a1 (H1 d1 u0 i H4 c2 u (fsubst0_fst i u0 c 
u c2 H9)) t a2 (H3 d1 u0 (S i) (getl_clear_bind Abst (CHead c (Bind Abst) u) 
c u (clear_bind Abst c u) (CHead d1 (Bind Abbr) u0) i H4) (CHead c2 (Bind 
Abst) u) t (fsubst0_fst (S i) u0 (CHead c (Bind Abst) u) t (CHead c2 (Bind 
Abst) u) (csubst0_fst_bind Abst i c c2 u0 H9 u)))) t2 H8))) H7)) (\lambda 
(H7: (land (subst0 i u0 (THead (Bind Abst) u t) t2) (csubst0 i u0 c 
c2))).(land_ind (subst0 i u0 (THead (Bind Abst) u t) t2) (csubst0 i u0 c c2) 
(arity g c2 t2 (AHead a1 a2)) (\lambda (H8: (subst0 i u0 (THead (Bind Abst) u 
t) t2)).(\lambda (H9: (csubst0 i u0 c c2)).(or3_ind (ex2 T (\lambda (u2: 
T).(eq T t2 (THead (Bind Abst) u2 t))) (\lambda (u2: T).(subst0 i u0 u u2))) 
(ex2 T (\lambda (t3: T).(eq T t2 (THead (Bind Abst) u t3))) (\lambda (t3: 
T).(subst0 (s (Bind Abst) i) u0 t t3))) (ex3_2 T T (\lambda (u2: T).(\lambda 
(t3: T).(eq T t2 (THead (Bind Abst) u2 t3)))) (\lambda (u2: T).(\lambda (_: 
T).(subst0 i u0 u u2))) (\lambda (_: T).(\lambda (t3: T).(subst0 (s (Bind 
Abst) i) u0 t t3)))) (arity g c2 t2 (AHead a1 a2)) (\lambda (H10: (ex2 T 
(\lambda (u2: T).(eq T t2 (THead (Bind Abst) u2 t))) (\lambda (u2: T).(subst0 
i u0 u u2)))).(ex2_ind T (\lambda (u2: T).(eq T t2 (THead (Bind Abst) u2 t))) 
(\lambda (u2: T).(subst0 i u0 u u2)) (arity g c2 t2 (AHead a1 a2)) (\lambda 
(x: T).(\lambda (H11: (eq T t2 (THead (Bind Abst) x t))).(\lambda (H12: 
(subst0 i u0 u x)).(eq_ind_r T (THead (Bind Abst) x t) (\lambda (t0: 
T).(arity g c2 t0 (AHead a1 a2))) (arity_head g c2 x a1 (H1 d1 u0 i H4 c2 x 
(fsubst0_both i u0 c u x H12 c2 H9)) t a2 (H3 d1 u0 (S i) (getl_clear_bind 
Abst (CHead c (Bind Abst) u) c u (clear_bind Abst c u) (CHead d1 (Bind Abbr) 
u0) i H4) (CHead c2 (Bind Abst) x) t (fsubst0_fst (S i) u0 (CHead c (Bind 
Abst) u) t (CHead c2 (Bind Abst) x) (csubst0_both_bind Abst i u0 u x H12 c c2 
H9)))) t2 H11)))) H10)) (\lambda (H10: (ex2 T (\lambda (t3: T).(eq T t2 
(THead (Bind Abst) u t3))) (\lambda (t3: T).(subst0 (s (Bind Abst) i) u0 t 
t3)))).(ex2_ind T (\lambda (t3: T).(eq T t2 (THead (Bind Abst) u t3))) 
(\lambda (t3: T).(subst0 (s (Bind Abst) i) u0 t t3)) (arity g c2 t2 (AHead a1 
a2)) (\lambda (x: T).(\lambda (H11: (eq T t2 (THead (Bind Abst) u 
x))).(\lambda (H12: (subst0 (s (Bind Abst) i) u0 t x)).(eq_ind_r T (THead 
(Bind Abst) u x) (\lambda (t0: T).(arity g c2 t0 (AHead a1 a2))) (arity_head 
g c2 u a1 (H1 d1 u0 i H4 c2 u (fsubst0_fst i u0 c u c2 H9)) x a2 (H3 d1 u0 (S 
i) (getl_clear_bind Abst (CHead c (Bind Abst) u) c u (clear_bind Abst c u) 
(CHead d1 (Bind Abbr) u0) i H4) (CHead c2 (Bind Abst) u) x (fsubst0_both (S 
i) u0 (CHead c (Bind Abst) u) t x H12 (CHead c2 (Bind Abst) u) 
(csubst0_fst_bind Abst i c c2 u0 H9 u)))) t2 H11)))) H10)) (\lambda (H10: 
(ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind Abst) u2 
t3)))) (\lambda (u2: T).(\lambda (_: T).(subst0 i u0 u u2))) (\lambda (_: 
T).(\lambda (t3: T).(subst0 (s (Bind Abst) i) u0 t t3))))).(ex3_2_ind T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind Abst) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(subst0 i u0 u u2))) (\lambda (_: 
T).(\lambda (t3: T).(subst0 (s (Bind Abst) i) u0 t t3))) (arity g c2 t2 
(AHead a1 a2)) (\lambda (x0: T).(\lambda (x1: T).(\lambda (H11: (eq T t2 
(THead (Bind Abst) x0 x1))).(\lambda (H12: (subst0 i u0 u x0)).(\lambda (H13: 
(subst0 (s (Bind Abst) i) u0 t x1)).(eq_ind_r T (THead (Bind Abst) x0 x1) 
(\lambda (t0: T).(arity g c2 t0 (AHead a1 a2))) (arity_head g c2 x0 a1 (H1 d1 
u0 i H4 c2 x0 (fsubst0_both i u0 c u x0 H12 c2 H9)) x1 a2 (H3 d1 u0 (S i) 
(getl_clear_bind Abst (CHead c (Bind Abst) u) c u (clear_bind Abst c u) 
(CHead d1 (Bind Abbr) u0) i H4) (CHead c2 (Bind Abst) x0) x1 (fsubst0_both (S 
i) u0 (CHead c (Bind Abst) u) t x1 H13 (CHead c2 (Bind Abst) x0) 
(csubst0_both_bind Abst i u0 u x0 H12 c c2 H9)))) t2 H11)))))) H10)) 
(subst0_gen_head (Bind Abst) u0 u t t2 i H8)))) H7)) H6))))))))))))))))))) 
(\lambda (c: C).(\lambda (u: T).(\lambda (a1: A).(\lambda (H0: (arity g c u 
a1)).(\lambda (H1: ((\forall (d1: C).(\forall (u0: T).(\forall (i: 
nat).((getl i c (CHead d1 (Bind Abbr) u0)) \to (\forall (c2: C).(\forall (t2: 
T).((fsubst0 i u0 c u c2 t2) \to (arity g c2 t2 a1)))))))))).(\lambda (t: 
T).(\lambda (a2: A).(\lambda (H2: (arity g c t (AHead a1 a2))).(\lambda (H3: 
((\forall (d1: C).(\forall (u0: T).(\forall (i: nat).((getl i c (CHead d1 
(Bind Abbr) u0)) \to (\forall (c2: C).(\forall (t2: T).((fsubst0 i u0 c t c2 
t2) \to (arity g c2 t2 (AHead a1 a2))))))))))).(\lambda (d1: C).(\lambda (u0: 
T).(\lambda (i: nat).(\lambda (H4: (getl i c (CHead d1 (Bind Abbr) 
u0))).(\lambda (c2: C).(\lambda (t2: T).(\lambda (H5: (fsubst0 i u0 c (THead 
(Flat Appl) u t) c2 t2)).(let H_x \def (fsubst0_gen_base c c2 (THead (Flat 
Appl) u t) t2 u0 i H5) in (let H6 \def H_x in (or3_ind (land (eq C c c2) 
(subst0 i u0 (THead (Flat Appl) u t) t2)) (land (eq T (THead (Flat Appl) u t) 
t2) (csubst0 i u0 c c2)) (land (subst0 i u0 (THead (Flat Appl) u t) t2) 
(csubst0 i u0 c c2)) (arity g c2 t2 a2) (\lambda (H7: (land (eq C c c2) 
(subst0 i u0 (THead (Flat Appl) u t) t2))).(land_ind (eq C c c2) (subst0 i u0 
(THead (Flat Appl) u t) t2) (arity g c2 t2 a2) (\lambda (H8: (eq C c 
c2)).(\lambda (H9: (subst0 i u0 (THead (Flat Appl) u t) t2)).(eq_ind C c 
(\lambda (c0: C).(arity g c0 t2 a2)) (or3_ind (ex2 T (\lambda (u2: T).(eq T 
t2 (THead (Flat Appl) u2 t))) (\lambda (u2: T).(subst0 i u0 u u2))) (ex2 T 
(\lambda (t3: T).(eq T t2 (THead (Flat Appl) u t3))) (\lambda (t3: T).(subst0 
(s (Flat Appl) i) u0 t t3))) (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq 
T t2 (THead (Flat Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(subst0 i 
u0 u u2))) (\lambda (_: T).(\lambda (t3: T).(subst0 (s (Flat Appl) i) u0 t 
t3)))) (arity g c t2 a2) (\lambda (H10: (ex2 T (\lambda (u2: T).(eq T t2 
(THead (Flat Appl) u2 t))) (\lambda (u2: T).(subst0 i u0 u u2)))).(ex2_ind T 
(\lambda (u2: T).(eq T t2 (THead (Flat Appl) u2 t))) (\lambda (u2: T).(subst0 
i u0 u u2)) (arity g c t2 a2) (\lambda (x: T).(\lambda (H11: (eq T t2 (THead 
(Flat Appl) x t))).(\lambda (H12: (subst0 i u0 u x)).(eq_ind_r T (THead (Flat 
Appl) x t) (\lambda (t0: T).(arity g c t0 a2)) (arity_appl g c x a1 (H1 d1 u0 
i H4 c x (fsubst0_snd i u0 c u x H12)) t a2 H2) t2 H11)))) H10)) (\lambda 
(H10: (ex2 T (\lambda (t3: T).(eq T t2 (THead (Flat Appl) u t3))) (\lambda 
(t3: T).(subst0 (s (Flat Appl) i) u0 t t3)))).(ex2_ind T (\lambda (t3: T).(eq 
T t2 (THead (Flat Appl) u t3))) (\lambda (t3: T).(subst0 (s (Flat Appl) i) u0 
t t3)) (arity g c t2 a2) (\lambda (x: T).(\lambda (H11: (eq T t2 (THead (Flat 
Appl) u x))).(\lambda (H12: (subst0 (s (Flat Appl) i) u0 t x)).(eq_ind_r T 
(THead (Flat Appl) u x) (\lambda (t0: T).(arity g c t0 a2)) (arity_appl g c u 
a1 H0 x a2 (H3 d1 u0 i H4 c x (fsubst0_snd i u0 c t x H12))) t2 H11)))) H10)) 
(\lambda (H10: (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead 
(Flat Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(subst0 i u0 u u2))) 
(\lambda (_: T).(\lambda (t3: T).(subst0 (s (Flat Appl) i) u0 t 
t3))))).(ex3_2_ind T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead 
(Flat Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(subst0 i u0 u u2))) 
(\lambda (_: T).(\lambda (t3: T).(subst0 (s (Flat Appl) i) u0 t t3))) (arity 
g c t2 a2) (\lambda (x0: T).(\lambda (x1: T).(\lambda (H11: (eq T t2 (THead 
(Flat Appl) x0 x1))).(\lambda (H12: (subst0 i u0 u x0)).(\lambda (H13: 
(subst0 (s (Flat Appl) i) u0 t x1)).(eq_ind_r T (THead (Flat Appl) x0 x1) 
(\lambda (t0: T).(arity g c t0 a2)) (arity_appl g c x0 a1 (H1 d1 u0 i H4 c x0 
(fsubst0_snd i u0 c u x0 H12)) x1 a2 (H3 d1 u0 i H4 c x1 (fsubst0_snd i u0 c 
t x1 H13))) t2 H11)))))) H10)) (subst0_gen_head (Flat Appl) u0 u t t2 i H9)) 
c2 H8))) H7)) (\lambda (H7: (land (eq T (THead (Flat Appl) u t) t2) (csubst0 
i u0 c c2))).(land_ind (eq T (THead (Flat Appl) u t) t2) (csubst0 i u0 c c2) 
(arity g c2 t2 a2) (\lambda (H8: (eq T (THead (Flat Appl) u t) t2)).(\lambda 
(H9: (csubst0 i u0 c c2)).(eq_ind T (THead (Flat Appl) u t) (\lambda (t0: 
T).(arity g c2 t0 a2)) (arity_appl g c2 u a1 (H1 d1 u0 i H4 c2 u (fsubst0_fst 
i u0 c u c2 H9)) t a2 (H3 d1 u0 i H4 c2 t (fsubst0_fst i u0 c t c2 H9))) t2 
H8))) H7)) (\lambda (H7: (land (subst0 i u0 (THead (Flat Appl) u t) t2) 
(csubst0 i u0 c c2))).(land_ind (subst0 i u0 (THead (Flat Appl) u t) t2) 
(csubst0 i u0 c c2) (arity g c2 t2 a2) (\lambda (H8: (subst0 i u0 (THead 
(Flat Appl) u t) t2)).(\lambda (H9: (csubst0 i u0 c c2)).(or3_ind (ex2 T 
(\lambda (u2: T).(eq T t2 (THead (Flat Appl) u2 t))) (\lambda (u2: T).(subst0 
i u0 u u2))) (ex2 T (\lambda (t3: T).(eq T t2 (THead (Flat Appl) u t3))) 
(\lambda (t3: T).(subst0 (s (Flat Appl) i) u0 t t3))) (ex3_2 T T (\lambda 
(u2: T).(\lambda (t3: T).(eq T t2 (THead (Flat Appl) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(subst0 i u0 u u2))) (\lambda (_: T).(\lambda (t3: 
T).(subst0 (s (Flat Appl) i) u0 t t3)))) (arity g c2 t2 a2) (\lambda (H10: 
(ex2 T (\lambda (u2: T).(eq T t2 (THead (Flat Appl) u2 t))) (\lambda (u2: 
T).(subst0 i u0 u u2)))).(ex2_ind T (\lambda (u2: T).(eq T t2 (THead (Flat 
Appl) u2 t))) (\lambda (u2: T).(subst0 i u0 u u2)) (arity g c2 t2 a2) 
(\lambda (x: T).(\lambda (H11: (eq T t2 (THead (Flat Appl) x t))).(\lambda 
(H12: (subst0 i u0 u x)).(eq_ind_r T (THead (Flat Appl) x t) (\lambda (t0: 
T).(arity g c2 t0 a2)) (arity_appl g c2 x a1 (H1 d1 u0 i H4 c2 x 
(fsubst0_both i u0 c u x H12 c2 H9)) t a2 (H3 d1 u0 i H4 c2 t (fsubst0_fst i 
u0 c t c2 H9))) t2 H11)))) H10)) (\lambda (H10: (ex2 T (\lambda (t3: T).(eq T 
t2 (THead (Flat Appl) u t3))) (\lambda (t3: T).(subst0 (s (Flat Appl) i) u0 t 
t3)))).(ex2_ind T (\lambda (t3: T).(eq T t2 (THead (Flat Appl) u t3))) 
(\lambda (t3: T).(subst0 (s (Flat Appl) i) u0 t t3)) (arity g c2 t2 a2) 
(\lambda (x: T).(\lambda (H11: (eq T t2 (THead (Flat Appl) u x))).(\lambda 
(H12: (subst0 (s (Flat Appl) i) u0 t x)).(eq_ind_r T (THead (Flat Appl) u x) 
(\lambda (t0: T).(arity g c2 t0 a2)) (arity_appl g c2 u a1 (H1 d1 u0 i H4 c2 
u (fsubst0_fst i u0 c u c2 H9)) x a2 (H3 d1 u0 i H4 c2 x (fsubst0_both i u0 c 
t x H12 c2 H9))) t2 H11)))) H10)) (\lambda (H10: (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T t2 (THead (Flat Appl) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(subst0 i u0 u u2))) (\lambda (_: T).(\lambda (t3: 
T).(subst0 (s (Flat Appl) i) u0 t t3))))).(ex3_2_ind T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T t2 (THead (Flat Appl) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(subst0 i u0 u u2))) (\lambda (_: T).(\lambda (t3: 
T).(subst0 (s (Flat Appl) i) u0 t t3))) (arity g c2 t2 a2) (\lambda (x0: 
T).(\lambda (x1: T).(\lambda (H11: (eq T t2 (THead (Flat Appl) x0 
x1))).(\lambda (H12: (subst0 i u0 u x0)).(\lambda (H13: (subst0 (s (Flat 
Appl) i) u0 t x1)).(eq_ind_r T (THead (Flat Appl) x0 x1) (\lambda (t0: 
T).(arity g c2 t0 a2)) (arity_appl g c2 x0 a1 (H1 d1 u0 i H4 c2 x0 
(fsubst0_both i u0 c u x0 H12 c2 H9)) x1 a2 (H3 d1 u0 i H4 c2 x1 
(fsubst0_both i u0 c t x1 H13 c2 H9))) t2 H11)))))) H10)) (subst0_gen_head 
(Flat Appl) u0 u t t2 i H8)))) H7)) H6))))))))))))))))))) (\lambda (c: 
C).(\lambda (u: T).(\lambda (a0: A).(\lambda (H0: (arity g c u (asucc g 
a0))).(\lambda (H1: ((\forall (d1: C).(\forall (u0: T).(\forall (i: 
nat).((getl i c (CHead d1 (Bind Abbr) u0)) \to (\forall (c2: C).(\forall (t2: 
T).((fsubst0 i u0 c u c2 t2) \to (arity g c2 t2 (asucc g 
a0))))))))))).(\lambda (t: T).(\lambda (H2: (arity g c t a0)).(\lambda (H3: 
((\forall (d1: C).(\forall (u0: T).(\forall (i: nat).((getl i c (CHead d1 
(Bind Abbr) u0)) \to (\forall (c2: C).(\forall (t2: T).((fsubst0 i u0 c t c2 
t2) \to (arity g c2 t2 a0)))))))))).(\lambda (d1: C).(\lambda (u0: 
T).(\lambda (i: nat).(\lambda (H4: (getl i c (CHead d1 (Bind Abbr) 
u0))).(\lambda (c2: C).(\lambda (t2: T).(\lambda (H5: (fsubst0 i u0 c (THead 
(Flat Cast) u t) c2 t2)).(let H_x \def (fsubst0_gen_base c c2 (THead (Flat 
Cast) u t) t2 u0 i H5) in (let H6 \def H_x in (or3_ind (land (eq C c c2) 
(subst0 i u0 (THead (Flat Cast) u t) t2)) (land (eq T (THead (Flat Cast) u t) 
t2) (csubst0 i u0 c c2)) (land (subst0 i u0 (THead (Flat Cast) u t) t2) 
(csubst0 i u0 c c2)) (arity g c2 t2 a0) (\lambda (H7: (land (eq C c c2) 
(subst0 i u0 (THead (Flat Cast) u t) t2))).(land_ind (eq C c c2) (subst0 i u0 
(THead (Flat Cast) u t) t2) (arity g c2 t2 a0) (\lambda (H8: (eq C c 
c2)).(\lambda (H9: (subst0 i u0 (THead (Flat Cast) u t) t2)).(eq_ind C c 
(\lambda (c0: C).(arity g c0 t2 a0)) (or3_ind (ex2 T (\lambda (u2: T).(eq T 
t2 (THead (Flat Cast) u2 t))) (\lambda (u2: T).(subst0 i u0 u u2))) (ex2 T 
(\lambda (t3: T).(eq T t2 (THead (Flat Cast) u t3))) (\lambda (t3: T).(subst0 
(s (Flat Cast) i) u0 t t3))) (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq 
T t2 (THead (Flat Cast) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(subst0 i 
u0 u u2))) (\lambda (_: T).(\lambda (t3: T).(subst0 (s (Flat Cast) i) u0 t 
t3)))) (arity g c t2 a0) (\lambda (H10: (ex2 T (\lambda (u2: T).(eq T t2 
(THead (Flat Cast) u2 t))) (\lambda (u2: T).(subst0 i u0 u u2)))).(ex2_ind T 
(\lambda (u2: T).(eq T t2 (THead (Flat Cast) u2 t))) (\lambda (u2: T).(subst0 
i u0 u u2)) (arity g c t2 a0) (\lambda (x: T).(\lambda (H11: (eq T t2 (THead 
(Flat Cast) x t))).(\lambda (H12: (subst0 i u0 u x)).(eq_ind_r T (THead (Flat 
Cast) x t) (\lambda (t0: T).(arity g c t0 a0)) (arity_cast g c x a0 (H1 d1 u0 
i H4 c x (fsubst0_snd i u0 c u x H12)) t H2) t2 H11)))) H10)) (\lambda (H10: 
(ex2 T (\lambda (t3: T).(eq T t2 (THead (Flat Cast) u t3))) (\lambda (t3: 
T).(subst0 (s (Flat Cast) i) u0 t t3)))).(ex2_ind T (\lambda (t3: T).(eq T t2 
(THead (Flat Cast) u t3))) (\lambda (t3: T).(subst0 (s (Flat Cast) i) u0 t 
t3)) (arity g c t2 a0) (\lambda (x: T).(\lambda (H11: (eq T t2 (THead (Flat 
Cast) u x))).(\lambda (H12: (subst0 (s (Flat Cast) i) u0 t x)).(eq_ind_r T 
(THead (Flat Cast) u x) (\lambda (t0: T).(arity g c t0 a0)) (arity_cast g c u 
a0 H0 x (H3 d1 u0 i H4 c x (fsubst0_snd i u0 c t x H12))) t2 H11)))) H10)) 
(\lambda (H10: (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead 
(Flat Cast) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(subst0 i u0 u u2))) 
(\lambda (_: T).(\lambda (t3: T).(subst0 (s (Flat Cast) i) u0 t 
t3))))).(ex3_2_ind T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead 
(Flat Cast) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(subst0 i u0 u u2))) 
(\lambda (_: T).(\lambda (t3: T).(subst0 (s (Flat Cast) i) u0 t t3))) (arity 
g c t2 a0) (\lambda (x0: T).(\lambda (x1: T).(\lambda (H11: (eq T t2 (THead 
(Flat Cast) x0 x1))).(\lambda (H12: (subst0 i u0 u x0)).(\lambda (H13: 
(subst0 (s (Flat Cast) i) u0 t x1)).(eq_ind_r T (THead (Flat Cast) x0 x1) 
(\lambda (t0: T).(arity g c t0 a0)) (arity_cast g c x0 a0 (H1 d1 u0 i H4 c x0 
(fsubst0_snd i u0 c u x0 H12)) x1 (H3 d1 u0 i H4 c x1 (fsubst0_snd i u0 c t 
x1 H13))) t2 H11)))))) H10)) (subst0_gen_head (Flat Cast) u0 u t t2 i H9)) c2 
H8))) H7)) (\lambda (H7: (land (eq T (THead (Flat Cast) u t) t2) (csubst0 i 
u0 c c2))).(land_ind (eq T (THead (Flat Cast) u t) t2) (csubst0 i u0 c c2) 
(arity g c2 t2 a0) (\lambda (H8: (eq T (THead (Flat Cast) u t) t2)).(\lambda 
(H9: (csubst0 i u0 c c2)).(eq_ind T (THead (Flat Cast) u t) (\lambda (t0: 
T).(arity g c2 t0 a0)) (arity_cast g c2 u a0 (H1 d1 u0 i H4 c2 u (fsubst0_fst 
i u0 c u c2 H9)) t (H3 d1 u0 i H4 c2 t (fsubst0_fst i u0 c t c2 H9))) t2 
H8))) H7)) (\lambda (H7: (land (subst0 i u0 (THead (Flat Cast) u t) t2) 
(csubst0 i u0 c c2))).(land_ind (subst0 i u0 (THead (Flat Cast) u t) t2) 
(csubst0 i u0 c c2) (arity g c2 t2 a0) (\lambda (H8: (subst0 i u0 (THead 
(Flat Cast) u t) t2)).(\lambda (H9: (csubst0 i u0 c c2)).(or3_ind (ex2 T 
(\lambda (u2: T).(eq T t2 (THead (Flat Cast) u2 t))) (\lambda (u2: T).(subst0 
i u0 u u2))) (ex2 T (\lambda (t3: T).(eq T t2 (THead (Flat Cast) u t3))) 
(\lambda (t3: T).(subst0 (s (Flat Cast) i) u0 t t3))) (ex3_2 T T (\lambda 
(u2: T).(\lambda (t3: T).(eq T t2 (THead (Flat Cast) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(subst0 i u0 u u2))) (\lambda (_: T).(\lambda (t3: 
T).(subst0 (s (Flat Cast) i) u0 t t3)))) (arity g c2 t2 a0) (\lambda (H10: 
(ex2 T (\lambda (u2: T).(eq T t2 (THead (Flat Cast) u2 t))) (\lambda (u2: 
T).(subst0 i u0 u u2)))).(ex2_ind T (\lambda (u2: T).(eq T t2 (THead (Flat 
Cast) u2 t))) (\lambda (u2: T).(subst0 i u0 u u2)) (arity g c2 t2 a0) 
(\lambda (x: T).(\lambda (H11: (eq T t2 (THead (Flat Cast) x t))).(\lambda 
(H12: (subst0 i u0 u x)).(eq_ind_r T (THead (Flat Cast) x t) (\lambda (t0: 
T).(arity g c2 t0 a0)) (arity_cast g c2 x a0 (H1 d1 u0 i H4 c2 x 
(fsubst0_both i u0 c u x H12 c2 H9)) t (H3 d1 u0 i H4 c2 t (fsubst0_fst i u0 
c t c2 H9))) t2 H11)))) H10)) (\lambda (H10: (ex2 T (\lambda (t3: T).(eq T t2 
(THead (Flat Cast) u t3))) (\lambda (t3: T).(subst0 (s (Flat Cast) i) u0 t 
t3)))).(ex2_ind T (\lambda (t3: T).(eq T t2 (THead (Flat Cast) u t3))) 
(\lambda (t3: T).(subst0 (s (Flat Cast) i) u0 t t3)) (arity g c2 t2 a0) 
(\lambda (x: T).(\lambda (H11: (eq T t2 (THead (Flat Cast) u x))).(\lambda 
(H12: (subst0 (s (Flat Cast) i) u0 t x)).(eq_ind_r T (THead (Flat Cast) u x) 
(\lambda (t0: T).(arity g c2 t0 a0)) (arity_cast g c2 u a0 (H1 d1 u0 i H4 c2 
u (fsubst0_fst i u0 c u c2 H9)) x (H3 d1 u0 i H4 c2 x (fsubst0_both i u0 c t 
x H12 c2 H9))) t2 H11)))) H10)) (\lambda (H10: (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T t2 (THead (Flat Cast) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(subst0 i u0 u u2))) (\lambda (_: T).(\lambda (t3: 
T).(subst0 (s (Flat Cast) i) u0 t t3))))).(ex3_2_ind T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T t2 (THead (Flat Cast) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(subst0 i u0 u u2))) (\lambda (_: T).(\lambda (t3: 
T).(subst0 (s (Flat Cast) i) u0 t t3))) (arity g c2 t2 a0) (\lambda (x0: 
T).(\lambda (x1: T).(\lambda (H11: (eq T t2 (THead (Flat Cast) x0 
x1))).(\lambda (H12: (subst0 i u0 u x0)).(\lambda (H13: (subst0 (s (Flat 
Cast) i) u0 t x1)).(eq_ind_r T (THead (Flat Cast) x0 x1) (\lambda (t0: 
T).(arity g c2 t0 a0)) (arity_cast g c2 x0 a0 (H1 d1 u0 i H4 c2 x0 
(fsubst0_both i u0 c u x0 H12 c2 H9)) x1 (H3 d1 u0 i H4 c2 x1 (fsubst0_both i 
u0 c t x1 H13 c2 H9))) t2 H11)))))) H10)) (subst0_gen_head (Flat Cast) u0 u t 
t2 i H8)))) H7)) H6)))))))))))))))))) (\lambda (c: C).(\lambda (t: 
T).(\lambda (a1: A).(\lambda (_: (arity g c t a1)).(\lambda (H1: ((\forall 
(d1: C).(\forall (u: T).(\forall (i: nat).((getl i c (CHead d1 (Bind Abbr) 
u)) \to (\forall (c2: C).(\forall (t2: T).((fsubst0 i u c t c2 t2) \to (arity 
g c2 t2 a1)))))))))).(\lambda (a2: A).(\lambda (H2: (leq g a1 a2)).(\lambda 
(d1: C).(\lambda (u: T).(\lambda (i: nat).(\lambda (H3: (getl i c (CHead d1 
(Bind Abbr) u))).(\lambda (c2: C).(\lambda (t2: T).(\lambda (H4: (fsubst0 i u 
c t c2 t2)).(let H_x \def (fsubst0_gen_base c c2 t t2 u i H4) in (let H5 \def 
H_x in (or3_ind (land (eq C c c2) (subst0 i u t t2)) (land (eq T t t2) 
(csubst0 i u c c2)) (land (subst0 i u t t2) (csubst0 i u c c2)) (arity g c2 
t2 a2) (\lambda (H6: (land (eq C c c2) (subst0 i u t t2))).(land_ind (eq C c 
c2) (subst0 i u t t2) (arity g c2 t2 a2) (\lambda (H7: (eq C c c2)).(\lambda 
(H8: (subst0 i u t t2)).(eq_ind C c (\lambda (c0: C).(arity g c0 t2 a2)) 
(arity_repl g c t2 a1 (H1 d1 u i H3 c t2 (fsubst0_snd i u c t t2 H8)) a2 H2) 
c2 H7))) H6)) (\lambda (H6: (land (eq T t t2) (csubst0 i u c c2))).(land_ind 
(eq T t t2) (csubst0 i u c c2) (arity g c2 t2 a2) (\lambda (H7: (eq T t 
t2)).(\lambda (H8: (csubst0 i u c c2)).(eq_ind T t (\lambda (t0: T).(arity g 
c2 t0 a2)) (arity_repl g c2 t a1 (H1 d1 u i H3 c2 t (fsubst0_fst i u c t c2 
H8)) a2 H2) t2 H7))) H6)) (\lambda (H6: (land (subst0 i u t t2) (csubst0 i u 
c c2))).(land_ind (subst0 i u t t2) (csubst0 i u c c2) (arity g c2 t2 a2) 
(\lambda (H7: (subst0 i u t t2)).(\lambda (H8: (csubst0 i u c 
c2)).(arity_repl g c2 t2 a1 (H1 d1 u i H3 c2 t2 (fsubst0_both i u c t t2 H7 
c2 H8)) a2 H2))) H6)) H5))))))))))))))))) c1 t1 a H))))).
(* COMMENTS
Initial nodes: 20387
END *)

theorem arity_subst0:
 \forall (g: G).(\forall (c: C).(\forall (t1: T).(\forall (a: A).((arity g c 
t1 a) \to (\forall (d: C).(\forall (u: T).(\forall (i: nat).((getl i c (CHead 
d (Bind Abbr) u)) \to (\forall (t2: T).((subst0 i u t1 t2) \to (arity g c t2 
a)))))))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (t1: T).(\lambda (a: A).(\lambda (H: 
(arity g c t1 a)).(\lambda (d: C).(\lambda (u: T).(\lambda (i: nat).(\lambda 
(H0: (getl i c (CHead d (Bind Abbr) u))).(\lambda (t2: T).(\lambda (H1: 
(subst0 i u t1 t2)).(arity_fsubst0 g c t1 a H d u i H0 c t2 (fsubst0_snd i u 
c t1 t2 H1)))))))))))).
(* COMMENTS
Initial nodes: 89
END *)

