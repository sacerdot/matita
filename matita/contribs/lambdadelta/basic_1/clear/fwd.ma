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

include "basic_1/clear/defs.ma".

include "basic_1/C/fwd.ma".

let rec clear_ind (P: (C \to (C \to Prop))) (f: (\forall (b: B).(\forall (e: 
C).(\forall (u: T).(P (CHead e (Bind b) u) (CHead e (Bind b) u)))))) (f0: 
(\forall (e: C).(\forall (c: C).((clear e c) \to ((P e c) \to (\forall (f0: 
F).(\forall (u: T).(P (CHead e (Flat f0) u) c)))))))) (c: C) (c0: C) (c1: 
clear c c0) on c1: P c c0 \def match c1 with [(clear_bind b e u) \Rightarrow 
(f b e u) | (clear_flat e c2 c3 f1 u) \Rightarrow (let TMP_1 \def ((clear_ind 
P f f0) e c2 c3) in (f0 e c2 c3 TMP_1 f1 u))].

theorem clear_gen_sort:
 \forall (x: C).(\forall (n: nat).((clear (CSort n) x) \to (\forall (P: 
Prop).P)))
\def
 \lambda (x: C).(\lambda (n: nat).(\lambda (H: (clear (CSort n) x)).(\lambda 
(P: Prop).(let TMP_1 \def (CSort n) in (let TMP_2 \def (\lambda (c: C).(clear 
c x)) in (let TMP_3 \def (\lambda (_: C).P) in (let TMP_15 \def (\lambda (y: 
C).(\lambda (H0: (clear y x)).(let TMP_4 \def (\lambda (c: C).(\lambda (_: 
C).((eq C c (CSort n)) \to P))) in (let TMP_9 \def (\lambda (b: B).(\lambda 
(e: C).(\lambda (u: T).(\lambda (H1: (eq C (CHead e (Bind b) u) (CSort 
n))).(let TMP_5 \def (Bind b) in (let TMP_6 \def (CHead e TMP_5 u) in (let 
TMP_7 \def (\lambda (ee: C).(match ee with [(CSort _) \Rightarrow False | 
(CHead _ _ _) \Rightarrow True])) in (let TMP_8 \def (CSort n) in (let H2 
\def (eq_ind C TMP_6 TMP_7 I TMP_8 H1) in (False_ind P H2)))))))))) in (let 
TMP_14 \def (\lambda (e: C).(\lambda (c: C).(\lambda (_: (clear e 
c)).(\lambda (_: (((eq C e (CSort n)) \to P))).(\lambda (f: F).(\lambda (u: 
T).(\lambda (H3: (eq C (CHead e (Flat f) u) (CSort n))).(let TMP_10 \def 
(Flat f) in (let TMP_11 \def (CHead e TMP_10 u) in (let TMP_12 \def (\lambda 
(ee: C).(match ee with [(CSort _) \Rightarrow False | (CHead _ _ _) 
\Rightarrow True])) in (let TMP_13 \def (CSort n) in (let H4 \def (eq_ind C 
TMP_11 TMP_12 I TMP_13 H3) in (False_ind P H4))))))))))))) in (clear_ind 
TMP_4 TMP_9 TMP_14 y x H0)))))) in (insert_eq C TMP_1 TMP_2 TMP_3 TMP_15 
H)))))))).

theorem clear_gen_bind:
 \forall (b: B).(\forall (e: C).(\forall (x: C).(\forall (u: T).((clear 
(CHead e (Bind b) u) x) \to (eq C x (CHead e (Bind b) u))))))
\def
 \lambda (b: B).(\lambda (e: C).(\lambda (x: C).(\lambda (u: T).(\lambda (H: 
(clear (CHead e (Bind b) u) x)).(let TMP_1 \def (Bind b) in (let TMP_2 \def 
(CHead e TMP_1 u) in (let TMP_3 \def (\lambda (c: C).(clear c x)) in (let 
TMP_4 \def (\lambda (c: C).(eq C x c)) in (let TMP_53 \def (\lambda (y: 
C).(\lambda (H0: (clear y x)).(let TMP_5 \def (\lambda (c: C).(\lambda (c0: 
C).((eq C c (CHead e (Bind b) u)) \to (eq C c0 c)))) in (let TMP_43 \def 
(\lambda (b0: B).(\lambda (e0: C).(\lambda (u0: T).(\lambda (H1: (eq C (CHead 
e0 (Bind b0) u0) (CHead e (Bind b) u))).(let TMP_6 \def (\lambda (e1: 
C).(match e1 with [(CSort _) \Rightarrow e0 | (CHead c _ _) \Rightarrow c])) 
in (let TMP_7 \def (Bind b0) in (let TMP_8 \def (CHead e0 TMP_7 u0) in (let 
TMP_9 \def (Bind b) in (let TMP_10 \def (CHead e TMP_9 u) in (let H2 \def 
(f_equal C C TMP_6 TMP_8 TMP_10 H1) in (let TMP_11 \def (\lambda (e1: 
C).(match e1 with [(CSort _) \Rightarrow b0 | (CHead _ k _) \Rightarrow 
(match k with [(Bind b1) \Rightarrow b1 | (Flat _) \Rightarrow b0])])) in 
(let TMP_12 \def (Bind b0) in (let TMP_13 \def (CHead e0 TMP_12 u0) in (let 
TMP_14 \def (Bind b) in (let TMP_15 \def (CHead e TMP_14 u) in (let H3 \def 
(f_equal C B TMP_11 TMP_13 TMP_15 H1) in (let TMP_16 \def (\lambda (e1: 
C).(match e1 with [(CSort _) \Rightarrow u0 | (CHead _ _ t) \Rightarrow t])) 
in (let TMP_17 \def (Bind b0) in (let TMP_18 \def (CHead e0 TMP_17 u0) in 
(let TMP_19 \def (Bind b) in (let TMP_20 \def (CHead e TMP_19 u) in (let H4 
\def (f_equal C T TMP_16 TMP_18 TMP_20 H1) in (let TMP_41 \def (\lambda (H5: 
(eq B b0 b)).(\lambda (H6: (eq C e0 e)).(let TMP_25 \def (\lambda (t: T).(let 
TMP_21 \def (Bind b0) in (let TMP_22 \def (CHead e0 TMP_21 t) in (let TMP_23 
\def (Bind b0) in (let TMP_24 \def (CHead e0 TMP_23 t) in (eq C TMP_22 
TMP_24)))))) in (let TMP_30 \def (\lambda (c: C).(let TMP_26 \def (Bind b0) 
in (let TMP_27 \def (CHead c TMP_26 u) in (let TMP_28 \def (Bind b0) in (let 
TMP_29 \def (CHead c TMP_28 u) in (eq C TMP_27 TMP_29)))))) in (let TMP_35 
\def (\lambda (b1: B).(let TMP_31 \def (Bind b1) in (let TMP_32 \def (CHead e 
TMP_31 u) in (let TMP_33 \def (Bind b1) in (let TMP_34 \def (CHead e TMP_33 
u) in (eq C TMP_32 TMP_34)))))) in (let TMP_36 \def (Bind b) in (let TMP_37 
\def (CHead e TMP_36 u) in (let TMP_38 \def (refl_equal C TMP_37) in (let 
TMP_39 \def (eq_ind_r B b TMP_35 TMP_38 b0 H5) in (let TMP_40 \def (eq_ind_r 
C e TMP_30 TMP_39 e0 H6) in (eq_ind_r T u TMP_25 TMP_40 u0 H4))))))))))) in 
(let TMP_42 \def (TMP_41 H3) in (TMP_42 H2))))))))))))))))))))))))) in (let 
TMP_52 \def (\lambda (e0: C).(\lambda (c: C).(\lambda (_: (clear e0 
c)).(\lambda (_: (((eq C e0 (CHead e (Bind b) u)) \to (eq C c e0)))).(\lambda 
(f: F).(\lambda (u0: T).(\lambda (H3: (eq C (CHead e0 (Flat f) u0) (CHead e 
(Bind b) u))).(let TMP_44 \def (Flat f) in (let TMP_45 \def (CHead e0 TMP_44 
u0) in (let TMP_46 \def (\lambda (ee: C).(match ee with [(CSort _) 
\Rightarrow False | (CHead _ k _) \Rightarrow (match k with [(Bind _) 
\Rightarrow False | (Flat _) \Rightarrow True])])) in (let TMP_47 \def (Bind 
b) in (let TMP_48 \def (CHead e TMP_47 u) in (let H4 \def (eq_ind C TMP_45 
TMP_46 I TMP_48 H3) in (let TMP_49 \def (Flat f) in (let TMP_50 \def (CHead 
e0 TMP_49 u0) in (let TMP_51 \def (eq C c TMP_50) in (False_ind TMP_51 
H4))))))))))))))))) in (clear_ind TMP_5 TMP_43 TMP_52 y x H0)))))) in 
(insert_eq C TMP_2 TMP_3 TMP_4 TMP_53 H)))))))))).

theorem clear_gen_flat:
 \forall (f: F).(\forall (e: C).(\forall (x: C).(\forall (u: T).((clear 
(CHead e (Flat f) u) x) \to (clear e x)))))
\def
 \lambda (f: F).(\lambda (e: C).(\lambda (x: C).(\lambda (u: T).(\lambda (H: 
(clear (CHead e (Flat f) u) x)).(let TMP_1 \def (Flat f) in (let TMP_2 \def 
(CHead e TMP_1 u) in (let TMP_3 \def (\lambda (c: C).(clear c x)) in (let 
TMP_4 \def (\lambda (_: C).(clear e x)) in (let TMP_35 \def (\lambda (y: 
C).(\lambda (H0: (clear y x)).(let TMP_5 \def (\lambda (c: C).(\lambda (c0: 
C).((eq C c (CHead e (Flat f) u)) \to (clear e c0)))) in (let TMP_14 \def 
(\lambda (b: B).(\lambda (e0: C).(\lambda (u0: T).(\lambda (H1: (eq C (CHead 
e0 (Bind b) u0) (CHead e (Flat f) u))).(let TMP_6 \def (Bind b) in (let TMP_7 
\def (CHead e0 TMP_6 u0) in (let TMP_8 \def (\lambda (ee: C).(match ee with 
[(CSort _) \Rightarrow False | (CHead _ k _) \Rightarrow (match k with [(Bind 
_) \Rightarrow True | (Flat _) \Rightarrow False])])) in (let TMP_9 \def 
(Flat f) in (let TMP_10 \def (CHead e TMP_9 u) in (let H2 \def (eq_ind C 
TMP_7 TMP_8 I TMP_10 H1) in (let TMP_11 \def (Bind b) in (let TMP_12 \def 
(CHead e0 TMP_11 u0) in (let TMP_13 \def (clear e TMP_12) in (False_ind 
TMP_13 H2)))))))))))))) in (let TMP_34 \def (\lambda (e0: C).(\lambda (c: 
C).(\lambda (H1: (clear e0 c)).(\lambda (H2: (((eq C e0 (CHead e (Flat f) u)) 
\to (clear e c)))).(\lambda (f0: F).(\lambda (u0: T).(\lambda (H3: (eq C 
(CHead e0 (Flat f0) u0) (CHead e (Flat f) u))).(let TMP_15 \def (\lambda (e1: 
C).(match e1 with [(CSort _) \Rightarrow e0 | (CHead c0 _ _) \Rightarrow 
c0])) in (let TMP_16 \def (Flat f0) in (let TMP_17 \def (CHead e0 TMP_16 u0) 
in (let TMP_18 \def (Flat f) in (let TMP_19 \def (CHead e TMP_18 u) in (let 
H4 \def (f_equal C C TMP_15 TMP_17 TMP_19 H3) in (let TMP_20 \def (\lambda 
(e1: C).(match e1 with [(CSort _) \Rightarrow f0 | (CHead _ k _) \Rightarrow 
(match k with [(Bind _) \Rightarrow f0 | (Flat f1) \Rightarrow f1])])) in 
(let TMP_21 \def (Flat f0) in (let TMP_22 \def (CHead e0 TMP_21 u0) in (let 
TMP_23 \def (Flat f) in (let TMP_24 \def (CHead e TMP_23 u) in (let H5 \def 
(f_equal C F TMP_20 TMP_22 TMP_24 H3) in (let TMP_25 \def (\lambda (e1: 
C).(match e1 with [(CSort _) \Rightarrow u0 | (CHead _ _ t) \Rightarrow t])) 
in (let TMP_26 \def (Flat f0) in (let TMP_27 \def (CHead e0 TMP_26 u0) in 
(let TMP_28 \def (Flat f) in (let TMP_29 \def (CHead e TMP_28 u) in (let H6 
\def (f_equal C T TMP_25 TMP_27 TMP_29 H3) in (let TMP_32 \def (\lambda (_: 
(eq F f0 f)).(\lambda (H8: (eq C e0 e)).(let TMP_30 \def (\lambda (c0: 
C).((eq C c0 (CHead e (Flat f) u)) \to (clear e c))) in (let H9 \def (eq_ind 
C e0 TMP_30 H2 e H8) in (let TMP_31 \def (\lambda (c0: C).(clear c0 c)) in 
(let H10 \def (eq_ind C e0 TMP_31 H1 e H8) in H10)))))) in (let TMP_33 \def 
(TMP_32 H5) in (TMP_33 H4)))))))))))))))))))))))))))) in (clear_ind TMP_5 
TMP_14 TMP_34 y x H0)))))) in (insert_eq C TMP_2 TMP_3 TMP_4 TMP_35 
H)))))))))).

theorem clear_gen_flat_r:
 \forall (f: F).(\forall (x: C).(\forall (e: C).(\forall (u: T).((clear x 
(CHead e (Flat f) u)) \to (\forall (P: Prop).P)))))
\def
 \lambda (f: F).(\lambda (x: C).(\lambda (e: C).(\lambda (u: T).(\lambda (H: 
(clear x (CHead e (Flat f) u))).(\lambda (P: Prop).(let TMP_1 \def (Flat f) 
in (let TMP_2 \def (CHead e TMP_1 u) in (let TMP_3 \def (\lambda (c: 
C).(clear x c)) in (let TMP_4 \def (\lambda (_: C).P) in (let TMP_22 \def 
(\lambda (y: C).(\lambda (H0: (clear x y)).(let TMP_5 \def (\lambda (_: 
C).(\lambda (c0: C).((eq C c0 (CHead e (Flat f) u)) \to P))) in (let TMP_11 
\def (\lambda (b: B).(\lambda (e0: C).(\lambda (u0: T).(\lambda (H1: (eq C 
(CHead e0 (Bind b) u0) (CHead e (Flat f) u))).(let TMP_6 \def (Bind b) in 
(let TMP_7 \def (CHead e0 TMP_6 u0) in (let TMP_8 \def (\lambda (ee: 
C).(match ee with [(CSort _) \Rightarrow False | (CHead _ k _) \Rightarrow 
(match k with [(Bind _) \Rightarrow True | (Flat _) \Rightarrow False])])) in 
(let TMP_9 \def (Flat f) in (let TMP_10 \def (CHead e TMP_9 u) in (let H2 
\def (eq_ind C TMP_7 TMP_8 I TMP_10 H1) in (False_ind P H2))))))))))) in (let 
TMP_21 \def (\lambda (e0: C).(\lambda (c: C).(\lambda (H1: (clear e0 
c)).(\lambda (H2: (((eq C c (CHead e (Flat f) u)) \to P))).(\lambda (_: 
F).(\lambda (_: T).(\lambda (H3: (eq C c (CHead e (Flat f) u))).(let TMP_12 
\def (\lambda (c0: C).((eq C c0 (CHead e (Flat f) u)) \to P)) in (let TMP_13 
\def (Flat f) in (let TMP_14 \def (CHead e TMP_13 u) in (let H4 \def (eq_ind 
C c TMP_12 H2 TMP_14 H3) in (let TMP_15 \def (\lambda (c0: C).(clear e0 c0)) 
in (let TMP_16 \def (Flat f) in (let TMP_17 \def (CHead e TMP_16 u) in (let 
H5 \def (eq_ind C c TMP_15 H1 TMP_17 H3) in (let TMP_18 \def (Flat f) in (let 
TMP_19 \def (CHead e TMP_18 u) in (let TMP_20 \def (refl_equal C TMP_19) in 
(H4 TMP_20))))))))))))))))))) in (clear_ind TMP_5 TMP_11 TMP_21 x y H0)))))) 
in (insert_eq C TMP_2 TMP_3 TMP_4 TMP_22 H))))))))))).

theorem clear_gen_all:
 \forall (c1: C).(\forall (c2: C).((clear c1 c2) \to (ex_3 B C T (\lambda (b: 
B).(\lambda (e: C).(\lambda (u: T).(eq C c2 (CHead e (Bind b) u))))))))
\def
 \lambda (c1: C).(\lambda (c2: C).(\lambda (H: (clear c1 c2)).(let TMP_4 \def 
(\lambda (_: C).(\lambda (c0: C).(let TMP_3 \def (\lambda (b: B).(\lambda (e: 
C).(\lambda (u: T).(let TMP_1 \def (Bind b) in (let TMP_2 \def (CHead e TMP_1 
u) in (eq C c0 TMP_2)))))) in (ex_3 B C T TMP_3)))) in (let TMP_13 \def 
(\lambda (b: B).(\lambda (e: C).(\lambda (u: T).(let TMP_9 \def (\lambda (b0: 
B).(\lambda (e0: C).(\lambda (u0: T).(let TMP_5 \def (Bind b) in (let TMP_6 
\def (CHead e TMP_5 u) in (let TMP_7 \def (Bind b0) in (let TMP_8 \def (CHead 
e0 TMP_7 u0) in (eq C TMP_6 TMP_8)))))))) in (let TMP_10 \def (Bind b) in 
(let TMP_11 \def (CHead e TMP_10 u) in (let TMP_12 \def (refl_equal C TMP_11) 
in (ex_3_intro B C T TMP_9 b e u TMP_12)))))))) in (let TMP_40 \def (\lambda 
(e: C).(\lambda (c: C).(\lambda (H0: (clear e c)).(\lambda (H1: (ex_3 B C T 
(\lambda (b: B).(\lambda (e0: C).(\lambda (u: T).(eq C c (CHead e0 (Bind b) 
u))))))).(\lambda (_: F).(\lambda (_: T).(let H2 \def H1 in (let TMP_16 \def 
(\lambda (b: B).(\lambda (e0: C).(\lambda (u0: T).(let TMP_14 \def (Bind b) 
in (let TMP_15 \def (CHead e0 TMP_14 u0) in (eq C c TMP_15)))))) in (let 
TMP_19 \def (\lambda (b: B).(\lambda (e0: C).(\lambda (u0: T).(let TMP_17 
\def (Bind b) in (let TMP_18 \def (CHead e0 TMP_17 u0) in (eq C c 
TMP_18)))))) in (let TMP_20 \def (ex_3 B C T TMP_19) in (let TMP_39 \def 
(\lambda (x0: B).(\lambda (x1: C).(\lambda (x2: T).(\lambda (H3: (eq C c 
(CHead x1 (Bind x0) x2))).(let TMP_21 \def (\lambda (c0: C).(clear e c0)) in 
(let TMP_22 \def (Bind x0) in (let TMP_23 \def (CHead x1 TMP_22 x2) in (let 
H4 \def (eq_ind C c TMP_21 H0 TMP_23 H3) in (let TMP_24 \def (Bind x0) in 
(let TMP_25 \def (CHead x1 TMP_24 x2) in (let TMP_29 \def (\lambda (c0: 
C).(let TMP_28 \def (\lambda (b: B).(\lambda (e0: C).(\lambda (u0: T).(let 
TMP_26 \def (Bind b) in (let TMP_27 \def (CHead e0 TMP_26 u0) in (eq C c0 
TMP_27)))))) in (ex_3 B C T TMP_28))) in (let TMP_34 \def (\lambda (b: 
B).(\lambda (e0: C).(\lambda (u0: T).(let TMP_30 \def (Bind x0) in (let 
TMP_31 \def (CHead x1 TMP_30 x2) in (let TMP_32 \def (Bind b) in (let TMP_33 
\def (CHead e0 TMP_32 u0) in (eq C TMP_31 TMP_33)))))))) in (let TMP_35 \def 
(Bind x0) in (let TMP_36 \def (CHead x1 TMP_35 x2) in (let TMP_37 \def 
(refl_equal C TMP_36) in (let TMP_38 \def (ex_3_intro B C T TMP_34 x0 x1 x2 
TMP_37) in (eq_ind_r C TMP_25 TMP_29 TMP_38 c H3))))))))))))))))) in 
(ex_3_ind B C T TMP_16 TMP_20 TMP_39 H2)))))))))))) in (clear_ind TMP_4 
TMP_13 TMP_40 c1 c2 H)))))).

theorem clear_mono:
 \forall (c: C).(\forall (c1: C).((clear c c1) \to (\forall (c2: C).((clear c 
c2) \to (eq C c1 c2)))))
\def
 \lambda (c: C).(let TMP_1 \def (\lambda (c0: C).(\forall (c1: C).((clear c0 
c1) \to (\forall (c2: C).((clear c0 c2) \to (eq C c1 c2)))))) in (let TMP_3 
\def (\lambda (n: nat).(\lambda (c1: C).(\lambda (_: (clear (CSort n) 
c1)).(\lambda (c2: C).(\lambda (H0: (clear (CSort n) c2)).(let TMP_2 \def (eq 
C c1 c2) in (clear_gen_sort c2 n H0 TMP_2))))))) in (let TMP_23 \def (\lambda 
(c0: C).(\lambda (H: ((\forall (c1: C).((clear c0 c1) \to (\forall (c2: 
C).((clear c0 c2) \to (eq C c1 c2))))))).(\lambda (k: K).(\lambda (t: 
T).(\lambda (c1: C).(\lambda (H0: (clear (CHead c0 k t) c1)).(\lambda (c2: 
C).(\lambda (H1: (clear (CHead c0 k t) c2)).(let TMP_4 \def (\lambda (k0: 
K).((clear (CHead c0 k0 t) c1) \to ((clear (CHead c0 k0 t) c2) \to (eq C c1 
c2)))) in (let TMP_19 \def (\lambda (b: B).(\lambda (H2: (clear (CHead c0 
(Bind b) t) c1)).(\lambda (H3: (clear (CHead c0 (Bind b) t) c2)).(let TMP_5 
\def (Bind b) in (let TMP_6 \def (CHead c0 TMP_5 t) in (let TMP_7 \def 
(\lambda (c3: C).(eq C c1 c3)) in (let TMP_8 \def (Bind b) in (let TMP_9 \def 
(CHead c0 TMP_8 t) in (let TMP_12 \def (\lambda (c3: C).(let TMP_10 \def 
(Bind b) in (let TMP_11 \def (CHead c0 TMP_10 t) in (eq C c3 TMP_11)))) in 
(let TMP_13 \def (Bind b) in (let TMP_14 \def (CHead c0 TMP_13 t) in (let 
TMP_15 \def (refl_equal C TMP_14) in (let TMP_16 \def (clear_gen_bind b c0 c1 
t H2) in (let TMP_17 \def (eq_ind_r C TMP_9 TMP_12 TMP_15 c1 TMP_16) in (let 
TMP_18 \def (clear_gen_bind b c0 c2 t H3) in (eq_ind_r C TMP_6 TMP_7 TMP_17 
c2 TMP_18)))))))))))))))) in (let TMP_22 \def (\lambda (f: F).(\lambda (H2: 
(clear (CHead c0 (Flat f) t) c1)).(\lambda (H3: (clear (CHead c0 (Flat f) t) 
c2)).(let TMP_20 \def (clear_gen_flat f c0 c1 t H2) in (let TMP_21 \def 
(clear_gen_flat f c0 c2 t H3) in (H c1 TMP_20 c2 TMP_21)))))) in (K_ind TMP_4 
TMP_19 TMP_22 k H0 H1)))))))))))) in (C_ind TMP_1 TMP_3 TMP_23 c)))).

theorem clear_cle:
 \forall (c1: C).(\forall (c2: C).((clear c1 c2) \to (cle c2 c1)))
\def
 \lambda (c1: C).(let TMP_3 \def (\lambda (c: C).(\forall (c2: C).((clear c 
c2) \to (let TMP_1 \def (cweight c2) in (let TMP_2 \def (cweight c) in (le 
TMP_1 TMP_2)))))) in (let TMP_6 \def (\lambda (n: nat).(\lambda (c2: 
C).(\lambda (H: (clear (CSort n) c2)).(let TMP_4 \def (cweight c2) in (let 
TMP_5 \def (le TMP_4 O) in (clear_gen_sort c2 n H TMP_5)))))) in (let TMP_31 
\def (\lambda (c: C).(\lambda (H: ((\forall (c2: C).((clear c c2) \to (le 
(cweight c2) (cweight c)))))).(\lambda (k: K).(\lambda (t: T).(\lambda (c2: 
C).(\lambda (H0: (clear (CHead c k t) c2)).(let TMP_11 \def (\lambda (k0: 
K).((clear (CHead c k0 t) c2) \to (let TMP_7 \def (cweight c2) in (let TMP_8 
\def (cweight c) in (let TMP_9 \def (tweight t) in (let TMP_10 \def (plus 
TMP_8 TMP_9) in (le TMP_7 TMP_10))))))) in (let TMP_24 \def (\lambda (b: 
B).(\lambda (H1: (clear (CHead c (Bind b) t) c2)).(let TMP_12 \def (Bind b) 
in (let TMP_13 \def (CHead c TMP_12 t) in (let TMP_18 \def (\lambda (c0: 
C).(let TMP_14 \def (cweight c0) in (let TMP_15 \def (cweight c) in (let 
TMP_16 \def (tweight t) in (let TMP_17 \def (plus TMP_15 TMP_16) in (le 
TMP_14 TMP_17)))))) in (let TMP_19 \def (cweight c) in (let TMP_20 \def 
(tweight t) in (let TMP_21 \def (plus TMP_19 TMP_20) in (let TMP_22 \def 
(le_n TMP_21) in (let TMP_23 \def (clear_gen_bind b c c2 t H1) in (eq_ind_r C 
TMP_13 TMP_18 TMP_22 c2 TMP_23))))))))))) in (let TMP_30 \def (\lambda (f: 
F).(\lambda (H1: (clear (CHead c (Flat f) t) c2)).(let TMP_25 \def (cweight 
c2) in (let TMP_26 \def (cweight c) in (let TMP_27 \def (tweight t) in (let 
TMP_28 \def (clear_gen_flat f c c2 t H1) in (let TMP_29 \def (H c2 TMP_28) in 
(le_plus_trans TMP_25 TMP_26 TMP_27 TMP_29)))))))) in (K_ind TMP_11 TMP_24 
TMP_30 k H0)))))))))) in (C_ind TMP_3 TMP_6 TMP_31 c1)))).

