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

include "basic_1A/wf3/ty3.ma".

include "basic_1A/app/defs.ma".

lemma wf3_total:
 \forall (g: G).(\forall (c1: C).(ex C (\lambda (c2: C).(wf3 g c1 c2))))
\def
 \lambda (g: G).(\lambda (c1: C).(C_ind (\lambda (c: C).(ex C (\lambda (c2: 
C).(wf3 g c c2)))) (\lambda (n: nat).(ex_intro C (\lambda (c2: C).(wf3 g 
(CSort n) c2)) (CSort n) (wf3_sort g n))) (\lambda (c: C).(\lambda (H: (ex C 
(\lambda (c2: C).(wf3 g c c2)))).(\lambda (k: K).(\lambda (t: T).(let H0 \def 
H in (ex_ind C (\lambda (c2: C).(wf3 g c c2)) (ex C (\lambda (c2: C).(wf3 g 
(CHead c k t) c2))) (\lambda (x: C).(\lambda (H1: (wf3 g c x)).(K_ind 
(\lambda (k0: K).(ex C (\lambda (c2: C).(wf3 g (CHead c k0 t) c2)))) (\lambda 
(b: B).(let H_x \def (ty3_inference g c t) in (let H2 \def H_x in (or_ind (ex 
T (\lambda (t2: T).(ty3 g c t t2))) (\forall (t2: T).((ty3 g c t t2) \to 
False)) (ex C (\lambda (c2: C).(wf3 g (CHead c (Bind b) t) c2))) (\lambda 
(H3: (ex T (\lambda (t2: T).(ty3 g c t t2)))).(ex_ind T (\lambda (t2: T).(ty3 
g c t t2)) (ex C (\lambda (c2: C).(wf3 g (CHead c (Bind b) t) c2))) (\lambda 
(x0: T).(\lambda (H4: (ty3 g c t x0)).(ex_intro C (\lambda (c2: C).(wf3 g 
(CHead c (Bind b) t) c2)) (CHead x (Bind b) t) (wf3_bind g c x H1 t x0 H4 
b)))) H3)) (\lambda (H3: ((\forall (t2: T).((ty3 g c t t2) \to 
False)))).(ex_intro C (\lambda (c2: C).(wf3 g (CHead c (Bind b) t) c2)) 
(CHead x (Bind Void) (TSort O)) (wf3_void g c x H1 t H3 b))) H2)))) (\lambda 
(f: F).(ex_intro C (\lambda (c2: C).(wf3 g (CHead c (Flat f) t) c2)) x 
(wf3_flat g c x H1 t f))) k))) H0)))))) c1)).

lemma ty3_shift1:
 \forall (g: G).(\forall (c: C).((wf3 g c c) \to (\forall (t1: T).(\forall 
(t2: T).((ty3 g c t1 t2) \to (ty3 g (CSort (cbk c)) (app1 c t1) (app1 c 
t2)))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (H: (wf3 g c c)).(insert_eq C c 
(\lambda (c0: C).(wf3 g c0 c)) (\lambda (c0: C).(\forall (t1: T).(\forall 
(t2: T).((ty3 g c0 t1 t2) \to (ty3 g (CSort (cbk c0)) (app1 c0 t1) (app1 c0 
t2)))))) (\lambda (y: C).(\lambda (H0: (wf3 g y c)).(wf3_ind g (\lambda (c0: 
C).(\lambda (c1: C).((eq C c0 c1) \to (\forall (t1: T).(\forall (t2: T).((ty3 
g c0 t1 t2) \to (ty3 g (CSort (cbk c0)) (app1 c0 t1) (app1 c0 t2)))))))) 
(\lambda (m: nat).(\lambda (_: (eq C (CSort m) (CSort m))).(\lambda (t1: 
T).(\lambda (t2: T).(\lambda (H2: (ty3 g (CSort m) t1 t2)).H2))))) (\lambda 
(c1: C).(\lambda (c2: C).(\lambda (H1: (wf3 g c1 c2)).(\lambda (H2: (((eq C 
c1 c2) \to (\forall (t1: T).(\forall (t2: T).((ty3 g c1 t1 t2) \to (ty3 g 
(CSort (cbk c1)) (app1 c1 t1) (app1 c1 t2)))))))).(\lambda (u: T).(\lambda 
(t: T).(\lambda (H3: (ty3 g c1 u t)).(\lambda (b: B).(\lambda (H4: (eq C 
(CHead c1 (Bind b) u) (CHead c2 (Bind b) u))).(\lambda (t1: T).(\lambda (t2: 
T).(\lambda (H5: (ty3 g (CHead c1 (Bind b) u) t1 t2)).(let H6 \def (f_equal C 
C (\lambda (e: C).(match e with [(CSort _) \Rightarrow c1 | (CHead c0 _ _) 
\Rightarrow c0])) (CHead c1 (Bind b) u) (CHead c2 (Bind b) u) H4) in (let H7 
\def (eq_ind_r C c2 (\lambda (c0: C).((eq C c1 c0) \to (\forall (t3: 
T).(\forall (t4: T).((ty3 g c1 t3 t4) \to (ty3 g (CSort (cbk c1)) (app1 c1 
t3) (app1 c1 t4))))))) H2 c1 H6) in (let H8 \def (eq_ind_r C c2 (\lambda (c0: 
C).(wf3 g c1 c0)) H1 c1 H6) in (ex_ind T (\lambda (t0: T).(ty3 g (CHead c1 
(Bind b) u) t2 t0)) (ty3 g (CSort (cbk c1)) (app1 c1 (THead (Bind b) u t1)) 
(app1 c1 (THead (Bind b) u t2))) (\lambda (x: T).(\lambda (_: (ty3 g (CHead 
c1 (Bind b) u) t2 x)).(H7 (refl_equal C c1) (THead (Bind b) u t1) (THead 
(Bind b) u t2) (ty3_bind g c1 u t H3 b t1 t2 H5)))) (ty3_correct g (CHead c1 
(Bind b) u) t1 t2 H5))))))))))))))))) (\lambda (c1: C).(\lambda (c2: 
C).(\lambda (H1: (wf3 g c1 c2)).(\lambda (H2: (((eq C c1 c2) \to (\forall 
(t1: T).(\forall (t2: T).((ty3 g c1 t1 t2) \to (ty3 g (CSort (cbk c1)) (app1 
c1 t1) (app1 c1 t2)))))))).(\lambda (u: T).(\lambda (H3: ((\forall (t: 
T).((ty3 g c1 u t) \to False)))).(\lambda (b: B).(\lambda (H4: (eq C (CHead 
c1 (Bind b) u) (CHead c2 (Bind Void) (TSort O)))).(\lambda (t1: T).(\lambda 
(t2: T).(\lambda (H5: (ty3 g (CHead c1 (Bind b) u) t1 t2)).(let H6 \def 
(f_equal C C (\lambda (e: C).(match e with [(CSort _) \Rightarrow c1 | (CHead 
c0 _ _) \Rightarrow c0])) (CHead c1 (Bind b) u) (CHead c2 (Bind Void) (TSort 
O)) H4) in ((let H7 \def (f_equal C B (\lambda (e: C).(match e with [(CSort 
_) \Rightarrow b | (CHead _ k _) \Rightarrow (match k with [(Bind b0) 
\Rightarrow b0 | (Flat _) \Rightarrow b])])) (CHead c1 (Bind b) u) (CHead c2 
(Bind Void) (TSort O)) H4) in ((let H8 \def (f_equal C T (\lambda (e: 
C).(match e with [(CSort _) \Rightarrow u | (CHead _ _ t) \Rightarrow t])) 
(CHead c1 (Bind b) u) (CHead c2 (Bind Void) (TSort O)) H4) in (\lambda (H9: 
(eq B b Void)).(\lambda (H10: (eq C c1 c2)).(let H11 \def (eq_ind B b 
(\lambda (b0: B).(ty3 g (CHead c1 (Bind b0) u) t1 t2)) H5 Void H9) in 
(eq_ind_r B Void (\lambda (b0: B).(ty3 g (CSort (cbk (CHead c1 (Bind b0) u))) 
(app1 (CHead c1 (Bind b0) u) t1) (app1 (CHead c1 (Bind b0) u) t2))) (let H12 
\def (eq_ind T u (\lambda (t: T).(ty3 g (CHead c1 (Bind Void) t) t1 t2)) H11 
(TSort O) H8) in (let H13 \def (eq_ind T u (\lambda (t: T).(\forall (t0: 
T).((ty3 g c1 t t0) \to False))) H3 (TSort O) H8) in (eq_ind_r T (TSort O) 
(\lambda (t: T).(ty3 g (CSort (cbk (CHead c1 (Bind Void) t))) (app1 (CHead c1 
(Bind Void) t) t1) (app1 (CHead c1 (Bind Void) t) t2))) (let H14 \def 
(eq_ind_r C c2 (\lambda (c0: C).((eq C c1 c0) \to (\forall (t3: T).(\forall 
(t4: T).((ty3 g c1 t3 t4) \to (ty3 g (CSort (cbk c1)) (app1 c1 t3) (app1 c1 
t4))))))) H2 c1 H10) in (let H15 \def (eq_ind_r C c2 (\lambda (c0: C).(wf3 g 
c1 c0)) H1 c1 H10) in (ex_ind T (\lambda (t: T).(ty3 g (CHead c1 (Bind Void) 
(TSort O)) t2 t)) (ty3 g (CSort (cbk c1)) (app1 c1 (THead (Bind Void) (TSort 
O) t1)) (app1 c1 (THead (Bind Void) (TSort O) t2))) (\lambda (x: T).(\lambda 
(_: (ty3 g (CHead c1 (Bind Void) (TSort O)) t2 x)).(H14 (refl_equal C c1) 
(THead (Bind Void) (TSort O) t1) (THead (Bind Void) (TSort O) t2) (ty3_bind g 
c1 (TSort O) (TSort (next g O)) (ty3_sort g c1 O) Void t1 t2 H12)))) 
(ty3_correct g (CHead c1 (Bind Void) (TSort O)) t1 t2 H12)))) u H8))) b 
H9))))) H7)) H6))))))))))))) (\lambda (c1: C).(\lambda (c2: C).(\lambda (H1: 
(wf3 g c1 c2)).(\lambda (H2: (((eq C c1 c2) \to (\forall (t1: T).(\forall 
(t2: T).((ty3 g c1 t1 t2) \to (ty3 g (CSort (cbk c1)) (app1 c1 t1) (app1 c1 
t2)))))))).(\lambda (u: T).(\lambda (f: F).(\lambda (H3: (eq C (CHead c1 
(Flat f) u) c2)).(\lambda (t1: T).(\lambda (t2: T).(\lambda (_: (ty3 g (CHead 
c1 (Flat f) u) t1 t2)).(let H5 \def (f_equal C C (\lambda (e: C).e) (CHead c1 
(Flat f) u) c2 H3) in (let H6 \def (eq_ind_r C c2 (\lambda (c0: C).((eq C c1 
c0) \to (\forall (t3: T).(\forall (t4: T).((ty3 g c1 t3 t4) \to (ty3 g (CSort 
(cbk c1)) (app1 c1 t3) (app1 c1 t4))))))) H2 (CHead c1 (Flat f) u) H5) in 
(let H7 \def (eq_ind_r C c2 (\lambda (c0: C).(wf3 g c1 c0)) H1 (CHead c1 
(Flat f) u) H5) in (let H_x \def (wf3_gen_head2 g c1 c1 u (Flat f) H7) in 
(let H8 \def H_x in (ex_ind B (\lambda (b: B).(eq K (Flat f) (Bind b))) (ty3 
g (CSort (cbk c1)) (app1 c1 (THead (Flat f) u t1)) (app1 c1 (THead (Flat f) u 
t2))) (\lambda (x: B).(\lambda (H9: (eq K (Flat f) (Bind x))).(let H10 \def 
(eq_ind K (Flat f) (\lambda (ee: K).(match ee with [(Bind _) \Rightarrow 
False | (Flat _) \Rightarrow True])) I (Bind x) H9) in (False_ind (ty3 g 
(CSort (cbk c1)) (app1 c1 (THead (Flat f) u t1)) (app1 c1 (THead (Flat f) u 
t2))) H10)))) H8)))))))))))))))) y c H0))) H))).

lemma wf3_idem:
 \forall (g: G).(\forall (c1: C).(\forall (c2: C).((wf3 g c1 c2) \to (wf3 g 
c2 c2))))
\def
 \lambda (g: G).(\lambda (c1: C).(\lambda (c2: C).(\lambda (H: (wf3 g c1 
c2)).(wf3_ind g (\lambda (_: C).(\lambda (c0: C).(wf3 g c0 c0))) (\lambda (m: 
nat).(wf3_sort g m)) (\lambda (c3: C).(\lambda (c4: C).(\lambda (H0: (wf3 g 
c3 c4)).(\lambda (H1: (wf3 g c4 c4)).(\lambda (u: T).(\lambda (t: T).(\lambda 
(H2: (ty3 g c3 u t)).(\lambda (b: B).(wf3_bind g c4 c4 H1 u t (wf3_ty3_conf g 
c3 u t H2 c4 H0) b))))))))) (\lambda (c3: C).(\lambda (c4: C).(\lambda (_: 
(wf3 g c3 c4)).(\lambda (H1: (wf3 g c4 c4)).(\lambda (u: T).(\lambda (_: 
((\forall (t: T).((ty3 g c3 u t) \to False)))).(\lambda (_: B).(wf3_bind g c4 
c4 H1 (TSort O) (TSort (next g O)) (ty3_sort g c4 O) Void)))))))) (\lambda 
(c3: C).(\lambda (c4: C).(\lambda (_: (wf3 g c3 c4)).(\lambda (H1: (wf3 g c4 
c4)).(\lambda (_: T).(\lambda (_: F).H1)))))) c1 c2 H)))).

lemma wf3_ty3:
 \forall (g: G).(\forall (c1: C).(\forall (t: T).(\forall (u: T).((ty3 g c1 t 
u) \to (ex2 C (\lambda (c2: C).(wf3 g c1 c2)) (\lambda (c2: C).(ty3 g c2 t 
u)))))))
\def
 \lambda (g: G).(\lambda (c1: C).(\lambda (t: T).(\lambda (u: T).(\lambda (H: 
(ty3 g c1 t u)).(let H_x \def (wf3_total g c1) in (let H0 \def H_x in (ex_ind 
C (\lambda (c2: C).(wf3 g c1 c2)) (ex2 C (\lambda (c2: C).(wf3 g c1 c2)) 
(\lambda (c2: C).(ty3 g c2 t u))) (\lambda (x: C).(\lambda (H1: (wf3 g c1 
x)).(ex_intro2 C (\lambda (c2: C).(wf3 g c1 c2)) (\lambda (c2: C).(ty3 g c2 t 
u)) x H1 (wf3_ty3_conf g c1 t u H x H1)))) H0))))))).

