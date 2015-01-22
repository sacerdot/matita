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

include "Basic-1/cimp/defs.ma".

include "Basic-1/getl/getl.ma".

theorem cimp_flat_sx:
 \forall (f: F).(\forall (c: C).(\forall (v: T).(cimp (CHead c (Flat f) v) 
c)))
\def
 \lambda (f: F).(\lambda (c: C).(\lambda (v: T).(\lambda (b: B).(\lambda (d1: 
C).(\lambda (w: T).(\lambda (h: nat).(\lambda (H: (getl h (CHead c (Flat f) 
v) (CHead d1 (Bind b) w))).(nat_ind (\lambda (n: nat).((getl n (CHead c (Flat 
f) v) (CHead d1 (Bind b) w)) \to (ex C (\lambda (d2: C).(getl n c (CHead d2 
(Bind b) w)))))) (\lambda (H0: (getl O (CHead c (Flat f) v) (CHead d1 (Bind 
b) w))).(ex_intro C (\lambda (d2: C).(getl O c (CHead d2 (Bind b) w))) d1 
(getl_intro O c (CHead d1 (Bind b) w) c (drop_refl c) (clear_gen_flat f c 
(CHead d1 (Bind b) w) v (getl_gen_O (CHead c (Flat f) v) (CHead d1 (Bind b) 
w) H0))))) (\lambda (h0: nat).(\lambda (_: (((getl h0 (CHead c (Flat f) v) 
(CHead d1 (Bind b) w)) \to (ex C (\lambda (d2: C).(getl h0 c (CHead d2 (Bind 
b) w))))))).(\lambda (H0: (getl (S h0) (CHead c (Flat f) v) (CHead d1 (Bind 
b) w))).(ex_intro C (\lambda (d2: C).(getl (S h0) c (CHead d2 (Bind b) w))) 
d1 (getl_gen_S (Flat f) c (CHead d1 (Bind b) w) v h0 H0))))) h H)))))))).
(* COMMENTS
Initial nodes: 327
END *)

theorem cimp_flat_dx:
 \forall (f: F).(\forall (c: C).(\forall (v: T).(cimp c (CHead c (Flat f) 
v))))
\def
 \lambda (f: F).(\lambda (c: C).(\lambda (v: T).(\lambda (b: B).(\lambda (d1: 
C).(\lambda (w: T).(\lambda (h: nat).(\lambda (H: (getl h c (CHead d1 (Bind 
b) w))).(ex_intro C (\lambda (d2: C).(getl h (CHead c (Flat f) v) (CHead d2 
(Bind b) w))) d1 (getl_flat c (CHead d1 (Bind b) w) h H f v))))))))).
(* COMMENTS
Initial nodes: 83
END *)

theorem cimp_bind:
 \forall (c1: C).(\forall (c2: C).((cimp c1 c2) \to (\forall (b: B).(\forall 
(v: T).(cimp (CHead c1 (Bind b) v) (CHead c2 (Bind b) v))))))
\def
 \lambda (c1: C).(\lambda (c2: C).(\lambda (H: ((\forall (b: B).(\forall (d1: 
C).(\forall (w: T).(\forall (h: nat).((getl h c1 (CHead d1 (Bind b) w)) \to 
(ex C (\lambda (d2: C).(getl h c2 (CHead d2 (Bind b) w))))))))))).(\lambda 
(b: B).(\lambda (v: T).(\lambda (b0: B).(\lambda (d1: C).(\lambda (w: 
T).(\lambda (h: nat).(\lambda (H0: (getl h (CHead c1 (Bind b) v) (CHead d1 
(Bind b0) w))).(nat_ind (\lambda (n: nat).((getl n (CHead c1 (Bind b) v) 
(CHead d1 (Bind b0) w)) \to (ex C (\lambda (d2: C).(getl n (CHead c2 (Bind b) 
v) (CHead d2 (Bind b0) w)))))) (\lambda (H1: (getl O (CHead c1 (Bind b) v) 
(CHead d1 (Bind b0) w))).(let H2 \def (f_equal C C (\lambda (e: C).(match e 
in C return (\lambda (_: C).C) with [(CSort _) \Rightarrow d1 | (CHead c _ _) 
\Rightarrow c])) (CHead d1 (Bind b0) w) (CHead c1 (Bind b) v) (clear_gen_bind 
b c1 (CHead d1 (Bind b0) w) v (getl_gen_O (CHead c1 (Bind b) v) (CHead d1 
(Bind b0) w) H1))) in ((let H3 \def (f_equal C B (\lambda (e: C).(match e in 
C return (\lambda (_: C).B) with [(CSort _) \Rightarrow b0 | (CHead _ k _) 
\Rightarrow (match k in K return (\lambda (_: K).B) with [(Bind b1) 
\Rightarrow b1 | (Flat _) \Rightarrow b0])])) (CHead d1 (Bind b0) w) (CHead 
c1 (Bind b) v) (clear_gen_bind b c1 (CHead d1 (Bind b0) w) v (getl_gen_O 
(CHead c1 (Bind b) v) (CHead d1 (Bind b0) w) H1))) in ((let H4 \def (f_equal 
C T (\lambda (e: C).(match e in C return (\lambda (_: C).T) with [(CSort _) 
\Rightarrow w | (CHead _ _ t) \Rightarrow t])) (CHead d1 (Bind b0) w) (CHead 
c1 (Bind b) v) (clear_gen_bind b c1 (CHead d1 (Bind b0) w) v (getl_gen_O 
(CHead c1 (Bind b) v) (CHead d1 (Bind b0) w) H1))) in (\lambda (H5: (eq B b0 
b)).(\lambda (_: (eq C d1 c1)).(eq_ind_r T v (\lambda (t: T).(ex C (\lambda 
(d2: C).(getl O (CHead c2 (Bind b) v) (CHead d2 (Bind b0) t))))) (eq_ind_r B 
b (\lambda (b1: B).(ex C (\lambda (d2: C).(getl O (CHead c2 (Bind b) v) 
(CHead d2 (Bind b1) v))))) (ex_intro C (\lambda (d2: C).(getl O (CHead c2 
(Bind b) v) (CHead d2 (Bind b) v))) c2 (getl_refl b c2 v)) b0 H5) w H4)))) 
H3)) H2))) (\lambda (h0: nat).(\lambda (_: (((getl h0 (CHead c1 (Bind b) v) 
(CHead d1 (Bind b0) w)) \to (ex C (\lambda (d2: C).(getl h0 (CHead c2 (Bind 
b) v) (CHead d2 (Bind b0) w))))))).(\lambda (H1: (getl (S h0) (CHead c1 (Bind 
b) v) (CHead d1 (Bind b0) w))).(let H_x \def (H b0 d1 w (r (Bind b) h0) 
(getl_gen_S (Bind b) c1 (CHead d1 (Bind b0) w) v h0 H1)) in (let H2 \def H_x 
in (ex_ind C (\lambda (d2: C).(getl h0 c2 (CHead d2 (Bind b0) w))) (ex C 
(\lambda (d2: C).(getl (S h0) (CHead c2 (Bind b) v) (CHead d2 (Bind b0) w)))) 
(\lambda (x: C).(\lambda (H3: (getl h0 c2 (CHead x (Bind b0) w))).(ex_intro C 
(\lambda (d2: C).(getl (S h0) (CHead c2 (Bind b) v) (CHead d2 (Bind b0) w))) 
x (getl_head (Bind b) h0 c2 (CHead x (Bind b0) w) H3 v)))) H2)))))) h 
H0)))))))))).
(* COMMENTS
Initial nodes: 817
END *)

theorem cimp_getl_conf:
 \forall (c1: C).(\forall (c2: C).((cimp c1 c2) \to (\forall (b: B).(\forall 
(d1: C).(\forall (w: T).(\forall (i: nat).((getl i c1 (CHead d1 (Bind b) w)) 
\to (ex2 C (\lambda (d2: C).(cimp d1 d2)) (\lambda (d2: C).(getl i c2 (CHead 
d2 (Bind b) w)))))))))))
\def
 \lambda (c1: C).(\lambda (c2: C).(\lambda (H: ((\forall (b: B).(\forall (d1: 
C).(\forall (w: T).(\forall (h: nat).((getl h c1 (CHead d1 (Bind b) w)) \to 
(ex C (\lambda (d2: C).(getl h c2 (CHead d2 (Bind b) w))))))))))).(\lambda 
(b: B).(\lambda (d1: C).(\lambda (w: T).(\lambda (i: nat).(\lambda (H0: (getl 
i c1 (CHead d1 (Bind b) w))).(let H_x \def (H b d1 w i H0) in (let H1 \def 
H_x in (ex_ind C (\lambda (d2: C).(getl i c2 (CHead d2 (Bind b) w))) (ex2 C 
(\lambda (d2: C).(\forall (b0: B).(\forall (d3: C).(\forall (w0: T).(\forall 
(h: nat).((getl h d1 (CHead d3 (Bind b0) w0)) \to (ex C (\lambda (d4: 
C).(getl h d2 (CHead d4 (Bind b0) w0)))))))))) (\lambda (d2: C).(getl i c2 
(CHead d2 (Bind b) w)))) (\lambda (x: C).(\lambda (H2: (getl i c2 (CHead x 
(Bind b) w))).(ex_intro2 C (\lambda (d2: C).(\forall (b0: B).(\forall (d3: 
C).(\forall (w0: T).(\forall (h: nat).((getl h d1 (CHead d3 (Bind b0) w0)) 
\to (ex C (\lambda (d4: C).(getl h d2 (CHead d4 (Bind b0) w0)))))))))) 
(\lambda (d2: C).(getl i c2 (CHead d2 (Bind b) w))) x (\lambda (b0: 
B).(\lambda (d0: C).(\lambda (w0: T).(\lambda (h: nat).(\lambda (H3: (getl h 
d1 (CHead d0 (Bind b0) w0))).(let H_y \def (getl_trans (S h) c1 (CHead d1 
(Bind b) w) i H0) in (let H_x0 \def (H b0 d0 w0 (plus (S h) i) (H_y (CHead d0 
(Bind b0) w0) (getl_head (Bind b) h d1 (CHead d0 (Bind b0) w0) H3 w))) in 
(let H4 \def H_x0 in (ex_ind C (\lambda (d2: C).(getl (S (plus h i)) c2 
(CHead d2 (Bind b0) w0))) (ex C (\lambda (d2: C).(getl h x (CHead d2 (Bind 
b0) w0)))) (\lambda (x0: C).(\lambda (H5: (getl (S (plus h i)) c2 (CHead x0 
(Bind b0) w0))).(let H_y0 \def (getl_conf_le (S (plus h i)) (CHead x0 (Bind 
b0) w0) c2 H5 (CHead x (Bind b) w) i H2) in (let H6 \def (refl_equal nat 
(plus (S h) i)) in (let H7 \def (eq_ind nat (S (plus h i)) (\lambda (n: 
nat).(getl (minus n i) (CHead x (Bind b) w) (CHead x0 (Bind b0) w0))) (H_y0 
(le_S i (plus h i) (le_plus_r h i))) (plus (S h) i) H6) in (let H8 \def 
(eq_ind nat (minus (plus (S h) i) i) (\lambda (n: nat).(getl n (CHead x (Bind 
b) w) (CHead x0 (Bind b0) w0))) H7 (S h) (minus_plus_r (S h) i)) in (ex_intro 
C (\lambda (d2: C).(getl h x (CHead d2 (Bind b0) w0))) x0 (getl_gen_S (Bind 
b) x (CHead x0 (Bind b0) w0) w h H8)))))))) H4))))))))) H2))) H1)))))))))).
(* COMMENTS
Initial nodes: 673
END *)

