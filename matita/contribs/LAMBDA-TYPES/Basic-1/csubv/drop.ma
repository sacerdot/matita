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

include "Basic-1/csubv/props.ma".

include "Basic-1/drop/fwd.ma".

theorem csubv_drop_conf:
 \forall (c1: C).(\forall (c2: C).((csubv c1 c2) \to (\forall (e1: 
C).(\forall (h: nat).((drop h O c1 e1) \to (ex2 C (\lambda (e2: C).(csubv e1 
e2)) (\lambda (e2: C).(drop h O c2 e2))))))))
\def
 \lambda (c1: C).(\lambda (c2: C).(\lambda (H: (csubv c1 c2)).(csubv_ind 
(\lambda (c: C).(\lambda (c0: C).(\forall (e1: C).(\forall (h: nat).((drop h 
O c e1) \to (ex2 C (\lambda (e2: C).(csubv e1 e2)) (\lambda (e2: C).(drop h O 
c0 e2)))))))) (\lambda (n: nat).(\lambda (e1: C).(\lambda (h: nat).(\lambda 
(H0: (drop h O (CSort n) e1)).(and3_ind (eq C e1 (CSort n)) (eq nat h O) (eq 
nat O O) (ex2 C (\lambda (e2: C).(csubv e1 e2)) (\lambda (e2: C).(drop h O 
(CSort n) e2))) (\lambda (H1: (eq C e1 (CSort n))).(\lambda (H2: (eq nat h 
O)).(\lambda (_: (eq nat O O)).(eq_ind_r nat O (\lambda (n0: nat).(ex2 C 
(\lambda (e2: C).(csubv e1 e2)) (\lambda (e2: C).(drop n0 O (CSort n) e2)))) 
(eq_ind_r C (CSort n) (\lambda (c: C).(ex2 C (\lambda (e2: C).(csubv c e2)) 
(\lambda (e2: C).(drop O O (CSort n) e2)))) (ex_intro2 C (\lambda (e2: 
C).(csubv (CSort n) e2)) (\lambda (e2: C).(drop O O (CSort n) e2)) (CSort n) 
(csubv_refl (CSort n)) (drop_refl (CSort n))) e1 H1) h H2)))) (drop_gen_sort 
n h O e1 H0)))))) (\lambda (c3: C).(\lambda (c4: C).(\lambda (H0: (csubv c3 
c4)).(\lambda (H1: ((\forall (e1: C).(\forall (h: nat).((drop h O c3 e1) \to 
(ex2 C (\lambda (e2: C).(csubv e1 e2)) (\lambda (e2: C).(drop h O c4 
e2)))))))).(\lambda (v1: T).(\lambda (v2: T).(\lambda (e1: C).(\lambda (h: 
nat).(\lambda (H2: (drop h O (CHead c3 (Bind Void) v1) e1)).(nat_ind (\lambda 
(n: nat).((drop n O (CHead c3 (Bind Void) v1) e1) \to (ex2 C (\lambda (e2: 
C).(csubv e1 e2)) (\lambda (e2: C).(drop n O (CHead c4 (Bind Void) v2) 
e2))))) (\lambda (H3: (drop O O (CHead c3 (Bind Void) v1) e1)).(eq_ind C 
(CHead c3 (Bind Void) v1) (\lambda (c: C).(ex2 C (\lambda (e2: C).(csubv c 
e2)) (\lambda (e2: C).(drop O O (CHead c4 (Bind Void) v2) e2)))) (ex_intro2 C 
(\lambda (e2: C).(csubv (CHead c3 (Bind Void) v1) e2)) (\lambda (e2: C).(drop 
O O (CHead c4 (Bind Void) v2) e2)) (CHead c4 (Bind Void) v2) (csubv_bind_same 
c3 c4 H0 Void v1 v2) (drop_refl (CHead c4 (Bind Void) v2))) e1 (drop_gen_refl 
(CHead c3 (Bind Void) v1) e1 H3))) (\lambda (h0: nat).(\lambda (_: (((drop h0 
O (CHead c3 (Bind Void) v1) e1) \to (ex2 C (\lambda (e2: C).(csubv e1 e2)) 
(\lambda (e2: C).(drop h0 O (CHead c4 (Bind Void) v2) e2)))))).(\lambda (H3: 
(drop (S h0) O (CHead c3 (Bind Void) v1) e1)).(let H_x \def (H1 e1 (r (Bind 
Void) h0) (drop_gen_drop (Bind Void) c3 e1 v1 h0 H3)) in (let H4 \def H_x in 
(ex2_ind C (\lambda (e2: C).(csubv e1 e2)) (\lambda (e2: C).(drop h0 O c4 
e2)) (ex2 C (\lambda (e2: C).(csubv e1 e2)) (\lambda (e2: C).(drop (S h0) O 
(CHead c4 (Bind Void) v2) e2))) (\lambda (x: C).(\lambda (H5: (csubv e1 
x)).(\lambda (H6: (drop h0 O c4 x)).(ex_intro2 C (\lambda (e2: C).(csubv e1 
e2)) (\lambda (e2: C).(drop (S h0) O (CHead c4 (Bind Void) v2) e2)) x H5 
(drop_drop (Bind Void) h0 c4 x H6 v2))))) H4)))))) h H2)))))))))) (\lambda 
(c3: C).(\lambda (c4: C).(\lambda (H0: (csubv c3 c4)).(\lambda (H1: ((\forall 
(e1: C).(\forall (h: nat).((drop h O c3 e1) \to (ex2 C (\lambda (e2: 
C).(csubv e1 e2)) (\lambda (e2: C).(drop h O c4 e2)))))))).(\lambda (b1: 
B).(\lambda (H2: (not (eq B b1 Void))).(\lambda (b2: B).(\lambda (v1: 
T).(\lambda (v2: T).(\lambda (e1: C).(\lambda (h: nat).(\lambda (H3: (drop h 
O (CHead c3 (Bind b1) v1) e1)).(nat_ind (\lambda (n: nat).((drop n O (CHead 
c3 (Bind b1) v1) e1) \to (ex2 C (\lambda (e2: C).(csubv e1 e2)) (\lambda (e2: 
C).(drop n O (CHead c4 (Bind b2) v2) e2))))) (\lambda (H4: (drop O O (CHead 
c3 (Bind b1) v1) e1)).(eq_ind C (CHead c3 (Bind b1) v1) (\lambda (c: C).(ex2 
C (\lambda (e2: C).(csubv c e2)) (\lambda (e2: C).(drop O O (CHead c4 (Bind 
b2) v2) e2)))) (ex_intro2 C (\lambda (e2: C).(csubv (CHead c3 (Bind b1) v1) 
e2)) (\lambda (e2: C).(drop O O (CHead c4 (Bind b2) v2) e2)) (CHead c4 (Bind 
b2) v2) (csubv_bind c3 c4 H0 b1 H2 b2 v1 v2) (drop_refl (CHead c4 (Bind b2) 
v2))) e1 (drop_gen_refl (CHead c3 (Bind b1) v1) e1 H4))) (\lambda (h0: 
nat).(\lambda (_: (((drop h0 O (CHead c3 (Bind b1) v1) e1) \to (ex2 C 
(\lambda (e2: C).(csubv e1 e2)) (\lambda (e2: C).(drop h0 O (CHead c4 (Bind 
b2) v2) e2)))))).(\lambda (H4: (drop (S h0) O (CHead c3 (Bind b1) v1) 
e1)).(let H_x \def (H1 e1 (r (Bind b1) h0) (drop_gen_drop (Bind b1) c3 e1 v1 
h0 H4)) in (let H5 \def H_x in (ex2_ind C (\lambda (e2: C).(csubv e1 e2)) 
(\lambda (e2: C).(drop h0 O c4 e2)) (ex2 C (\lambda (e2: C).(csubv e1 e2)) 
(\lambda (e2: C).(drop (S h0) O (CHead c4 (Bind b2) v2) e2))) (\lambda (x: 
C).(\lambda (H6: (csubv e1 x)).(\lambda (H7: (drop h0 O c4 x)).(ex_intro2 C 
(\lambda (e2: C).(csubv e1 e2)) (\lambda (e2: C).(drop (S h0) O (CHead c4 
(Bind b2) v2) e2)) x H6 (drop_drop (Bind b2) h0 c4 x H7 v2))))) H5)))))) h 
H3))))))))))))) (\lambda (c3: C).(\lambda (c4: C).(\lambda (H0: (csubv c3 
c4)).(\lambda (H1: ((\forall (e1: C).(\forall (h: nat).((drop h O c3 e1) \to 
(ex2 C (\lambda (e2: C).(csubv e1 e2)) (\lambda (e2: C).(drop h O c4 
e2)))))))).(\lambda (f1: F).(\lambda (f2: F).(\lambda (v1: T).(\lambda (v2: 
T).(\lambda (e1: C).(\lambda (h: nat).(\lambda (H2: (drop h O (CHead c3 (Flat 
f1) v1) e1)).(nat_ind (\lambda (n: nat).((drop n O (CHead c3 (Flat f1) v1) 
e1) \to (ex2 C (\lambda (e2: C).(csubv e1 e2)) (\lambda (e2: C).(drop n O 
(CHead c4 (Flat f2) v2) e2))))) (\lambda (H3: (drop O O (CHead c3 (Flat f1) 
v1) e1)).(eq_ind C (CHead c3 (Flat f1) v1) (\lambda (c: C).(ex2 C (\lambda 
(e2: C).(csubv c e2)) (\lambda (e2: C).(drop O O (CHead c4 (Flat f2) v2) 
e2)))) (ex_intro2 C (\lambda (e2: C).(csubv (CHead c3 (Flat f1) v1) e2)) 
(\lambda (e2: C).(drop O O (CHead c4 (Flat f2) v2) e2)) (CHead c4 (Flat f2) 
v2) (csubv_flat c3 c4 H0 f1 f2 v1 v2) (drop_refl (CHead c4 (Flat f2) v2))) e1 
(drop_gen_refl (CHead c3 (Flat f1) v1) e1 H3))) (\lambda (h0: nat).(\lambda 
(_: (((drop h0 O (CHead c3 (Flat f1) v1) e1) \to (ex2 C (\lambda (e2: 
C).(csubv e1 e2)) (\lambda (e2: C).(drop h0 O (CHead c4 (Flat f2) v2) 
e2)))))).(\lambda (H3: (drop (S h0) O (CHead c3 (Flat f1) v1) e1)).(let H_x 
\def (H1 e1 (r (Flat f1) h0) (drop_gen_drop (Flat f1) c3 e1 v1 h0 H3)) in 
(let H4 \def H_x in (ex2_ind C (\lambda (e2: C).(csubv e1 e2)) (\lambda (e2: 
C).(drop (S h0) O c4 e2)) (ex2 C (\lambda (e2: C).(csubv e1 e2)) (\lambda 
(e2: C).(drop (S h0) O (CHead c4 (Flat f2) v2) e2))) (\lambda (x: C).(\lambda 
(H5: (csubv e1 x)).(\lambda (H6: (drop (S h0) O c4 x)).(ex_intro2 C (\lambda 
(e2: C).(csubv e1 e2)) (\lambda (e2: C).(drop (S h0) O (CHead c4 (Flat f2) 
v2) e2)) x H5 (drop_drop (Flat f2) h0 c4 x H6 v2))))) H4)))))) h 
H2)))))))))))) c1 c2 H))).
(* COMMENTS
Initial nodes: 1897
END *)

