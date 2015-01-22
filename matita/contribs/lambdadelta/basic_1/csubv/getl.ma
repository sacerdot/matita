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

include "Basic-1/csubv/clear.ma".

include "Basic-1/csubv/drop.ma".

include "Basic-1/getl/fwd.ma".

theorem csubv_getl_conf:
 \forall (c1: C).(\forall (c2: C).((csubv c1 c2) \to (\forall (b1: 
B).(\forall (d1: C).(\forall (v1: T).(\forall (i: nat).((getl i c1 (CHead d1 
(Bind b1) v1)) \to (ex2_3 B C T (\lambda (_: B).(\lambda (d2: C).(\lambda (_: 
T).(csubv d1 d2)))) (\lambda (b2: B).(\lambda (d2: C).(\lambda (v2: T).(getl 
i c2 (CHead d2 (Bind b2) v2)))))))))))))
\def
 \lambda (c1: C).(\lambda (c2: C).(\lambda (H: (csubv c1 c2)).(\lambda (b1: 
B).(\lambda (d1: C).(\lambda (v1: T).(\lambda (i: nat).(\lambda (H0: (getl i 
c1 (CHead d1 (Bind b1) v1))).(let H1 \def (getl_gen_all c1 (CHead d1 (Bind 
b1) v1) i H0) in (ex2_ind C (\lambda (e: C).(drop i O c1 e)) (\lambda (e: 
C).(clear e (CHead d1 (Bind b1) v1))) (ex2_3 B C T (\lambda (_: B).(\lambda 
(d2: C).(\lambda (_: T).(csubv d1 d2)))) (\lambda (b2: B).(\lambda (d2: 
C).(\lambda (v2: T).(getl i c2 (CHead d2 (Bind b2) v2)))))) (\lambda (x: 
C).(\lambda (H2: (drop i O c1 x)).(\lambda (H3: (clear x (CHead d1 (Bind b1) 
v1))).(let H_x \def (csubv_drop_conf c1 c2 H x i H2) in (let H4 \def H_x in 
(ex2_ind C (\lambda (e2: C).(csubv x e2)) (\lambda (e2: C).(drop i O c2 e2)) 
(ex2_3 B C T (\lambda (_: B).(\lambda (d2: C).(\lambda (_: T).(csubv d1 
d2)))) (\lambda (b2: B).(\lambda (d2: C).(\lambda (v2: T).(getl i c2 (CHead 
d2 (Bind b2) v2)))))) (\lambda (x0: C).(\lambda (H5: (csubv x x0)).(\lambda 
(H6: (drop i O c2 x0)).(let H_x0 \def (csubv_clear_conf x x0 H5 b1 d1 v1 H3) 
in (let H7 \def H_x0 in (ex2_3_ind B C T (\lambda (_: B).(\lambda (d2: 
C).(\lambda (_: T).(csubv d1 d2)))) (\lambda (b2: B).(\lambda (d2: 
C).(\lambda (v2: T).(clear x0 (CHead d2 (Bind b2) v2))))) (ex2_3 B C T 
(\lambda (_: B).(\lambda (d2: C).(\lambda (_: T).(csubv d1 d2)))) (\lambda 
(b2: B).(\lambda (d2: C).(\lambda (v2: T).(getl i c2 (CHead d2 (Bind b2) 
v2)))))) (\lambda (x1: B).(\lambda (x2: C).(\lambda (x3: T).(\lambda (H8: 
(csubv d1 x2)).(\lambda (H9: (clear x0 (CHead x2 (Bind x1) x3))).(ex2_3_intro 
B C T (\lambda (_: B).(\lambda (d2: C).(\lambda (_: T).(csubv d1 d2)))) 
(\lambda (b2: B).(\lambda (d2: C).(\lambda (v2: T).(getl i c2 (CHead d2 (Bind 
b2) v2))))) x1 x2 x3 H8 (getl_intro i c2 (CHead x2 (Bind x1) x3) x0 H6 
H9))))))) H7)))))) H4)))))) H1))))))))).
(* COMMENTS
Initial nodes: 455
END *)

theorem csubv_getl_conf_void:
 \forall (c1: C).(\forall (c2: C).((csubv c1 c2) \to (\forall (d1: 
C).(\forall (v1: T).(\forall (i: nat).((getl i c1 (CHead d1 (Bind Void) v1)) 
\to (ex2_2 C T (\lambda (d2: C).(\lambda (_: T).(csubv d1 d2))) (\lambda (d2: 
C).(\lambda (v2: T).(getl i c2 (CHead d2 (Bind Void) v2)))))))))))
\def
 \lambda (c1: C).(\lambda (c2: C).(\lambda (H: (csubv c1 c2)).(\lambda (d1: 
C).(\lambda (v1: T).(\lambda (i: nat).(\lambda (H0: (getl i c1 (CHead d1 
(Bind Void) v1))).(let H1 \def (getl_gen_all c1 (CHead d1 (Bind Void) v1) i 
H0) in (ex2_ind C (\lambda (e: C).(drop i O c1 e)) (\lambda (e: C).(clear e 
(CHead d1 (Bind Void) v1))) (ex2_2 C T (\lambda (d2: C).(\lambda (_: 
T).(csubv d1 d2))) (\lambda (d2: C).(\lambda (v2: T).(getl i c2 (CHead d2 
(Bind Void) v2))))) (\lambda (x: C).(\lambda (H2: (drop i O c1 x)).(\lambda 
(H3: (clear x (CHead d1 (Bind Void) v1))).(let H_x \def (csubv_drop_conf c1 
c2 H x i H2) in (let H4 \def H_x in (ex2_ind C (\lambda (e2: C).(csubv x e2)) 
(\lambda (e2: C).(drop i O c2 e2)) (ex2_2 C T (\lambda (d2: C).(\lambda (_: 
T).(csubv d1 d2))) (\lambda (d2: C).(\lambda (v2: T).(getl i c2 (CHead d2 
(Bind Void) v2))))) (\lambda (x0: C).(\lambda (H5: (csubv x x0)).(\lambda 
(H6: (drop i O c2 x0)).(let H_x0 \def (csubv_clear_conf_void x x0 H5 d1 v1 
H3) in (let H7 \def H_x0 in (ex2_2_ind C T (\lambda (d2: C).(\lambda (_: 
T).(csubv d1 d2))) (\lambda (d2: C).(\lambda (v2: T).(clear x0 (CHead d2 
(Bind Void) v2)))) (ex2_2 C T (\lambda (d2: C).(\lambda (_: T).(csubv d1 
d2))) (\lambda (d2: C).(\lambda (v2: T).(getl i c2 (CHead d2 (Bind Void) 
v2))))) (\lambda (x1: C).(\lambda (x2: T).(\lambda (H8: (csubv d1 
x1)).(\lambda (H9: (clear x0 (CHead x1 (Bind Void) x2))).(ex2_2_intro C T 
(\lambda (d2: C).(\lambda (_: T).(csubv d1 d2))) (\lambda (d2: C).(\lambda 
(v2: T).(getl i c2 (CHead d2 (Bind Void) v2)))) x1 x2 H8 (getl_intro i c2 
(CHead x1 (Bind Void) x2) x0 H6 H9)))))) H7)))))) H4)))))) H1)))))))).
(* COMMENTS
Initial nodes: 417
END *)

