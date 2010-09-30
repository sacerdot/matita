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

include "Basic-1/sty1/props.ma".

include "Basic-1/cnt/props.ma".

theorem sty1_cnt:
 \forall (g: G).(\forall (c: C).(\forall (t1: T).(\forall (t: T).((sty0 g c 
t1 t) \to (ex2 T (\lambda (t2: T).(sty1 g c t1 t2)) (\lambda (t2: T).(cnt 
t2)))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (t1: T).(\lambda (t: T).(\lambda (H: 
(sty0 g c t1 t)).(sty0_ind g (\lambda (c0: C).(\lambda (t0: T).(\lambda (_: 
T).(ex2 T (\lambda (t3: T).(sty1 g c0 t0 t3)) (\lambda (t3: T).(cnt t3)))))) 
(\lambda (c0: C).(\lambda (n: nat).(ex_intro2 T (\lambda (t2: T).(sty1 g c0 
(TSort n) t2)) (\lambda (t2: T).(cnt t2)) (TSort (next g n)) (sty1_sty0 g c0 
(TSort n) (TSort (next g n)) (sty0_sort g c0 n)) (cnt_sort (next g n))))) 
(\lambda (c0: C).(\lambda (d: C).(\lambda (v: T).(\lambda (i: nat).(\lambda 
(H0: (getl i c0 (CHead d (Bind Abbr) v))).(\lambda (w: T).(\lambda (_: (sty0 
g d v w)).(\lambda (H2: (ex2 T (\lambda (t2: T).(sty1 g d v t2)) (\lambda 
(t2: T).(cnt t2)))).(let H3 \def H2 in (ex2_ind T (\lambda (t2: T).(sty1 g d 
v t2)) (\lambda (t2: T).(cnt t2)) (ex2 T (\lambda (t2: T).(sty1 g c0 (TLRef 
i) t2)) (\lambda (t2: T).(cnt t2))) (\lambda (x: T).(\lambda (H4: (sty1 g d v 
x)).(\lambda (H5: (cnt x)).(ex_intro2 T (\lambda (t2: T).(sty1 g c0 (TLRef i) 
t2)) (\lambda (t2: T).(cnt t2)) (lift (S i) O x) (sty1_abbr g c0 d v i H0 x 
H4) (cnt_lift x H5 (S i) O))))) H3)))))))))) (\lambda (c0: C).(\lambda (d: 
C).(\lambda (v: T).(\lambda (i: nat).(\lambda (H0: (getl i c0 (CHead d (Bind 
Abst) v))).(\lambda (w: T).(\lambda (H1: (sty0 g d v w)).(\lambda (H2: (ex2 T 
(\lambda (t2: T).(sty1 g d v t2)) (\lambda (t2: T).(cnt t2)))).(let H3 \def 
H2 in (ex2_ind T (\lambda (t2: T).(sty1 g d v t2)) (\lambda (t2: T).(cnt t2)) 
(ex2 T (\lambda (t2: T).(sty1 g c0 (TLRef i) t2)) (\lambda (t2: T).(cnt t2))) 
(\lambda (x: T).(\lambda (H4: (sty1 g d v x)).(\lambda (H5: (cnt 
x)).(ex_intro2 T (\lambda (t2: T).(sty1 g c0 (TLRef i) t2)) (\lambda (t2: 
T).(cnt t2)) (lift (S i) O x) (sty1_trans g c0 (TLRef i) (lift (S i) O v) 
(sty1_sty0 g c0 (TLRef i) (lift (S i) O v) (sty0_abst g c0 d v i H0 w H1)) 
(lift (S i) O x) (sty1_lift g d v x H4 c0 (S i) O (getl_drop Abst c0 d v i 
H0))) (cnt_lift x H5 (S i) O))))) H3)))))))))) (\lambda (b: B).(\lambda (c0: 
C).(\lambda (v: T).(\lambda (t2: T).(\lambda (t3: T).(\lambda (_: (sty0 g 
(CHead c0 (Bind b) v) t2 t3)).(\lambda (H1: (ex2 T (\lambda (t4: T).(sty1 g 
(CHead c0 (Bind b) v) t2 t4)) (\lambda (t4: T).(cnt t4)))).(let H2 \def H1 in 
(ex2_ind T (\lambda (t4: T).(sty1 g (CHead c0 (Bind b) v) t2 t4)) (\lambda 
(t4: T).(cnt t4)) (ex2 T (\lambda (t4: T).(sty1 g c0 (THead (Bind b) v t2) 
t4)) (\lambda (t4: T).(cnt t4))) (\lambda (x: T).(\lambda (H3: (sty1 g (CHead 
c0 (Bind b) v) t2 x)).(\lambda (H4: (cnt x)).(ex_intro2 T (\lambda (t4: 
T).(sty1 g c0 (THead (Bind b) v t2) t4)) (\lambda (t4: T).(cnt t4)) (THead 
(Bind b) v x) (sty1_bind g b c0 v t2 x H3) (cnt_head x H4 (Bind b) v))))) 
H2))))))))) (\lambda (c0: C).(\lambda (v: T).(\lambda (t2: T).(\lambda (t3: 
T).(\lambda (_: (sty0 g c0 t2 t3)).(\lambda (H1: (ex2 T (\lambda (t4: 
T).(sty1 g c0 t2 t4)) (\lambda (t4: T).(cnt t4)))).(let H2 \def H1 in 
(ex2_ind T (\lambda (t4: T).(sty1 g c0 t2 t4)) (\lambda (t4: T).(cnt t4)) 
(ex2 T (\lambda (t4: T).(sty1 g c0 (THead (Flat Appl) v t2) t4)) (\lambda 
(t4: T).(cnt t4))) (\lambda (x: T).(\lambda (H3: (sty1 g c0 t2 x)).(\lambda 
(H4: (cnt x)).(ex_intro2 T (\lambda (t4: T).(sty1 g c0 (THead (Flat Appl) v 
t2) t4)) (\lambda (t4: T).(cnt t4)) (THead (Flat Appl) v x) (sty1_appl g c0 v 
t2 x H3) (cnt_head x H4 (Flat Appl) v))))) H2)))))))) (\lambda (c0: 
C).(\lambda (v1: T).(\lambda (v2: T).(\lambda (H0: (sty0 g c0 v1 
v2)).(\lambda (_: (ex2 T (\lambda (t2: T).(sty1 g c0 v1 t2)) (\lambda (t2: 
T).(cnt t2)))).(\lambda (t2: T).(\lambda (t3: T).(\lambda (_: (sty0 g c0 t2 
t3)).(\lambda (H3: (ex2 T (\lambda (t4: T).(sty1 g c0 t2 t4)) (\lambda (t4: 
T).(cnt t4)))).(let H4 \def H3 in (ex2_ind T (\lambda (t4: T).(sty1 g c0 t2 
t4)) (\lambda (t4: T).(cnt t4)) (ex2 T (\lambda (t4: T).(sty1 g c0 (THead 
(Flat Cast) v1 t2) t4)) (\lambda (t4: T).(cnt t4))) (\lambda (x: T).(\lambda 
(H5: (sty1 g c0 t2 x)).(\lambda (H6: (cnt x)).(let H_x \def (sty1_cast2 g c0 
t2 x H5 v1 v2 H0) in (let H7 \def H_x in (ex2_ind T (\lambda (v3: T).(sty1 g 
c0 v1 v3)) (\lambda (v3: T).(sty1 g c0 (THead (Flat Cast) v1 t2) (THead (Flat 
Cast) v3 x))) (ex2 T (\lambda (t4: T).(sty1 g c0 (THead (Flat Cast) v1 t2) 
t4)) (\lambda (t4: T).(cnt t4))) (\lambda (x0: T).(\lambda (_: (sty1 g c0 v1 
x0)).(\lambda (H9: (sty1 g c0 (THead (Flat Cast) v1 t2) (THead (Flat Cast) x0 
x))).(ex_intro2 T (\lambda (t4: T).(sty1 g c0 (THead (Flat Cast) v1 t2) t4)) 
(\lambda (t4: T).(cnt t4)) (THead (Flat Cast) x0 x) H9 (cnt_head x H6 (Flat 
Cast) x0))))) H7)))))) H4))))))))))) c t1 t H))))).
(* COMMENTS
Initial nodes: 1313
END *)

