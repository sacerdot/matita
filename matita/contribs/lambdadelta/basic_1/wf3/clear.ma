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

include "Basic-1/wf3/fwd.ma".

theorem wf3_clear_conf:
 \forall (c1: C).(\forall (c: C).((clear c1 c) \to (\forall (g: G).(\forall 
(c2: C).((wf3 g c1 c2) \to (wf3 g c c2))))))
\def
 \lambda (c1: C).(\lambda (c: C).(\lambda (H: (clear c1 c)).(clear_ind 
(\lambda (c0: C).(\lambda (c2: C).(\forall (g: G).(\forall (c3: C).((wf3 g c0 
c3) \to (wf3 g c2 c3)))))) (\lambda (b: B).(\lambda (e: C).(\lambda (u: 
T).(\lambda (g: G).(\lambda (c2: C).(\lambda (H0: (wf3 g (CHead e (Bind b) u) 
c2)).H0)))))) (\lambda (e: C).(\lambda (c0: C).(\lambda (_: (clear e 
c0)).(\lambda (H1: ((\forall (g: G).(\forall (c2: C).((wf3 g e c2) \to (wf3 g 
c0 c2)))))).(\lambda (f: F).(\lambda (u: T).(\lambda (g: G).(\lambda (c2: 
C).(\lambda (H2: (wf3 g (CHead e (Flat f) u) c2)).(let H_y \def 
(wf3_gen_flat1 g e c2 u f H2) in (H1 g c2 H_y))))))))))) c1 c H))).
(* COMMENTS
Initial nodes: 145
END *)

theorem clear_wf3_trans:
 \forall (c1: C).(\forall (d1: C).((clear c1 d1) \to (\forall (g: G).(\forall 
(d2: C).((wf3 g d1 d2) \to (ex2 C (\lambda (c2: C).(wf3 g c1 c2)) (\lambda 
(c2: C).(clear c2 d2))))))))
\def
 \lambda (c1: C).(\lambda (d1: C).(\lambda (H: (clear c1 d1)).(clear_ind 
(\lambda (c: C).(\lambda (c0: C).(\forall (g: G).(\forall (d2: C).((wf3 g c0 
d2) \to (ex2 C (\lambda (c2: C).(wf3 g c c2)) (\lambda (c2: C).(clear c2 
d2)))))))) (\lambda (b: B).(\lambda (e: C).(\lambda (u: T).(\lambda (g: 
G).(\lambda (d2: C).(\lambda (H0: (wf3 g (CHead e (Bind b) u) d2)).(let H_x 
\def (wf3_gen_bind1 g e d2 u b H0) in (let H1 \def H_x in (or_ind (ex3_2 C T 
(\lambda (c2: C).(\lambda (_: T).(eq C d2 (CHead c2 (Bind b) u)))) (\lambda 
(c2: C).(\lambda (_: T).(wf3 g e c2))) (\lambda (_: C).(\lambda (w: T).(ty3 g 
e u w)))) (ex3 C (\lambda (c2: C).(eq C d2 (CHead c2 (Bind Void) (TSort O)))) 
(\lambda (c2: C).(wf3 g e c2)) (\lambda (_: C).(\forall (w: T).((ty3 g e u w) 
\to False)))) (ex2 C (\lambda (c2: C).(wf3 g (CHead e (Bind b) u) c2)) 
(\lambda (c2: C).(clear c2 d2))) (\lambda (H2: (ex3_2 C T (\lambda (c2: 
C).(\lambda (_: T).(eq C d2 (CHead c2 (Bind b) u)))) (\lambda (c2: 
C).(\lambda (_: T).(wf3 g e c2))) (\lambda (_: C).(\lambda (w: T).(ty3 g e u 
w))))).(ex3_2_ind C T (\lambda (c2: C).(\lambda (_: T).(eq C d2 (CHead c2 
(Bind b) u)))) (\lambda (c2: C).(\lambda (_: T).(wf3 g e c2))) (\lambda (_: 
C).(\lambda (w: T).(ty3 g e u w))) (ex2 C (\lambda (c2: C).(wf3 g (CHead e 
(Bind b) u) c2)) (\lambda (c2: C).(clear c2 d2))) (\lambda (x0: C).(\lambda 
(x1: T).(\lambda (H3: (eq C d2 (CHead x0 (Bind b) u))).(\lambda (H4: (wf3 g e 
x0)).(\lambda (H5: (ty3 g e u x1)).(eq_ind_r C (CHead x0 (Bind b) u) (\lambda 
(c: C).(ex2 C (\lambda (c2: C).(wf3 g (CHead e (Bind b) u) c2)) (\lambda (c2: 
C).(clear c2 c)))) (ex_intro2 C (\lambda (c2: C).(wf3 g (CHead e (Bind b) u) 
c2)) (\lambda (c2: C).(clear c2 (CHead x0 (Bind b) u))) (CHead x0 (Bind b) u) 
(wf3_bind g e x0 H4 u x1 H5 b) (clear_bind b x0 u)) d2 H3)))))) H2)) (\lambda 
(H2: (ex3 C (\lambda (c2: C).(eq C d2 (CHead c2 (Bind Void) (TSort O)))) 
(\lambda (c2: C).(wf3 g e c2)) (\lambda (_: C).(\forall (w: T).((ty3 g e u w) 
\to False))))).(ex3_ind C (\lambda (c2: C).(eq C d2 (CHead c2 (Bind Void) 
(TSort O)))) (\lambda (c2: C).(wf3 g e c2)) (\lambda (_: C).(\forall (w: 
T).((ty3 g e u w) \to False))) (ex2 C (\lambda (c2: C).(wf3 g (CHead e (Bind 
b) u) c2)) (\lambda (c2: C).(clear c2 d2))) (\lambda (x0: C).(\lambda (H3: 
(eq C d2 (CHead x0 (Bind Void) (TSort O)))).(\lambda (H4: (wf3 g e 
x0)).(\lambda (H5: ((\forall (w: T).((ty3 g e u w) \to False)))).(eq_ind_r C 
(CHead x0 (Bind Void) (TSort O)) (\lambda (c: C).(ex2 C (\lambda (c2: C).(wf3 
g (CHead e (Bind b) u) c2)) (\lambda (c2: C).(clear c2 c)))) (ex_intro2 C 
(\lambda (c2: C).(wf3 g (CHead e (Bind b) u) c2)) (\lambda (c2: C).(clear c2 
(CHead x0 (Bind Void) (TSort O)))) (CHead x0 (Bind Void) (TSort O)) (wf3_void 
g e x0 H4 u H5 b) (clear_bind Void x0 (TSort O))) d2 H3))))) H2)) H1))))))))) 
(\lambda (e: C).(\lambda (c: C).(\lambda (_: (clear e c)).(\lambda (H1: 
((\forall (g: G).(\forall (d2: C).((wf3 g c d2) \to (ex2 C (\lambda (c2: 
C).(wf3 g e c2)) (\lambda (c2: C).(clear c2 d2)))))))).(\lambda (f: 
F).(\lambda (u: T).(\lambda (g: G).(\lambda (d2: C).(\lambda (H2: (wf3 g c 
d2)).(let H_x \def (H1 g d2 H2) in (let H3 \def H_x in (ex2_ind C (\lambda 
(c2: C).(wf3 g e c2)) (\lambda (c2: C).(clear c2 d2)) (ex2 C (\lambda (c2: 
C).(wf3 g (CHead e (Flat f) u) c2)) (\lambda (c2: C).(clear c2 d2))) (\lambda 
(x: C).(\lambda (H4: (wf3 g e x)).(\lambda (H5: (clear x d2)).(ex_intro2 C 
(\lambda (c2: C).(wf3 g (CHead e (Flat f) u) c2)) (\lambda (c2: C).(clear c2 
d2)) x (wf3_flat g e x H4 u f) H5)))) H3)))))))))))) c1 d1 H))).
(* COMMENTS
Initial nodes: 1023
END *)

