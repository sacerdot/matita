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

include "Basic-1/csubt/defs.ma".

include "Basic-1/clear/fwd.ma".

theorem csubt_clear_conf:
 \forall (g: G).(\forall (c1: C).(\forall (c2: C).((csubt g c1 c2) \to 
(\forall (e1: C).((clear c1 e1) \to (ex2 C (\lambda (e2: C).(csubt g e1 e2)) 
(\lambda (e2: C).(clear c2 e2))))))))
\def
 \lambda (g: G).(\lambda (c1: C).(\lambda (c2: C).(\lambda (H: (csubt g c1 
c2)).(csubt_ind g (\lambda (c: C).(\lambda (c0: C).(\forall (e1: C).((clear c 
e1) \to (ex2 C (\lambda (e2: C).(csubt g e1 e2)) (\lambda (e2: C).(clear c0 
e2))))))) (\lambda (n: nat).(\lambda (e1: C).(\lambda (H0: (clear (CSort n) 
e1)).(clear_gen_sort e1 n H0 (ex2 C (\lambda (e2: C).(csubt g e1 e2)) 
(\lambda (e2: C).(clear (CSort n) e2))))))) (\lambda (c3: C).(\lambda (c4: 
C).(\lambda (H0: (csubt g c3 c4)).(\lambda (H1: ((\forall (e1: C).((clear c3 
e1) \to (ex2 C (\lambda (e2: C).(csubt g e1 e2)) (\lambda (e2: C).(clear c4 
e2))))))).(\lambda (k: K).(\lambda (u: T).(\lambda (e1: C).(\lambda (H2: 
(clear (CHead c3 k u) e1)).(K_ind (\lambda (k0: K).((clear (CHead c3 k0 u) 
e1) \to (ex2 C (\lambda (e2: C).(csubt g e1 e2)) (\lambda (e2: C).(clear 
(CHead c4 k0 u) e2))))) (\lambda (b: B).(\lambda (H3: (clear (CHead c3 (Bind 
b) u) e1)).(eq_ind_r C (CHead c3 (Bind b) u) (\lambda (c: C).(ex2 C (\lambda 
(e2: C).(csubt g c e2)) (\lambda (e2: C).(clear (CHead c4 (Bind b) u) e2)))) 
(ex_intro2 C (\lambda (e2: C).(csubt g (CHead c3 (Bind b) u) e2)) (\lambda 
(e2: C).(clear (CHead c4 (Bind b) u) e2)) (CHead c4 (Bind b) u) (csubt_head g 
c3 c4 H0 (Bind b) u) (clear_bind b c4 u)) e1 (clear_gen_bind b c3 e1 u H3)))) 
(\lambda (f: F).(\lambda (H3: (clear (CHead c3 (Flat f) u) e1)).(let H4 \def 
(H1 e1 (clear_gen_flat f c3 e1 u H3)) in (ex2_ind C (\lambda (e2: C).(csubt g 
e1 e2)) (\lambda (e2: C).(clear c4 e2)) (ex2 C (\lambda (e2: C).(csubt g e1 
e2)) (\lambda (e2: C).(clear (CHead c4 (Flat f) u) e2))) (\lambda (x: 
C).(\lambda (H5: (csubt g e1 x)).(\lambda (H6: (clear c4 x)).(ex_intro2 C 
(\lambda (e2: C).(csubt g e1 e2)) (\lambda (e2: C).(clear (CHead c4 (Flat f) 
u) e2)) x H5 (clear_flat c4 x H6 f u))))) H4)))) k H2))))))))) (\lambda (c3: 
C).(\lambda (c4: C).(\lambda (H0: (csubt g c3 c4)).(\lambda (_: ((\forall 
(e1: C).((clear c3 e1) \to (ex2 C (\lambda (e2: C).(csubt g e1 e2)) (\lambda 
(e2: C).(clear c4 e2))))))).(\lambda (b: B).(\lambda (H2: (not (eq B b 
Void))).(\lambda (u1: T).(\lambda (u2: T).(\lambda (e1: C).(\lambda (H3: 
(clear (CHead c3 (Bind Void) u1) e1)).(eq_ind_r C (CHead c3 (Bind Void) u1) 
(\lambda (c: C).(ex2 C (\lambda (e2: C).(csubt g c e2)) (\lambda (e2: 
C).(clear (CHead c4 (Bind b) u2) e2)))) (ex_intro2 C (\lambda (e2: C).(csubt 
g (CHead c3 (Bind Void) u1) e2)) (\lambda (e2: C).(clear (CHead c4 (Bind b) 
u2) e2)) (CHead c4 (Bind b) u2) (csubt_void g c3 c4 H0 b H2 u1 u2) 
(clear_bind b c4 u2)) e1 (clear_gen_bind Void c3 e1 u1 H3)))))))))))) 
(\lambda (c3: C).(\lambda (c4: C).(\lambda (H0: (csubt g c3 c4)).(\lambda (_: 
((\forall (e1: C).((clear c3 e1) \to (ex2 C (\lambda (e2: C).(csubt g e1 e2)) 
(\lambda (e2: C).(clear c4 e2))))))).(\lambda (u: T).(\lambda (t: T).(\lambda 
(H2: (ty3 g c3 u t)).(\lambda (H3: (ty3 g c4 u t)).(\lambda (e1: C).(\lambda 
(H4: (clear (CHead c3 (Bind Abst) t) e1)).(eq_ind_r C (CHead c3 (Bind Abst) 
t) (\lambda (c: C).(ex2 C (\lambda (e2: C).(csubt g c e2)) (\lambda (e2: 
C).(clear (CHead c4 (Bind Abbr) u) e2)))) (ex_intro2 C (\lambda (e2: 
C).(csubt g (CHead c3 (Bind Abst) t) e2)) (\lambda (e2: C).(clear (CHead c4 
(Bind Abbr) u) e2)) (CHead c4 (Bind Abbr) u) (csubt_abst g c3 c4 H0 u t H2 
H3) (clear_bind Abbr c4 u)) e1 (clear_gen_bind Abst c3 e1 t H4)))))))))))) c1 
c2 H)))).
(* COMMENTS
Initial nodes: 929
END *)

