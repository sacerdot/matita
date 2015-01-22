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

include "Basic-1/csuba/defs.ma".

include "Basic-1/clear/fwd.ma".

theorem csuba_clear_conf:
 \forall (g: G).(\forall (c1: C).(\forall (c2: C).((csuba g c1 c2) \to 
(\forall (e1: C).((clear c1 e1) \to (ex2 C (\lambda (e2: C).(csuba g e1 e2)) 
(\lambda (e2: C).(clear c2 e2))))))))
\def
 \lambda (g: G).(\lambda (c1: C).(\lambda (c2: C).(\lambda (H: (csuba g c1 
c2)).(csuba_ind g (\lambda (c: C).(\lambda (c0: C).(\forall (e1: C).((clear c 
e1) \to (ex2 C (\lambda (e2: C).(csuba g e1 e2)) (\lambda (e2: C).(clear c0 
e2))))))) (\lambda (n: nat).(\lambda (e1: C).(\lambda (H0: (clear (CSort n) 
e1)).(clear_gen_sort e1 n H0 (ex2 C (\lambda (e2: C).(csuba g e1 e2)) 
(\lambda (e2: C).(clear (CSort n) e2))))))) (\lambda (c3: C).(\lambda (c4: 
C).(\lambda (H0: (csuba g c3 c4)).(\lambda (H1: ((\forall (e1: C).((clear c3 
e1) \to (ex2 C (\lambda (e2: C).(csuba g e1 e2)) (\lambda (e2: C).(clear c4 
e2))))))).(\lambda (k: K).(\lambda (u: T).(\lambda (e1: C).(\lambda (H2: 
(clear (CHead c3 k u) e1)).(K_ind (\lambda (k0: K).((clear (CHead c3 k0 u) 
e1) \to (ex2 C (\lambda (e2: C).(csuba g e1 e2)) (\lambda (e2: C).(clear 
(CHead c4 k0 u) e2))))) (\lambda (b: B).(\lambda (H3: (clear (CHead c3 (Bind 
b) u) e1)).(eq_ind_r C (CHead c3 (Bind b) u) (\lambda (c: C).(ex2 C (\lambda 
(e2: C).(csuba g c e2)) (\lambda (e2: C).(clear (CHead c4 (Bind b) u) e2)))) 
(ex_intro2 C (\lambda (e2: C).(csuba g (CHead c3 (Bind b) u) e2)) (\lambda 
(e2: C).(clear (CHead c4 (Bind b) u) e2)) (CHead c4 (Bind b) u) (csuba_head g 
c3 c4 H0 (Bind b) u) (clear_bind b c4 u)) e1 (clear_gen_bind b c3 e1 u H3)))) 
(\lambda (f: F).(\lambda (H3: (clear (CHead c3 (Flat f) u) e1)).(let H4 \def 
(H1 e1 (clear_gen_flat f c3 e1 u H3)) in (ex2_ind C (\lambda (e2: C).(csuba g 
e1 e2)) (\lambda (e2: C).(clear c4 e2)) (ex2 C (\lambda (e2: C).(csuba g e1 
e2)) (\lambda (e2: C).(clear (CHead c4 (Flat f) u) e2))) (\lambda (x: 
C).(\lambda (H5: (csuba g e1 x)).(\lambda (H6: (clear c4 x)).(ex_intro2 C 
(\lambda (e2: C).(csuba g e1 e2)) (\lambda (e2: C).(clear (CHead c4 (Flat f) 
u) e2)) x H5 (clear_flat c4 x H6 f u))))) H4)))) k H2))))))))) (\lambda (c3: 
C).(\lambda (c4: C).(\lambda (H0: (csuba g c3 c4)).(\lambda (_: ((\forall 
(e1: C).((clear c3 e1) \to (ex2 C (\lambda (e2: C).(csuba g e1 e2)) (\lambda 
(e2: C).(clear c4 e2))))))).(\lambda (b: B).(\lambda (H2: (not (eq B b 
Void))).(\lambda (u1: T).(\lambda (u2: T).(\lambda (e1: C).(\lambda (H3: 
(clear (CHead c3 (Bind Void) u1) e1)).(eq_ind_r C (CHead c3 (Bind Void) u1) 
(\lambda (c: C).(ex2 C (\lambda (e2: C).(csuba g c e2)) (\lambda (e2: 
C).(clear (CHead c4 (Bind b) u2) e2)))) (ex_intro2 C (\lambda (e2: C).(csuba 
g (CHead c3 (Bind Void) u1) e2)) (\lambda (e2: C).(clear (CHead c4 (Bind b) 
u2) e2)) (CHead c4 (Bind b) u2) (csuba_void g c3 c4 H0 b H2 u1 u2) 
(clear_bind b c4 u2)) e1 (clear_gen_bind Void c3 e1 u1 H3)))))))))))) 
(\lambda (c3: C).(\lambda (c4: C).(\lambda (H0: (csuba g c3 c4)).(\lambda (_: 
((\forall (e1: C).((clear c3 e1) \to (ex2 C (\lambda (e2: C).(csuba g e1 e2)) 
(\lambda (e2: C).(clear c4 e2))))))).(\lambda (t: T).(\lambda (a: A).(\lambda 
(H2: (arity g c3 t (asucc g a))).(\lambda (u: T).(\lambda (H3: (arity g c4 u 
a)).(\lambda (e1: C).(\lambda (H4: (clear (CHead c3 (Bind Abst) t) 
e1)).(eq_ind_r C (CHead c3 (Bind Abst) t) (\lambda (c: C).(ex2 C (\lambda 
(e2: C).(csuba g c e2)) (\lambda (e2: C).(clear (CHead c4 (Bind Abbr) u) 
e2)))) (ex_intro2 C (\lambda (e2: C).(csuba g (CHead c3 (Bind Abst) t) e2)) 
(\lambda (e2: C).(clear (CHead c4 (Bind Abbr) u) e2)) (CHead c4 (Bind Abbr) 
u) (csuba_abst g c3 c4 H0 t a H2 u H3) (clear_bind Abbr c4 u)) e1 
(clear_gen_bind Abst c3 e1 t H4))))))))))))) c1 c2 H)))).
(* COMMENTS
Initial nodes: 937
END *)

theorem csuba_clear_trans:
 \forall (g: G).(\forall (c1: C).(\forall (c2: C).((csuba g c2 c1) \to 
(\forall (e1: C).((clear c1 e1) \to (ex2 C (\lambda (e2: C).(csuba g e2 e1)) 
(\lambda (e2: C).(clear c2 e2))))))))
\def
 \lambda (g: G).(\lambda (c1: C).(\lambda (c2: C).(\lambda (H: (csuba g c2 
c1)).(csuba_ind g (\lambda (c: C).(\lambda (c0: C).(\forall (e1: C).((clear 
c0 e1) \to (ex2 C (\lambda (e2: C).(csuba g e2 e1)) (\lambda (e2: C).(clear c 
e2))))))) (\lambda (n: nat).(\lambda (e1: C).(\lambda (H0: (clear (CSort n) 
e1)).(clear_gen_sort e1 n H0 (ex2 C (\lambda (e2: C).(csuba g e2 e1)) 
(\lambda (e2: C).(clear (CSort n) e2))))))) (\lambda (c3: C).(\lambda (c4: 
C).(\lambda (H0: (csuba g c3 c4)).(\lambda (H1: ((\forall (e1: C).((clear c4 
e1) \to (ex2 C (\lambda (e2: C).(csuba g e2 e1)) (\lambda (e2: C).(clear c3 
e2))))))).(\lambda (k: K).(\lambda (u: T).(\lambda (e1: C).(\lambda (H2: 
(clear (CHead c4 k u) e1)).(K_ind (\lambda (k0: K).((clear (CHead c4 k0 u) 
e1) \to (ex2 C (\lambda (e2: C).(csuba g e2 e1)) (\lambda (e2: C).(clear 
(CHead c3 k0 u) e2))))) (\lambda (b: B).(\lambda (H3: (clear (CHead c4 (Bind 
b) u) e1)).(eq_ind_r C (CHead c4 (Bind b) u) (\lambda (c: C).(ex2 C (\lambda 
(e2: C).(csuba g e2 c)) (\lambda (e2: C).(clear (CHead c3 (Bind b) u) e2)))) 
(ex_intro2 C (\lambda (e2: C).(csuba g e2 (CHead c4 (Bind b) u))) (\lambda 
(e2: C).(clear (CHead c3 (Bind b) u) e2)) (CHead c3 (Bind b) u) (csuba_head g 
c3 c4 H0 (Bind b) u) (clear_bind b c3 u)) e1 (clear_gen_bind b c4 e1 u H3)))) 
(\lambda (f: F).(\lambda (H3: (clear (CHead c4 (Flat f) u) e1)).(let H4 \def 
(H1 e1 (clear_gen_flat f c4 e1 u H3)) in (ex2_ind C (\lambda (e2: C).(csuba g 
e2 e1)) (\lambda (e2: C).(clear c3 e2)) (ex2 C (\lambda (e2: C).(csuba g e2 
e1)) (\lambda (e2: C).(clear (CHead c3 (Flat f) u) e2))) (\lambda (x: 
C).(\lambda (H5: (csuba g x e1)).(\lambda (H6: (clear c3 x)).(ex_intro2 C 
(\lambda (e2: C).(csuba g e2 e1)) (\lambda (e2: C).(clear (CHead c3 (Flat f) 
u) e2)) x H5 (clear_flat c3 x H6 f u))))) H4)))) k H2))))))))) (\lambda (c3: 
C).(\lambda (c4: C).(\lambda (H0: (csuba g c3 c4)).(\lambda (_: ((\forall 
(e1: C).((clear c4 e1) \to (ex2 C (\lambda (e2: C).(csuba g e2 e1)) (\lambda 
(e2: C).(clear c3 e2))))))).(\lambda (b: B).(\lambda (H2: (not (eq B b 
Void))).(\lambda (u1: T).(\lambda (u2: T).(\lambda (e1: C).(\lambda (H3: 
(clear (CHead c4 (Bind b) u2) e1)).(eq_ind_r C (CHead c4 (Bind b) u2) 
(\lambda (c: C).(ex2 C (\lambda (e2: C).(csuba g e2 c)) (\lambda (e2: 
C).(clear (CHead c3 (Bind Void) u1) e2)))) (ex_intro2 C (\lambda (e2: 
C).(csuba g e2 (CHead c4 (Bind b) u2))) (\lambda (e2: C).(clear (CHead c3 
(Bind Void) u1) e2)) (CHead c3 (Bind Void) u1) (csuba_void g c3 c4 H0 b H2 u1 
u2) (clear_bind Void c3 u1)) e1 (clear_gen_bind b c4 e1 u2 H3)))))))))))) 
(\lambda (c3: C).(\lambda (c4: C).(\lambda (H0: (csuba g c3 c4)).(\lambda (_: 
((\forall (e1: C).((clear c4 e1) \to (ex2 C (\lambda (e2: C).(csuba g e2 e1)) 
(\lambda (e2: C).(clear c3 e2))))))).(\lambda (t: T).(\lambda (a: A).(\lambda 
(H2: (arity g c3 t (asucc g a))).(\lambda (u: T).(\lambda (H3: (arity g c4 u 
a)).(\lambda (e1: C).(\lambda (H4: (clear (CHead c4 (Bind Abbr) u) 
e1)).(eq_ind_r C (CHead c4 (Bind Abbr) u) (\lambda (c: C).(ex2 C (\lambda 
(e2: C).(csuba g e2 c)) (\lambda (e2: C).(clear (CHead c3 (Bind Abst) t) 
e2)))) (ex_intro2 C (\lambda (e2: C).(csuba g e2 (CHead c4 (Bind Abbr) u))) 
(\lambda (e2: C).(clear (CHead c3 (Bind Abst) t) e2)) (CHead c3 (Bind Abst) 
t) (csuba_abst g c3 c4 H0 t a H2 u H3) (clear_bind Abst c3 t)) e1 
(clear_gen_bind Abbr c4 e1 u H4))))))))))))) c2 c1 H)))).
(* COMMENTS
Initial nodes: 937
END *)

