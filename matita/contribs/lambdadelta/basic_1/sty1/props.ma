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

include "Basic-1/sty1/defs.ma".

include "Basic-1/sty0/props.ma".

theorem sty1_trans:
 \forall (g: G).(\forall (c: C).(\forall (t1: T).(\forall (t: T).((sty1 g c 
t1 t) \to (\forall (t2: T).((sty1 g c t t2) \to (sty1 g c t1 t2)))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (t1: T).(\lambda (t: T).(\lambda (H: 
(sty1 g c t1 t)).(\lambda (t2: T).(\lambda (H0: (sty1 g c t t2)).(sty1_ind g 
c t (\lambda (t0: T).(sty1 g c t1 t0)) (\lambda (t3: T).(\lambda (H1: (sty0 g 
c t t3)).(sty1_sing g c t1 t H t3 H1))) (\lambda (t0: T).(\lambda (_: (sty1 g 
c t t0)).(\lambda (H2: (sty1 g c t1 t0)).(\lambda (t3: T).(\lambda (H3: (sty0 
g c t0 t3)).(sty1_sing g c t1 t0 H2 t3 H3)))))) t2 H0))))))).
(* COMMENTS
Initial nodes: 131
END *)

theorem sty1_bind:
 \forall (g: G).(\forall (b: B).(\forall (c: C).(\forall (v: T).(\forall (t1: 
T).(\forall (t2: T).((sty1 g (CHead c (Bind b) v) t1 t2) \to (sty1 g c (THead 
(Bind b) v t1) (THead (Bind b) v t2))))))))
\def
 \lambda (g: G).(\lambda (b: B).(\lambda (c: C).(\lambda (v: T).(\lambda (t1: 
T).(\lambda (t2: T).(\lambda (H: (sty1 g (CHead c (Bind b) v) t1 
t2)).(sty1_ind g (CHead c (Bind b) v) t1 (\lambda (t: T).(sty1 g c (THead 
(Bind b) v t1) (THead (Bind b) v t))) (\lambda (t3: T).(\lambda (H0: (sty0 g 
(CHead c (Bind b) v) t1 t3)).(sty1_sty0 g c (THead (Bind b) v t1) (THead 
(Bind b) v t3) (sty0_bind g b c v t1 t3 H0)))) (\lambda (t: T).(\lambda (_: 
(sty1 g (CHead c (Bind b) v) t1 t)).(\lambda (H1: (sty1 g c (THead (Bind b) v 
t1) (THead (Bind b) v t))).(\lambda (t3: T).(\lambda (H2: (sty0 g (CHead c 
(Bind b) v) t t3)).(sty1_sing g c (THead (Bind b) v t1) (THead (Bind b) v t) 
H1 (THead (Bind b) v t3) (sty0_bind g b c v t t3 H2))))))) t2 H))))))).
(* COMMENTS
Initial nodes: 259
END *)

theorem sty1_appl:
 \forall (g: G).(\forall (c: C).(\forall (v: T).(\forall (t1: T).(\forall 
(t2: T).((sty1 g c t1 t2) \to (sty1 g c (THead (Flat Appl) v t1) (THead (Flat 
Appl) v t2)))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (v: T).(\lambda (t1: T).(\lambda 
(t2: T).(\lambda (H: (sty1 g c t1 t2)).(sty1_ind g c t1 (\lambda (t: T).(sty1 
g c (THead (Flat Appl) v t1) (THead (Flat Appl) v t))) (\lambda (t3: 
T).(\lambda (H0: (sty0 g c t1 t3)).(sty1_sty0 g c (THead (Flat Appl) v t1) 
(THead (Flat Appl) v t3) (sty0_appl g c v t1 t3 H0)))) (\lambda (t: 
T).(\lambda (_: (sty1 g c t1 t)).(\lambda (H1: (sty1 g c (THead (Flat Appl) v 
t1) (THead (Flat Appl) v t))).(\lambda (t3: T).(\lambda (H2: (sty0 g c t 
t3)).(sty1_sing g c (THead (Flat Appl) v t1) (THead (Flat Appl) v t) H1 
(THead (Flat Appl) v t3) (sty0_appl g c v t t3 H2))))))) t2 H)))))).
(* COMMENTS
Initial nodes: 213
END *)

theorem sty1_lift:
 \forall (g: G).(\forall (e: C).(\forall (t1: T).(\forall (t2: T).((sty1 g e 
t1 t2) \to (\forall (c: C).(\forall (h: nat).(\forall (d: nat).((drop h d c 
e) \to (sty1 g c (lift h d t1) (lift h d t2))))))))))
\def
 \lambda (g: G).(\lambda (e: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda 
(H: (sty1 g e t1 t2)).(sty1_ind g e t1 (\lambda (t: T).(\forall (c: 
C).(\forall (h: nat).(\forall (d: nat).((drop h d c e) \to (sty1 g c (lift h 
d t1) (lift h d t))))))) (\lambda (t3: T).(\lambda (H0: (sty0 g e t1 
t3)).(\lambda (c: C).(\lambda (h: nat).(\lambda (d: nat).(\lambda (H1: (drop 
h d c e)).(sty1_sty0 g c (lift h d t1) (lift h d t3) (sty0_lift g e t1 t3 H0 
c h d H1)))))))) (\lambda (t: T).(\lambda (_: (sty1 g e t1 t)).(\lambda (H1: 
((\forall (c: C).(\forall (h: nat).(\forall (d: nat).((drop h d c e) \to 
(sty1 g c (lift h d t1) (lift h d t)))))))).(\lambda (t3: T).(\lambda (H2: 
(sty0 g e t t3)).(\lambda (c: C).(\lambda (h: nat).(\lambda (d: nat).(\lambda 
(H3: (drop h d c e)).(sty1_sing g c (lift h d t1) (lift h d t) (H1 c h d H3) 
(lift h d t3) (sty0_lift g e t t3 H2 c h d H3))))))))))) t2 H))))).
(* COMMENTS
Initial nodes: 277
END *)

theorem sty1_correct:
 \forall (g: G).(\forall (c: C).(\forall (t1: T).(\forall (t: T).((sty1 g c 
t1 t) \to (ex T (\lambda (t2: T).(sty0 g c t t2)))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (t1: T).(\lambda (t: T).(\lambda (H: 
(sty1 g c t1 t)).(sty1_ind g c t1 (\lambda (t0: T).(ex T (\lambda (t2: 
T).(sty0 g c t0 t2)))) (\lambda (t2: T).(\lambda (H0: (sty0 g c t1 
t2)).(sty0_correct g c t1 t2 H0))) (\lambda (t0: T).(\lambda (_: (sty1 g c t1 
t0)).(\lambda (_: (ex T (\lambda (t2: T).(sty0 g c t0 t2)))).(\lambda (t2: 
T).(\lambda (H2: (sty0 g c t0 t2)).(sty0_correct g c t0 t2 H2)))))) t H))))).
(* COMMENTS
Initial nodes: 123
END *)

theorem sty1_abbr:
 \forall (g: G).(\forall (c: C).(\forall (d: C).(\forall (v: T).(\forall (i: 
nat).((getl i c (CHead d (Bind Abbr) v)) \to (\forall (w: T).((sty1 g d v w) 
\to (sty1 g c (TLRef i) (lift (S i) O w)))))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (d: C).(\lambda (v: T).(\lambda (i: 
nat).(\lambda (H: (getl i c (CHead d (Bind Abbr) v))).(\lambda (w: 
T).(\lambda (H0: (sty1 g d v w)).(sty1_ind g d v (\lambda (t: T).(sty1 g c 
(TLRef i) (lift (S i) O t))) (\lambda (t2: T).(\lambda (H1: (sty0 g d v 
t2)).(sty1_sty0 g c (TLRef i) (lift (S i) O t2) (sty0_abbr g c d v i H t2 
H1)))) (\lambda (t: T).(\lambda (_: (sty1 g d v t)).(\lambda (H2: (sty1 g c 
(TLRef i) (lift (S i) O t))).(\lambda (t2: T).(\lambda (H3: (sty0 g d t 
t2)).(sty1_sing g c (TLRef i) (lift (S i) O t) H2 (lift (S i) O t2) 
(sty0_lift g d t t2 H3 c (S i) O (getl_drop Abbr c d v i H)))))))) w 
H0)))))))).
(* COMMENTS
Initial nodes: 231
END *)

theorem sty1_cast2:
 \forall (g: G).(\forall (c: C).(\forall (t1: T).(\forall (t2: T).((sty1 g c 
t1 t2) \to (\forall (v1: T).(\forall (v2: T).((sty0 g c v1 v2) \to (ex2 T 
(\lambda (v3: T).(sty1 g c v1 v3)) (\lambda (v3: T).(sty1 g c (THead (Flat 
Cast) v1 t1) (THead (Flat Cast) v3 t2)))))))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda 
(H: (sty1 g c t1 t2)).(sty1_ind g c t1 (\lambda (t: T).(\forall (v1: 
T).(\forall (v2: T).((sty0 g c v1 v2) \to (ex2 T (\lambda (v3: T).(sty1 g c 
v1 v3)) (\lambda (v3: T).(sty1 g c (THead (Flat Cast) v1 t1) (THead (Flat 
Cast) v3 t)))))))) (\lambda (t3: T).(\lambda (H0: (sty0 g c t1 t3)).(\lambda 
(v1: T).(\lambda (v2: T).(\lambda (H1: (sty0 g c v1 v2)).(ex_intro2 T 
(\lambda (v3: T).(sty1 g c v1 v3)) (\lambda (v3: T).(sty1 g c (THead (Flat 
Cast) v1 t1) (THead (Flat Cast) v3 t3))) v2 (sty1_sty0 g c v1 v2 H1) 
(sty1_sty0 g c (THead (Flat Cast) v1 t1) (THead (Flat Cast) v2 t3) (sty0_cast 
g c v1 v2 H1 t1 t3 H0)))))))) (\lambda (t: T).(\lambda (_: (sty1 g c t1 
t)).(\lambda (H1: ((\forall (v1: T).(\forall (v2: T).((sty0 g c v1 v2) \to 
(ex2 T (\lambda (v3: T).(sty1 g c v1 v3)) (\lambda (v3: T).(sty1 g c (THead 
(Flat Cast) v1 t1) (THead (Flat Cast) v3 t))))))))).(\lambda (t3: T).(\lambda 
(H2: (sty0 g c t t3)).(\lambda (v1: T).(\lambda (v2: T).(\lambda (H3: (sty0 g 
c v1 v2)).(let H_x \def (H1 v1 v2 H3) in (let H4 \def H_x in (ex2_ind T 
(\lambda (v3: T).(sty1 g c v1 v3)) (\lambda (v3: T).(sty1 g c (THead (Flat 
Cast) v1 t1) (THead (Flat Cast) v3 t))) (ex2 T (\lambda (v3: T).(sty1 g c v1 
v3)) (\lambda (v3: T).(sty1 g c (THead (Flat Cast) v1 t1) (THead (Flat Cast) 
v3 t3)))) (\lambda (x: T).(\lambda (H5: (sty1 g c v1 x)).(\lambda (H6: (sty1 
g c (THead (Flat Cast) v1 t1) (THead (Flat Cast) x t))).(let H_x0 \def 
(sty1_correct g c v1 x H5) in (let H7 \def H_x0 in (ex_ind T (\lambda (t4: 
T).(sty0 g c x t4)) (ex2 T (\lambda (v3: T).(sty1 g c v1 v3)) (\lambda (v3: 
T).(sty1 g c (THead (Flat Cast) v1 t1) (THead (Flat Cast) v3 t3)))) (\lambda 
(x0: T).(\lambda (H8: (sty0 g c x x0)).(ex_intro2 T (\lambda (v3: T).(sty1 g 
c v1 v3)) (\lambda (v3: T).(sty1 g c (THead (Flat Cast) v1 t1) (THead (Flat 
Cast) v3 t3))) x0 (sty1_sing g c v1 x H5 x0 H8) (sty1_sing g c (THead (Flat 
Cast) v1 t1) (THead (Flat Cast) x t) H6 (THead (Flat Cast) x0 t3) (sty0_cast 
g c x x0 H8 t t3 H2))))) H7)))))) H4))))))))))) t2 H))))).
(* COMMENTS
Initial nodes: 657
END *)

