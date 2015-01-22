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

include "Basic-1/csubst1/defs.ma".

include "Basic-1/subst1/defs.ma".

theorem csubst1_head:
 \forall (k: K).(\forall (i: nat).(\forall (v: T).(\forall (u1: T).(\forall 
(u2: T).((subst1 i v u1 u2) \to (\forall (c1: C).(\forall (c2: C).((csubst1 i 
v c1 c2) \to (csubst1 (s k i) v (CHead c1 k u1) (CHead c2 k u2))))))))))
\def
 \lambda (k: K).(\lambda (i: nat).(\lambda (v: T).(\lambda (u1: T).(\lambda 
(u2: T).(\lambda (H: (subst1 i v u1 u2)).(subst1_ind i v u1 (\lambda (t: 
T).(\forall (c1: C).(\forall (c2: C).((csubst1 i v c1 c2) \to (csubst1 (s k 
i) v (CHead c1 k u1) (CHead c2 k t)))))) (\lambda (c1: C).(\lambda (c2: 
C).(\lambda (H0: (csubst1 i v c1 c2)).(csubst1_ind i v c1 (\lambda (c: 
C).(csubst1 (s k i) v (CHead c1 k u1) (CHead c k u1))) (csubst1_refl (s k i) 
v (CHead c1 k u1)) (\lambda (c3: C).(\lambda (H1: (csubst0 i v c1 
c3)).(csubst1_sing (s k i) v (CHead c1 k u1) (CHead c3 k u1) (csubst0_fst k i 
c1 c3 v H1 u1)))) c2 H0)))) (\lambda (t2: T).(\lambda (H0: (subst0 i v u1 
t2)).(\lambda (c1: C).(\lambda (c2: C).(\lambda (H1: (csubst1 i v c1 
c2)).(csubst1_ind i v c1 (\lambda (c: C).(csubst1 (s k i) v (CHead c1 k u1) 
(CHead c k t2))) (csubst1_sing (s k i) v (CHead c1 k u1) (CHead c1 k t2) 
(csubst0_snd k i v u1 t2 H0 c1)) (\lambda (c3: C).(\lambda (H2: (csubst0 i v 
c1 c3)).(csubst1_sing (s k i) v (CHead c1 k u1) (CHead c3 k t2) (csubst0_both 
k i v u1 t2 H0 c1 c3 H2)))) c2 H1)))))) u2 H)))))).
(* COMMENTS
Initial nodes: 365
END *)

theorem csubst1_bind:
 \forall (b: B).(\forall (i: nat).(\forall (v: T).(\forall (u1: T).(\forall 
(u2: T).((subst1 i v u1 u2) \to (\forall (c1: C).(\forall (c2: C).((csubst1 i 
v c1 c2) \to (csubst1 (S i) v (CHead c1 (Bind b) u1) (CHead c2 (Bind b) 
u2))))))))))
\def
 \lambda (b: B).(\lambda (i: nat).(\lambda (v: T).(\lambda (u1: T).(\lambda 
(u2: T).(\lambda (H: (subst1 i v u1 u2)).(\lambda (c1: C).(\lambda (c2: 
C).(\lambda (H0: (csubst1 i v c1 c2)).(eq_ind nat (s (Bind b) i) (\lambda (n: 
nat).(csubst1 n v (CHead c1 (Bind b) u1) (CHead c2 (Bind b) u2))) 
(csubst1_head (Bind b) i v u1 u2 H c1 c2 H0) (S i) (refl_equal nat (S 
i))))))))))).
(* COMMENTS
Initial nodes: 107
END *)

theorem csubst1_flat:
 \forall (f: F).(\forall (i: nat).(\forall (v: T).(\forall (u1: T).(\forall 
(u2: T).((subst1 i v u1 u2) \to (\forall (c1: C).(\forall (c2: C).((csubst1 i 
v c1 c2) \to (csubst1 i v (CHead c1 (Flat f) u1) (CHead c2 (Flat f) 
u2))))))))))
\def
 \lambda (f: F).(\lambda (i: nat).(\lambda (v: T).(\lambda (u1: T).(\lambda 
(u2: T).(\lambda (H: (subst1 i v u1 u2)).(\lambda (c1: C).(\lambda (c2: 
C).(\lambda (H0: (csubst1 i v c1 c2)).(eq_ind nat (s (Flat f) i) (\lambda (n: 
nat).(csubst1 n v (CHead c1 (Flat f) u1) (CHead c2 (Flat f) u2))) 
(csubst1_head (Flat f) i v u1 u2 H c1 c2 H0) i (refl_equal nat i)))))))))).
(* COMMENTS
Initial nodes: 103
END *)

