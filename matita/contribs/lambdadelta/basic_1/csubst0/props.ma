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

include "Basic-1/csubst0/defs.ma".

theorem csubst0_snd_bind:
 \forall (b: B).(\forall (i: nat).(\forall (v: T).(\forall (u1: T).(\forall 
(u2: T).((subst0 i v u1 u2) \to (\forall (c: C).(csubst0 (S i) v (CHead c 
(Bind b) u1) (CHead c (Bind b) u2))))))))
\def
 \lambda (b: B).(\lambda (i: nat).(\lambda (v: T).(\lambda (u1: T).(\lambda 
(u2: T).(\lambda (H: (subst0 i v u1 u2)).(\lambda (c: C).(eq_ind nat (s (Bind 
b) i) (\lambda (n: nat).(csubst0 n v (CHead c (Bind b) u1) (CHead c (Bind b) 
u2))) (csubst0_snd (Bind b) i v u1 u2 H c) (S i) (refl_equal nat (S 
i))))))))).
(* COMMENTS
Initial nodes: 91
END *)

theorem csubst0_fst_bind:
 \forall (b: B).(\forall (i: nat).(\forall (c1: C).(\forall (c2: C).(\forall 
(v: T).((csubst0 i v c1 c2) \to (\forall (u: T).(csubst0 (S i) v (CHead c1 
(Bind b) u) (CHead c2 (Bind b) u))))))))
\def
 \lambda (b: B).(\lambda (i: nat).(\lambda (c1: C).(\lambda (c2: C).(\lambda 
(v: T).(\lambda (H: (csubst0 i v c1 c2)).(\lambda (u: T).(eq_ind nat (s (Bind 
b) i) (\lambda (n: nat).(csubst0 n v (CHead c1 (Bind b) u) (CHead c2 (Bind b) 
u))) (csubst0_fst (Bind b) i c1 c2 v H u) (S i) (refl_equal nat (S i))))))))).
(* COMMENTS
Initial nodes: 91
END *)

theorem csubst0_both_bind:
 \forall (b: B).(\forall (i: nat).(\forall (v: T).(\forall (u1: T).(\forall 
(u2: T).((subst0 i v u1 u2) \to (\forall (c1: C).(\forall (c2: C).((csubst0 i 
v c1 c2) \to (csubst0 (S i) v (CHead c1 (Bind b) u1) (CHead c2 (Bind b) 
u2))))))))))
\def
 \lambda (b: B).(\lambda (i: nat).(\lambda (v: T).(\lambda (u1: T).(\lambda 
(u2: T).(\lambda (H: (subst0 i v u1 u2)).(\lambda (c1: C).(\lambda (c2: 
C).(\lambda (H0: (csubst0 i v c1 c2)).(eq_ind nat (s (Bind b) i) (\lambda (n: 
nat).(csubst0 n v (CHead c1 (Bind b) u1) (CHead c2 (Bind b) u2))) 
(csubst0_both (Bind b) i v u1 u2 H c1 c2 H0) (S i) (refl_equal nat (S 
i))))))))))).
(* COMMENTS
Initial nodes: 107
END *)

