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

include "Basic-1/csubst0/fwd.ma".

include "Basic-1/subst1/props.ma".

theorem csubst1_gen_head:
 \forall (k: K).(\forall (c1: C).(\forall (x: C).(\forall (u1: T).(\forall 
(v: T).(\forall (i: nat).((csubst1 (s k i) v (CHead c1 k u1) x) \to (ex3_2 T 
C (\lambda (u2: T).(\lambda (c2: C).(eq C x (CHead c2 k u2)))) (\lambda (u2: 
T).(\lambda (_: C).(subst1 i v u1 u2))) (\lambda (_: T).(\lambda (c2: 
C).(csubst1 i v c1 c2))))))))))
\def
 \lambda (k: K).(\lambda (c1: C).(\lambda (x: C).(\lambda (u1: T).(\lambda 
(v: T).(\lambda (i: nat).(\lambda (H: (csubst1 (s k i) v (CHead c1 k u1) 
x)).(csubst1_ind (s k i) v (CHead c1 k u1) (\lambda (c: C).(ex3_2 T C 
(\lambda (u2: T).(\lambda (c2: C).(eq C c (CHead c2 k u2)))) (\lambda (u2: 
T).(\lambda (_: C).(subst1 i v u1 u2))) (\lambda (_: T).(\lambda (c2: 
C).(csubst1 i v c1 c2))))) (ex3_2_intro T C (\lambda (u2: T).(\lambda (c2: 
C).(eq C (CHead c1 k u1) (CHead c2 k u2)))) (\lambda (u2: T).(\lambda (_: 
C).(subst1 i v u1 u2))) (\lambda (_: T).(\lambda (c2: C).(csubst1 i v c1 
c2))) u1 c1 (refl_equal C (CHead c1 k u1)) (subst1_refl i v u1) (csubst1_refl 
i v c1)) (\lambda (c2: C).(\lambda (H0: (csubst0 (s k i) v (CHead c1 k u1) 
c2)).(or3_ind (ex3_2 T nat (\lambda (_: T).(\lambda (j: nat).(eq nat (s k i) 
(s k j)))) (\lambda (u2: T).(\lambda (_: nat).(eq C c2 (CHead c1 k u2)))) 
(\lambda (u2: T).(\lambda (j: nat).(subst0 j v u1 u2)))) (ex3_2 C nat 
(\lambda (_: C).(\lambda (j: nat).(eq nat (s k i) (s k j)))) (\lambda (c3: 
C).(\lambda (_: nat).(eq C c2 (CHead c3 k u1)))) (\lambda (c3: C).(\lambda 
(j: nat).(csubst0 j v c1 c3)))) (ex4_3 T C nat (\lambda (_: T).(\lambda (_: 
C).(\lambda (j: nat).(eq nat (s k i) (s k j))))) (\lambda (u2: T).(\lambda 
(c3: C).(\lambda (_: nat).(eq C c2 (CHead c3 k u2))))) (\lambda (u2: 
T).(\lambda (_: C).(\lambda (j: nat).(subst0 j v u1 u2)))) (\lambda (_: 
T).(\lambda (c3: C).(\lambda (j: nat).(csubst0 j v c1 c3))))) (ex3_2 T C 
(\lambda (u2: T).(\lambda (c3: C).(eq C c2 (CHead c3 k u2)))) (\lambda (u2: 
T).(\lambda (_: C).(subst1 i v u1 u2))) (\lambda (_: T).(\lambda (c3: 
C).(csubst1 i v c1 c3)))) (\lambda (H1: (ex3_2 T nat (\lambda (_: T).(\lambda 
(j: nat).(eq nat (s k i) (s k j)))) (\lambda (u2: T).(\lambda (_: nat).(eq C 
c2 (CHead c1 k u2)))) (\lambda (u2: T).(\lambda (j: nat).(subst0 j v u1 
u2))))).(ex3_2_ind T nat (\lambda (_: T).(\lambda (j: nat).(eq nat (s k i) (s 
k j)))) (\lambda (u2: T).(\lambda (_: nat).(eq C c2 (CHead c1 k u2)))) 
(\lambda (u2: T).(\lambda (j: nat).(subst0 j v u1 u2))) (ex3_2 T C (\lambda 
(u2: T).(\lambda (c3: C).(eq C c2 (CHead c3 k u2)))) (\lambda (u2: 
T).(\lambda (_: C).(subst1 i v u1 u2))) (\lambda (_: T).(\lambda (c3: 
C).(csubst1 i v c1 c3)))) (\lambda (x0: T).(\lambda (x1: nat).(\lambda (H2: 
(eq nat (s k i) (s k x1))).(\lambda (H3: (eq C c2 (CHead c1 k x0))).(\lambda 
(H4: (subst0 x1 v u1 x0)).(eq_ind_r C (CHead c1 k x0) (\lambda (c: C).(ex3_2 
T C (\lambda (u2: T).(\lambda (c3: C).(eq C c (CHead c3 k u2)))) (\lambda 
(u2: T).(\lambda (_: C).(subst1 i v u1 u2))) (\lambda (_: T).(\lambda (c3: 
C).(csubst1 i v c1 c3))))) (let H5 \def (eq_ind_r nat x1 (\lambda (n: 
nat).(subst0 n v u1 x0)) H4 i (s_inj k i x1 H2)) in (ex3_2_intro T C (\lambda 
(u2: T).(\lambda (c3: C).(eq C (CHead c1 k x0) (CHead c3 k u2)))) (\lambda 
(u2: T).(\lambda (_: C).(subst1 i v u1 u2))) (\lambda (_: T).(\lambda (c3: 
C).(csubst1 i v c1 c3))) x0 c1 (refl_equal C (CHead c1 k x0)) (subst1_single 
i v u1 x0 H5) (csubst1_refl i v c1))) c2 H3)))))) H1)) (\lambda (H1: (ex3_2 C 
nat (\lambda (_: C).(\lambda (j: nat).(eq nat (s k i) (s k j)))) (\lambda 
(c3: C).(\lambda (_: nat).(eq C c2 (CHead c3 k u1)))) (\lambda (c3: 
C).(\lambda (j: nat).(csubst0 j v c1 c3))))).(ex3_2_ind C nat (\lambda (_: 
C).(\lambda (j: nat).(eq nat (s k i) (s k j)))) (\lambda (c3: C).(\lambda (_: 
nat).(eq C c2 (CHead c3 k u1)))) (\lambda (c3: C).(\lambda (j: nat).(csubst0 
j v c1 c3))) (ex3_2 T C (\lambda (u2: T).(\lambda (c3: C).(eq C c2 (CHead c3 
k u2)))) (\lambda (u2: T).(\lambda (_: C).(subst1 i v u1 u2))) (\lambda (_: 
T).(\lambda (c3: C).(csubst1 i v c1 c3)))) (\lambda (x0: C).(\lambda (x1: 
nat).(\lambda (H2: (eq nat (s k i) (s k x1))).(\lambda (H3: (eq C c2 (CHead 
x0 k u1))).(\lambda (H4: (csubst0 x1 v c1 x0)).(eq_ind_r C (CHead x0 k u1) 
(\lambda (c: C).(ex3_2 T C (\lambda (u2: T).(\lambda (c3: C).(eq C c (CHead 
c3 k u2)))) (\lambda (u2: T).(\lambda (_: C).(subst1 i v u1 u2))) (\lambda 
(_: T).(\lambda (c3: C).(csubst1 i v c1 c3))))) (let H5 \def (eq_ind_r nat x1 
(\lambda (n: nat).(csubst0 n v c1 x0)) H4 i (s_inj k i x1 H2)) in 
(ex3_2_intro T C (\lambda (u2: T).(\lambda (c3: C).(eq C (CHead x0 k u1) 
(CHead c3 k u2)))) (\lambda (u2: T).(\lambda (_: C).(subst1 i v u1 u2))) 
(\lambda (_: T).(\lambda (c3: C).(csubst1 i v c1 c3))) u1 x0 (refl_equal C 
(CHead x0 k u1)) (subst1_refl i v u1) (csubst1_sing i v c1 x0 H5))) c2 
H3)))))) H1)) (\lambda (H1: (ex4_3 T C nat (\lambda (_: T).(\lambda (_: 
C).(\lambda (j: nat).(eq nat (s k i) (s k j))))) (\lambda (u2: T).(\lambda 
(c3: C).(\lambda (_: nat).(eq C c2 (CHead c3 k u2))))) (\lambda (u2: 
T).(\lambda (_: C).(\lambda (j: nat).(subst0 j v u1 u2)))) (\lambda (_: 
T).(\lambda (c3: C).(\lambda (j: nat).(csubst0 j v c1 c3)))))).(ex4_3_ind T C 
nat (\lambda (_: T).(\lambda (_: C).(\lambda (j: nat).(eq nat (s k i) (s k 
j))))) (\lambda (u2: T).(\lambda (c3: C).(\lambda (_: nat).(eq C c2 (CHead c3 
k u2))))) (\lambda (u2: T).(\lambda (_: C).(\lambda (j: nat).(subst0 j v u1 
u2)))) (\lambda (_: T).(\lambda (c3: C).(\lambda (j: nat).(csubst0 j v c1 
c3)))) (ex3_2 T C (\lambda (u2: T).(\lambda (c3: C).(eq C c2 (CHead c3 k 
u2)))) (\lambda (u2: T).(\lambda (_: C).(subst1 i v u1 u2))) (\lambda (_: 
T).(\lambda (c3: C).(csubst1 i v c1 c3)))) (\lambda (x0: T).(\lambda (x1: 
C).(\lambda (x2: nat).(\lambda (H2: (eq nat (s k i) (s k x2))).(\lambda (H3: 
(eq C c2 (CHead x1 k x0))).(\lambda (H4: (subst0 x2 v u1 x0)).(\lambda (H5: 
(csubst0 x2 v c1 x1)).(eq_ind_r C (CHead x1 k x0) (\lambda (c: C).(ex3_2 T C 
(\lambda (u2: T).(\lambda (c3: C).(eq C c (CHead c3 k u2)))) (\lambda (u2: 
T).(\lambda (_: C).(subst1 i v u1 u2))) (\lambda (_: T).(\lambda (c3: 
C).(csubst1 i v c1 c3))))) (let H6 \def (eq_ind_r nat x2 (\lambda (n: 
nat).(csubst0 n v c1 x1)) H5 i (s_inj k i x2 H2)) in (let H7 \def (eq_ind_r 
nat x2 (\lambda (n: nat).(subst0 n v u1 x0)) H4 i (s_inj k i x2 H2)) in 
(ex3_2_intro T C (\lambda (u2: T).(\lambda (c3: C).(eq C (CHead x1 k x0) 
(CHead c3 k u2)))) (\lambda (u2: T).(\lambda (_: C).(subst1 i v u1 u2))) 
(\lambda (_: T).(\lambda (c3: C).(csubst1 i v c1 c3))) x0 x1 (refl_equal C 
(CHead x1 k x0)) (subst1_single i v u1 x0 H7) (csubst1_sing i v c1 x1 H6)))) 
c2 H3)))))))) H1)) (csubst0_gen_head k c1 c2 u1 v (s k i) H0)))) x H))))))).
(* COMMENTS
Initial nodes: 1817
END *)

