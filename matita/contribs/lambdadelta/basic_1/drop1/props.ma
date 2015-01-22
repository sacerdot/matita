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

include "Basic-1/drop1/fwd.ma".

include "Basic-1/drop/props.ma".

include "Basic-1/getl/defs.ma".

theorem drop1_skip_bind:
 \forall (b: B).(\forall (e: C).(\forall (hds: PList).(\forall (c: 
C).(\forall (u: T).((drop1 hds c e) \to (drop1 (Ss hds) (CHead c (Bind b) 
(lift1 hds u)) (CHead e (Bind b) u)))))))
\def
 \lambda (b: B).(\lambda (e: C).(\lambda (hds: PList).(PList_ind (\lambda (p: 
PList).(\forall (c: C).(\forall (u: T).((drop1 p c e) \to (drop1 (Ss p) 
(CHead c (Bind b) (lift1 p u)) (CHead e (Bind b) u)))))) (\lambda (c: 
C).(\lambda (u: T).(\lambda (H: (drop1 PNil c e)).(let H_y \def 
(drop1_gen_pnil c e H) in (eq_ind_r C e (\lambda (c0: C).(drop1 PNil (CHead 
c0 (Bind b) u) (CHead e (Bind b) u))) (drop1_nil (CHead e (Bind b) u)) c 
H_y))))) (\lambda (n: nat).(\lambda (n0: nat).(\lambda (p: PList).(\lambda 
(H: ((\forall (c: C).(\forall (u: T).((drop1 p c e) \to (drop1 (Ss p) (CHead 
c (Bind b) (lift1 p u)) (CHead e (Bind b) u))))))).(\lambda (c: C).(\lambda 
(u: T).(\lambda (H0: (drop1 (PCons n n0 p) c e)).(let H_x \def 
(drop1_gen_pcons c e p n n0 H0) in (let H1 \def H_x in (ex2_ind C (\lambda 
(c2: C).(drop n n0 c c2)) (\lambda (c2: C).(drop1 p c2 e)) (drop1 (PCons n (S 
n0) (Ss p)) (CHead c (Bind b) (lift n n0 (lift1 p u))) (CHead e (Bind b) u)) 
(\lambda (x: C).(\lambda (H2: (drop n n0 c x)).(\lambda (H3: (drop1 p x 
e)).(drop1_cons (CHead c (Bind b) (lift n n0 (lift1 p u))) (CHead x (Bind b) 
(lift1 p u)) n (S n0) (drop_skip_bind n n0 c x H2 b (lift1 p u)) (CHead e 
(Bind b) u) (Ss p) (H x u H3))))) H1)))))))))) hds))).
(* COMMENTS
Initial nodes: 379
END *)

theorem drop1_cons_tail:
 \forall (c2: C).(\forall (c3: C).(\forall (h: nat).(\forall (d: nat).((drop 
h d c2 c3) \to (\forall (hds: PList).(\forall (c1: C).((drop1 hds c1 c2) \to 
(drop1 (PConsTail hds h d) c1 c3))))))))
\def
 \lambda (c2: C).(\lambda (c3: C).(\lambda (h: nat).(\lambda (d: 
nat).(\lambda (H: (drop h d c2 c3)).(\lambda (hds: PList).(PList_ind (\lambda 
(p: PList).(\forall (c1: C).((drop1 p c1 c2) \to (drop1 (PConsTail p h d) c1 
c3)))) (\lambda (c1: C).(\lambda (H0: (drop1 PNil c1 c2)).(let H_y \def 
(drop1_gen_pnil c1 c2 H0) in (eq_ind_r C c2 (\lambda (c: C).(drop1 (PCons h d 
PNil) c c3)) (drop1_cons c2 c3 h d H c3 PNil (drop1_nil c3)) c1 H_y)))) 
(\lambda (n: nat).(\lambda (n0: nat).(\lambda (p: PList).(\lambda (H0: 
((\forall (c1: C).((drop1 p c1 c2) \to (drop1 (PConsTail p h d) c1 
c3))))).(\lambda (c1: C).(\lambda (H1: (drop1 (PCons n n0 p) c1 c2)).(let H_x 
\def (drop1_gen_pcons c1 c2 p n n0 H1) in (let H2 \def H_x in (ex2_ind C 
(\lambda (c4: C).(drop n n0 c1 c4)) (\lambda (c4: C).(drop1 p c4 c2)) (drop1 
(PCons n n0 (PConsTail p h d)) c1 c3) (\lambda (x: C).(\lambda (H3: (drop n 
n0 c1 x)).(\lambda (H4: (drop1 p x c2)).(drop1_cons c1 x n n0 H3 c3 
(PConsTail p h d) (H0 x H4))))) H2))))))))) hds)))))).
(* COMMENTS
Initial nodes: 271
END *)

theorem drop1_trans:
 \forall (is1: PList).(\forall (c1: C).(\forall (c0: C).((drop1 is1 c1 c0) 
\to (\forall (is2: PList).(\forall (c2: C).((drop1 is2 c0 c2) \to (drop1 
(papp is1 is2) c1 c2)))))))
\def
 \lambda (is1: PList).(PList_ind (\lambda (p: PList).(\forall (c1: 
C).(\forall (c0: C).((drop1 p c1 c0) \to (\forall (is2: PList).(\forall (c2: 
C).((drop1 is2 c0 c2) \to (drop1 (papp p is2) c1 c2)))))))) (\lambda (c1: 
C).(\lambda (c0: C).(\lambda (H: (drop1 PNil c1 c0)).(\lambda (is2: 
PList).(\lambda (c2: C).(\lambda (H0: (drop1 is2 c0 c2)).(let H_y \def 
(drop1_gen_pnil c1 c0 H) in (let H1 \def (eq_ind_r C c0 (\lambda (c: 
C).(drop1 is2 c c2)) H0 c1 H_y) in H1)))))))) (\lambda (n: nat).(\lambda (n0: 
nat).(\lambda (p: PList).(\lambda (H: ((\forall (c1: C).(\forall (c0: 
C).((drop1 p c1 c0) \to (\forall (is2: PList).(\forall (c2: C).((drop1 is2 c0 
c2) \to (drop1 (papp p is2) c1 c2))))))))).(\lambda (c1: C).(\lambda (c0: 
C).(\lambda (H0: (drop1 (PCons n n0 p) c1 c0)).(\lambda (is2: PList).(\lambda 
(c2: C).(\lambda (H1: (drop1 is2 c0 c2)).(let H_x \def (drop1_gen_pcons c1 c0 
p n n0 H0) in (let H2 \def H_x in (ex2_ind C (\lambda (c3: C).(drop n n0 c1 
c3)) (\lambda (c3: C).(drop1 p c3 c0)) (drop1 (PCons n n0 (papp p is2)) c1 
c2) (\lambda (x: C).(\lambda (H3: (drop n n0 c1 x)).(\lambda (H4: (drop1 p x 
c0)).(drop1_cons c1 x n n0 H3 c2 (papp p is2) (H x c0 H4 is2 c2 H1))))) 
H2))))))))))))) is1).
(* COMMENTS
Initial nodes: 287
END *)

