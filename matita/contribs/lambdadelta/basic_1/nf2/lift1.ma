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

include "Basic-1/nf2/props.ma".

include "Basic-1/drop1/fwd.ma".

theorem nf2_lift1:
 \forall (e: C).(\forall (hds: PList).(\forall (c: C).(\forall (t: T).((drop1 
hds c e) \to ((nf2 e t) \to (nf2 c (lift1 hds t)))))))
\def
 \lambda (e: C).(\lambda (hds: PList).(PList_ind (\lambda (p: PList).(\forall 
(c: C).(\forall (t: T).((drop1 p c e) \to ((nf2 e t) \to (nf2 c (lift1 p 
t))))))) (\lambda (c: C).(\lambda (t: T).(\lambda (H: (drop1 PNil c 
e)).(\lambda (H0: (nf2 e t)).(let H_y \def (drop1_gen_pnil c e H) in 
(eq_ind_r C e (\lambda (c0: C).(nf2 c0 t)) H0 c H_y)))))) (\lambda (n: 
nat).(\lambda (n0: nat).(\lambda (p: PList).(\lambda (H: ((\forall (c: 
C).(\forall (t: T).((drop1 p c e) \to ((nf2 e t) \to (nf2 c (lift1 p 
t)))))))).(\lambda (c: C).(\lambda (t: T).(\lambda (H0: (drop1 (PCons n n0 p) 
c e)).(\lambda (H1: (nf2 e t)).(let H_x \def (drop1_gen_pcons c e p n n0 H0) 
in (let H2 \def H_x in (ex2_ind C (\lambda (c2: C).(drop n n0 c c2)) (\lambda 
(c2: C).(drop1 p c2 e)) (nf2 c (lift n n0 (lift1 p t))) (\lambda (x: 
C).(\lambda (H3: (drop n n0 c x)).(\lambda (H4: (drop1 p x e)).(nf2_lift x 
(lift1 p t) (H x t H4 H1) c n n0 H3)))) H2))))))))))) hds)).
(* COMMENTS
Initial nodes: 249
END *)

