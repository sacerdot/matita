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

include "Basic-1/sn3/props.ma".

include "Basic-1/drop1/fwd.ma".

include "Basic-1/lift1/fwd.ma".

theorem sns3_lifts1:
 \forall (e: C).(\forall (hds: PList).(\forall (c: C).((drop1 hds c e) \to 
(\forall (ts: TList).((sns3 e ts) \to (sns3 c (lifts1 hds ts)))))))
\def
 \lambda (e: C).(\lambda (hds: PList).(PList_ind (\lambda (p: PList).(\forall 
(c: C).((drop1 p c e) \to (\forall (ts: TList).((sns3 e ts) \to (sns3 c 
(lifts1 p ts))))))) (\lambda (c: C).(\lambda (H: (drop1 PNil c e)).(\lambda 
(ts: TList).(\lambda (H0: (sns3 e ts)).(let H_y \def (drop1_gen_pnil c e H) 
in (eq_ind_r C e (\lambda (c0: C).(sns3 c0 (lifts1 PNil ts))) (eq_ind_r TList 
ts (\lambda (t: TList).(sns3 e t)) H0 (lifts1 PNil ts) (lifts1_nil ts)) c 
H_y)))))) (\lambda (n: nat).(\lambda (n0: nat).(\lambda (p: PList).(\lambda 
(H: ((\forall (c: C).((drop1 p c e) \to (\forall (ts: TList).((sns3 e ts) \to 
(sns3 c (lifts1 p ts)))))))).(\lambda (c: C).(\lambda (H0: (drop1 (PCons n n0 
p) c e)).(\lambda (ts: TList).(\lambda (H1: (sns3 e ts)).(let H_x \def 
(drop1_gen_pcons c e p n n0 H0) in (let H2 \def H_x in (ex2_ind C (\lambda 
(c2: C).(drop n n0 c c2)) (\lambda (c2: C).(drop1 p c2 e)) (sns3 c (lifts1 
(PCons n n0 p) ts)) (\lambda (x: C).(\lambda (H3: (drop n n0 c x)).(\lambda 
(H4: (drop1 p x e)).(eq_ind_r TList (lifts n n0 (lifts1 p ts)) (\lambda (t: 
TList).(sns3 c t)) (sns3_lifts c x n n0 H3 (lifts1 p ts) (H x H4 ts H1)) 
(lifts1 (PCons n n0 p) ts) (lifts1_cons n n0 p ts))))) H2))))))))))) hds)).
(* COMMENTS
Initial nodes: 323
END *)

