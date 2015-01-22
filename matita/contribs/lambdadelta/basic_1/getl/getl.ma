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

include "Basic-1/getl/drop.ma".

include "Basic-1/getl/clear.ma".

theorem getl_conf_le:
 \forall (i: nat).(\forall (a: C).(\forall (c: C).((getl i c a) \to (\forall 
(e: C).(\forall (h: nat).((getl h c e) \to ((le h i) \to (getl (minus i h) e 
a))))))))
\def
 \lambda (i: nat).(\lambda (a: C).(\lambda (c: C).(\lambda (H: (getl i c 
a)).(\lambda (e: C).(\lambda (h: nat).(\lambda (H0: (getl h c e)).(\lambda 
(H1: (le h i)).(let H2 \def (getl_gen_all c e h H0) in (ex2_ind C (\lambda 
(e0: C).(drop h O c e0)) (\lambda (e0: C).(clear e0 e)) (getl (minus i h) e 
a) (\lambda (x: C).(\lambda (H3: (drop h O c x)).(\lambda (H4: (clear x 
e)).(getl_clear_conf (minus i h) x a (getl_drop_conf_ge i a c H x h O H3 H1) 
e H4)))) H2))))))))).
(* COMMENTS
Initial nodes: 133
END *)

theorem getl_trans:
 \forall (i: nat).(\forall (c1: C).(\forall (c2: C).(\forall (h: nat).((getl 
h c1 c2) \to (\forall (e2: C).((getl i c2 e2) \to (getl (plus i h) c1 
e2)))))))
\def
 \lambda (i: nat).(\lambda (c1: C).(\lambda (c2: C).(\lambda (h: 
nat).(\lambda (H: (getl h c1 c2)).(\lambda (e2: C).(\lambda (H0: (getl i c2 
e2)).(let H1 \def (getl_gen_all c2 e2 i H0) in (ex2_ind C (\lambda (e: 
C).(drop i O c2 e)) (\lambda (e: C).(clear e e2)) (getl (plus i h) c1 e2) 
(\lambda (x: C).(\lambda (H2: (drop i O c2 x)).(\lambda (H3: (clear x 
e2)).(nat_ind (\lambda (n: nat).((drop n O c2 x) \to (getl (plus n h) c1 
e2))) (\lambda (H4: (drop O O c2 x)).(let H5 \def (eq_ind_r C x (\lambda (c: 
C).(clear c e2)) H3 c2 (drop_gen_refl c2 x H4)) in (getl_clear_trans (plus O 
h) c1 c2 H e2 H5))) (\lambda (i0: nat).(\lambda (_: (((drop i0 O c2 x) \to 
(getl (plus i0 h) c1 e2)))).(\lambda (H4: (drop (S i0) O c2 x)).(let H_y \def 
(getl_drop_trans c1 c2 h H x i0 H4) in (getl_intro (plus (S i0) h) c1 e2 x 
H_y H3))))) i H2)))) H1)))))))).
(* COMMENTS
Initial nodes: 247
END *)

