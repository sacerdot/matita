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

include "Basic-1/getl/fwd.ma".

include "Basic-1/drop/props.ma".

include "Basic-1/clear/props.ma".

theorem getl_refl:
 \forall (b: B).(\forall (c: C).(\forall (u: T).(getl O (CHead c (Bind b) u) 
(CHead c (Bind b) u))))
\def
 \lambda (b: B).(\lambda (c: C).(\lambda (u: T).(getl_intro O (CHead c (Bind 
b) u) (CHead c (Bind b) u) (CHead c (Bind b) u) (drop_refl (CHead c (Bind b) 
u)) (clear_bind b c u)))).
(* COMMENTS
Initial nodes: 59
END *)

theorem getl_head:
 \forall (k: K).(\forall (h: nat).(\forall (c: C).(\forall (e: C).((getl (r k 
h) c e) \to (\forall (u: T).(getl (S h) (CHead c k u) e))))))
\def
 \lambda (k: K).(\lambda (h: nat).(\lambda (c: C).(\lambda (e: C).(\lambda 
(H: (getl (r k h) c e)).(\lambda (u: T).(let H0 \def (getl_gen_all c e (r k 
h) H) in (ex2_ind C (\lambda (e0: C).(drop (r k h) O c e0)) (\lambda (e0: 
C).(clear e0 e)) (getl (S h) (CHead c k u) e) (\lambda (x: C).(\lambda (H1: 
(drop (r k h) O c x)).(\lambda (H2: (clear x e)).(getl_intro (S h) (CHead c k 
u) e x (drop_drop k h c x H1 u) H2)))) H0))))))).
(* COMMENTS
Initial nodes: 137
END *)

theorem getl_flat:
 \forall (c: C).(\forall (e: C).(\forall (h: nat).((getl h c e) \to (\forall 
(f: F).(\forall (u: T).(getl h (CHead c (Flat f) u) e))))))
\def
 \lambda (c: C).(\lambda (e: C).(\lambda (h: nat).(\lambda (H: (getl h c 
e)).(\lambda (f: F).(\lambda (u: T).(let H0 \def (getl_gen_all c e h H) in 
(ex2_ind C (\lambda (e0: C).(drop h O c e0)) (\lambda (e0: C).(clear e0 e)) 
(getl h (CHead c (Flat f) u) e) (\lambda (x: C).(\lambda (H1: (drop h O c 
x)).(\lambda (H2: (clear x e)).(nat_ind (\lambda (n: nat).((drop n O c x) \to 
(getl n (CHead c (Flat f) u) e))) (\lambda (H3: (drop O O c x)).(let H4 \def 
(eq_ind_r C x (\lambda (c0: C).(clear c0 e)) H2 c (drop_gen_refl c x H3)) in 
(getl_intro O (CHead c (Flat f) u) e (CHead c (Flat f) u) (drop_refl (CHead c 
(Flat f) u)) (clear_flat c e H4 f u)))) (\lambda (h0: nat).(\lambda (_: 
(((drop h0 O c x) \to (getl h0 (CHead c (Flat f) u) e)))).(\lambda (H3: (drop 
(S h0) O c x)).(getl_intro (S h0) (CHead c (Flat f) u) e x (drop_drop (Flat 
f) h0 c x H3 u) H2)))) h H1)))) H0))))))).
(* COMMENTS
Initial nodes: 285
END *)

theorem getl_ctail:
 \forall (b: B).(\forall (c: C).(\forall (d: C).(\forall (u: T).(\forall (i: 
nat).((getl i c (CHead d (Bind b) u)) \to (\forall (k: K).(\forall (v: 
T).(getl i (CTail k v c) (CHead (CTail k v d) (Bind b) u)))))))))
\def
 \lambda (b: B).(\lambda (c: C).(\lambda (d: C).(\lambda (u: T).(\lambda (i: 
nat).(\lambda (H: (getl i c (CHead d (Bind b) u))).(\lambda (k: K).(\lambda 
(v: T).(let H0 \def (getl_gen_all c (CHead d (Bind b) u) i H) in (ex2_ind C 
(\lambda (e: C).(drop i O c e)) (\lambda (e: C).(clear e (CHead d (Bind b) 
u))) (getl i (CTail k v c) (CHead (CTail k v d) (Bind b) u)) (\lambda (x: 
C).(\lambda (H1: (drop i O c x)).(\lambda (H2: (clear x (CHead d (Bind b) 
u))).(getl_intro i (CTail k v c) (CHead (CTail k v d) (Bind b) u) (CTail k v 
x) (drop_ctail c x O i H1 k v) (clear_ctail b x d u H2 k v))))) H0))))))))).
(* COMMENTS
Initial nodes: 203
END *)

theorem getl_mono:
 \forall (c: C).(\forall (x1: C).(\forall (h: nat).((getl h c x1) \to 
(\forall (x2: C).((getl h c x2) \to (eq C x1 x2))))))
\def
 \lambda (c: C).(\lambda (x1: C).(\lambda (h: nat).(\lambda (H: (getl h c 
x1)).(\lambda (x2: C).(\lambda (H0: (getl h c x2)).(let H1 \def (getl_gen_all 
c x2 h H0) in (ex2_ind C (\lambda (e: C).(drop h O c e)) (\lambda (e: 
C).(clear e x2)) (eq C x1 x2) (\lambda (x: C).(\lambda (H2: (drop h O c 
x)).(\lambda (H3: (clear x x2)).(let H4 \def (getl_gen_all c x1 h H) in 
(ex2_ind C (\lambda (e: C).(drop h O c e)) (\lambda (e: C).(clear e x1)) (eq 
C x1 x2) (\lambda (x0: C).(\lambda (H5: (drop h O c x0)).(\lambda (H6: (clear 
x0 x1)).(let H7 \def (eq_ind C x (\lambda (c0: C).(drop h O c c0)) H2 x0 
(drop_mono c x O h H2 x0 H5)) in (let H8 \def (eq_ind_r C x0 (\lambda (c0: 
C).(drop h O c c0)) H7 x (drop_mono c x O h H2 x0 H5)) in (let H9 \def 
(eq_ind_r C x0 (\lambda (c0: C).(clear c0 x1)) H6 x (drop_mono c x O h H2 x0 
H5)) in (clear_mono x x1 H9 x2 H3))))))) H4))))) H1))))))).
(* COMMENTS
Initial nodes: 269
END *)

