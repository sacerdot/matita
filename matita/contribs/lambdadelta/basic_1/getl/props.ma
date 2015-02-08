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

include "basic_1/getl/fwd.ma".

include "basic_1/clear/props.ma".

include "basic_1/drop/props.ma".

theorem getl_refl:
 \forall (b: B).(\forall (c: C).(\forall (u: T).(getl O (CHead c (Bind b) u) 
(CHead c (Bind b) u))))
\def
 \lambda (b: B).(\lambda (c: C).(\lambda (u: T).(let TMP_1 \def (Bind b) in 
(let TMP_2 \def (CHead c TMP_1 u) in (let TMP_3 \def (Bind b) in (let TMP_4 
\def (CHead c TMP_3 u) in (let TMP_5 \def (Bind b) in (let TMP_6 \def (CHead 
c TMP_5 u) in (let TMP_7 \def (Bind b) in (let TMP_8 \def (CHead c TMP_7 u) 
in (let TMP_9 \def (drop_refl TMP_8) in (let TMP_10 \def (clear_bind b c u) 
in (getl_intro O TMP_2 TMP_4 TMP_6 TMP_9 TMP_10))))))))))))).

theorem getl_head:
 \forall (k: K).(\forall (h: nat).(\forall (c: C).(\forall (e: C).((getl (r k 
h) c e) \to (\forall (u: T).(getl (S h) (CHead c k u) e))))))
\def
 \lambda (k: K).(\lambda (h: nat).(\lambda (c: C).(\lambda (e: C).(\lambda 
(H: (getl (r k h) c e)).(\lambda (u: T).(let TMP_1 \def (r k h) in (let H0 
\def (getl_gen_all c e TMP_1 H) in (let TMP_3 \def (\lambda (e0: C).(let 
TMP_2 \def (r k h) in (drop TMP_2 O c e0))) in (let TMP_4 \def (\lambda (e0: 
C).(clear e0 e)) in (let TMP_5 \def (S h) in (let TMP_6 \def (CHead c k u) in 
(let TMP_7 \def (getl TMP_5 TMP_6 e) in (let TMP_11 \def (\lambda (x: 
C).(\lambda (H1: (drop (r k h) O c x)).(\lambda (H2: (clear x e)).(let TMP_8 
\def (S h) in (let TMP_9 \def (CHead c k u) in (let TMP_10 \def (drop_drop k 
h c x H1 u) in (getl_intro TMP_8 TMP_9 e x TMP_10 H2))))))) in (ex2_ind C 
TMP_3 TMP_4 TMP_7 TMP_11 H0)))))))))))))).

theorem getl_flat:
 \forall (c: C).(\forall (e: C).(\forall (h: nat).((getl h c e) \to (\forall 
(f: F).(\forall (u: T).(getl h (CHead c (Flat f) u) e))))))
\def
 \lambda (c: C).(\lambda (e: C).(\lambda (h: nat).(\lambda (H: (getl h c 
e)).(\lambda (f: F).(\lambda (u: T).(let H0 \def (getl_gen_all c e h H) in 
(let TMP_1 \def (\lambda (e0: C).(drop h O c e0)) in (let TMP_2 \def (\lambda 
(e0: C).(clear e0 e)) in (let TMP_3 \def (Flat f) in (let TMP_4 \def (CHead c 
TMP_3 u) in (let TMP_5 \def (getl h TMP_4 e) in (let TMP_26 \def (\lambda (x: 
C).(\lambda (H1: (drop h O c x)).(\lambda (H2: (clear x e)).(let TMP_8 \def 
(\lambda (n: nat).((drop n O c x) \to (let TMP_6 \def (Flat f) in (let TMP_7 
\def (CHead c TMP_6 u) in (getl n TMP_7 e))))) in (let TMP_19 \def (\lambda 
(H3: (drop O O c x)).(let TMP_9 \def (\lambda (c0: C).(clear c0 e)) in (let 
TMP_10 \def (drop_gen_refl c x H3) in (let H4 \def (eq_ind_r C x TMP_9 H2 c 
TMP_10) in (let TMP_11 \def (Flat f) in (let TMP_12 \def (CHead c TMP_11 u) 
in (let TMP_13 \def (Flat f) in (let TMP_14 \def (CHead c TMP_13 u) in (let 
TMP_15 \def (Flat f) in (let TMP_16 \def (CHead c TMP_15 u) in (let TMP_17 
\def (drop_refl TMP_16) in (let TMP_18 \def (clear_flat c e H4 f u) in 
(getl_intro O TMP_12 e TMP_14 TMP_17 TMP_18))))))))))))) in (let TMP_25 \def 
(\lambda (h0: nat).(\lambda (_: (((drop h0 O c x) \to (getl h0 (CHead c (Flat 
f) u) e)))).(\lambda (H3: (drop (S h0) O c x)).(let TMP_20 \def (S h0) in 
(let TMP_21 \def (Flat f) in (let TMP_22 \def (CHead c TMP_21 u) in (let 
TMP_23 \def (Flat f) in (let TMP_24 \def (drop_drop TMP_23 h0 c x H3 u) in 
(getl_intro TMP_20 TMP_22 e x TMP_24 H2))))))))) in (nat_ind TMP_8 TMP_19 
TMP_25 h H1))))))) in (ex2_ind C TMP_1 TMP_2 TMP_5 TMP_26 H0))))))))))))).

theorem getl_ctail:
 \forall (b: B).(\forall (c: C).(\forall (d: C).(\forall (u: T).(\forall (i: 
nat).((getl i c (CHead d (Bind b) u)) \to (\forall (k: K).(\forall (v: 
T).(getl i (CTail k v c) (CHead (CTail k v d) (Bind b) u)))))))))
\def
 \lambda (b: B).(\lambda (c: C).(\lambda (d: C).(\lambda (u: T).(\lambda (i: 
nat).(\lambda (H: (getl i c (CHead d (Bind b) u))).(\lambda (k: K).(\lambda 
(v: T).(let TMP_1 \def (Bind b) in (let TMP_2 \def (CHead d TMP_1 u) in (let 
H0 \def (getl_gen_all c TMP_2 i H) in (let TMP_3 \def (\lambda (e: C).(drop i 
O c e)) in (let TMP_6 \def (\lambda (e: C).(let TMP_4 \def (Bind b) in (let 
TMP_5 \def (CHead d TMP_4 u) in (clear e TMP_5)))) in (let TMP_7 \def (CTail 
k v c) in (let TMP_8 \def (CTail k v d) in (let TMP_9 \def (Bind b) in (let 
TMP_10 \def (CHead TMP_8 TMP_9 u) in (let TMP_11 \def (getl i TMP_7 TMP_10) 
in (let TMP_19 \def (\lambda (x: C).(\lambda (H1: (drop i O c x)).(\lambda 
(H2: (clear x (CHead d (Bind b) u))).(let TMP_12 \def (CTail k v c) in (let 
TMP_13 \def (CTail k v d) in (let TMP_14 \def (Bind b) in (let TMP_15 \def 
(CHead TMP_13 TMP_14 u) in (let TMP_16 \def (CTail k v x) in (let TMP_17 \def 
(drop_ctail c x O i H1 k v) in (let TMP_18 \def (clear_ctail b x d u H2 k v) 
in (getl_intro i TMP_12 TMP_15 TMP_16 TMP_17 TMP_18))))))))))) in (ex2_ind C 
TMP_3 TMP_6 TMP_11 TMP_19 H0))))))))))))))))))).

