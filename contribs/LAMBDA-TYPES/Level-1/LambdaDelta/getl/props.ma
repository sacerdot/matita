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

set "baseuri" "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/getl/props".

include "getl/fwd.ma".

include "drop/props.ma".

include "clear/props.ma".

theorem getl_refl:
 \forall (b: B).(\forall (c: C).(\forall (u: T).(getl O (CHead c (Bind b) u) 
(CHead c (Bind b) u))))
\def
 \lambda (b: B).(\lambda (c: C).(\lambda (u: T).(getl_intro O (CHead c (Bind 
b) u) (CHead c (Bind b) u) (CHead c (Bind b) u) (drop_refl (CHead c (Bind b) 
u)) (clear_bind b c u)))).

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

theorem getl_flat:
 \forall (c: C).(\forall (e: C).(\forall (h: nat).((getl h c e) \to (\forall 
(f: F).(\forall (u: T).(getl h (CHead c (Flat f) u) e))))))
\def
 \lambda (c: C).(\lambda (e: C).(\lambda (h: nat).(\lambda (H: (getl h c 
e)).(\lambda (f: F).(\lambda (u: T).(let H0 \def (getl_gen_all c e h H) in 
(ex2_ind C (\lambda (e0: C).(drop h O c e0)) (\lambda (e0: C).(clear e0 e)) 
(getl h (CHead c (Flat f) u) e) (\lambda (x: C).(\lambda (H1: (drop h O c 
x)).(\lambda (H2: (clear x e)).((match h in nat return (\lambda (n: 
nat).((drop n O c x) \to (getl n (CHead c (Flat f) u) e))) with [O 
\Rightarrow (\lambda (H3: (drop O O c x)).(let H4 \def (eq_ind_r C x (\lambda 
(c: C).(clear c e)) H2 c (drop_gen_refl c x H3)) in (getl_intro O (CHead c 
(Flat f) u) e (CHead c (Flat f) u) (drop_refl (CHead c (Flat f) u)) 
(clear_flat c e H4 f u)))) | (S n) \Rightarrow (\lambda (H3: (drop (S n) O c 
x)).(getl_intro (S n) (CHead c (Flat f) u) e x (drop_drop (Flat f) n c x H3 
u) H2))]) H1)))) H0))))))).

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

