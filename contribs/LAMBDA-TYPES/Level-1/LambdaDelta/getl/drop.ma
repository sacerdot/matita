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

set "baseuri" "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/getl/drop".

include "getl/fwd.ma".

include "clear/drop.ma".

include "r/props.ma".

theorem getl_drop:
 \forall (b: B).(\forall (c: C).(\forall (e: C).(\forall (u: T).(\forall (h: 
nat).((getl h c (CHead e (Bind b) u)) \to (drop (S h) O c e))))))
\def
 \lambda (b: B).(\lambda (c: C).(C_ind (\lambda (c0: C).(\forall (e: 
C).(\forall (u: T).(\forall (h: nat).((getl h c0 (CHead e (Bind b) u)) \to 
(drop (S h) O c0 e)))))) (\lambda (n: nat).(\lambda (e: C).(\lambda (u: 
T).(\lambda (h: nat).(\lambda (H: (getl h (CSort n) (CHead e (Bind b) 
u))).(getl_gen_sort n h (CHead e (Bind b) u) H (drop (S h) O (CSort n) 
e))))))) (\lambda (c0: C).(\lambda (H: ((\forall (e: C).(\forall (u: 
T).(\forall (h: nat).((getl h c0 (CHead e (Bind b) u)) \to (drop (S h) O c0 
e))))))).(\lambda (k: K).(\lambda (t: T).(\lambda (e: C).(\lambda (u: 
T).(\lambda (h: nat).(nat_ind (\lambda (n: nat).((getl n (CHead c0 k t) 
(CHead e (Bind b) u)) \to (drop (S n) O (CHead c0 k t) e))) (\lambda (H0: 
(getl O (CHead c0 k t) (CHead e (Bind b) u))).(K_ind (\lambda (k0: K).((clear 
(CHead c0 k0 t) (CHead e (Bind b) u)) \to (drop (S O) O (CHead c0 k0 t) e))) 
(\lambda (b0: B).(\lambda (H1: (clear (CHead c0 (Bind b0) t) (CHead e (Bind 
b) u))).(let H2 \def (f_equal C C (\lambda (e0: C).(match e0 in C return 
(\lambda (_: C).C) with [(CSort _) \Rightarrow e | (CHead c _ _) \Rightarrow 
c])) (CHead e (Bind b) u) (CHead c0 (Bind b0) t) (clear_gen_bind b0 c0 (CHead 
e (Bind b) u) t H1)) in ((let H3 \def (f_equal C B (\lambda (e0: C).(match e0 
in C return (\lambda (_: C).B) with [(CSort _) \Rightarrow b | (CHead _ k _) 
\Rightarrow (match k in K return (\lambda (_: K).B) with [(Bind b) 
\Rightarrow b | (Flat _) \Rightarrow b])])) (CHead e (Bind b) u) (CHead c0 
(Bind b0) t) (clear_gen_bind b0 c0 (CHead e (Bind b) u) t H1)) in ((let H4 
\def (f_equal C T (\lambda (e0: C).(match e0 in C return (\lambda (_: C).T) 
with [(CSort _) \Rightarrow u | (CHead _ _ t) \Rightarrow t])) (CHead e (Bind 
b) u) (CHead c0 (Bind b0) t) (clear_gen_bind b0 c0 (CHead e (Bind b) u) t 
H1)) in (\lambda (H5: (eq B b b0)).(\lambda (H6: (eq C e c0)).(eq_ind_r C c0 
(\lambda (c1: C).(drop (S O) O (CHead c0 (Bind b0) t) c1)) (eq_ind B b 
(\lambda (b1: B).(drop (S O) O (CHead c0 (Bind b1) t) c0)) (drop_drop (Bind 
b) O c0 c0 (drop_refl c0) t) b0 H5) e H6)))) H3)) H2)))) (\lambda (f: 
F).(\lambda (H1: (clear (CHead c0 (Flat f) t) (CHead e (Bind b) 
u))).(drop_clear_O b (CHead c0 (Flat f) t) e u (clear_flat c0 (CHead e (Bind 
b) u) (clear_gen_flat f c0 (CHead e (Bind b) u) t H1) f t) e O (drop_refl 
e)))) k (getl_gen_O (CHead c0 k t) (CHead e (Bind b) u) H0))) (\lambda (n: 
nat).(\lambda (_: (((getl n (CHead c0 k t) (CHead e (Bind b) u)) \to (drop (S 
n) O (CHead c0 k t) e)))).(\lambda (H1: (getl (S n) (CHead c0 k t) (CHead e 
(Bind b) u))).(drop_drop k (S n) c0 e (eq_ind_r nat (S (r k n)) (\lambda (n0: 
nat).(drop n0 O c0 e)) (H e u (r k n) (getl_gen_S k c0 (CHead e (Bind b) u) t 
n H1)) (r k (S n)) (r_S k n)) t)))) h)))))))) c)).

