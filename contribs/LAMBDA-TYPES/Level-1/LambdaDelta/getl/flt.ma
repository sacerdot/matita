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

set "baseuri" "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/getl/flt".

include "getl/fwd.ma".

include "clear/props.ma".

include "flt/props.ma".

theorem getl_flt:
 \forall (b: B).(\forall (c: C).(\forall (e: C).(\forall (u: T).(\forall (i: 
nat).((getl i c (CHead e (Bind b) u)) \to (flt e u c (TLRef i)))))))
\def
 \lambda (b: B).(\lambda (c: C).(C_ind (\lambda (c0: C).(\forall (e: 
C).(\forall (u: T).(\forall (i: nat).((getl i c0 (CHead e (Bind b) u)) \to 
(flt e u c0 (TLRef i))))))) (\lambda (n: nat).(\lambda (e: C).(\lambda (u: 
T).(\lambda (i: nat).(\lambda (H: (getl i (CSort n) (CHead e (Bind b) 
u))).(getl_gen_sort n i (CHead e (Bind b) u) H (flt e u (CSort n) (TLRef 
i)))))))) (\lambda (c0: C).(\lambda (H: ((\forall (e: C).(\forall (u: 
T).(\forall (i: nat).((getl i c0 (CHead e (Bind b) u)) \to (flt e u c0 (TLRef 
i)))))))).(\lambda (k: K).(\lambda (t: T).(\lambda (e: C).(\lambda (u: 
T).(\lambda (i: nat).(match i in nat return (\lambda (n: nat).((getl n (CHead 
c0 k t) (CHead e (Bind b) u)) \to (flt e u (CHead c0 k t) (TLRef n)))) with 
[O \Rightarrow (\lambda (H0: (getl O (CHead c0 k t) (CHead e (Bind b) 
u))).((match k in K return (\lambda (k0: K).((clear (CHead c0 k0 t) (CHead e 
(Bind b) u)) \to (flt e u (CHead c0 k0 t) (TLRef O)))) with [(Bind b0) 
\Rightarrow (\lambda (H1: (clear (CHead c0 (Bind b0) t) (CHead e (Bind b) 
u))).(let H2 \def (f_equal C C (\lambda (e0: C).(match e0 in C return 
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
H1)) in (\lambda (H5: (eq B b b0)).(\lambda (H6: (eq C e c0)).(eq_ind_r T t 
(\lambda (t0: T).(flt e t0 (CHead c0 (Bind b0) t) (TLRef O))) (eq_ind_r C c0 
(\lambda (c1: C).(flt c1 t (CHead c0 (Bind b0) t) (TLRef O))) (eq_ind B b 
(\lambda (b1: B).(flt c0 t (CHead c0 (Bind b1) t) (TLRef O))) (flt_arith0 
(Bind b) c0 t O) b0 H5) e H6) u H4)))) H3)) H2))) | (Flat f) \Rightarrow 
(\lambda (H1: (clear (CHead c0 (Flat f) t) (CHead e (Bind b) u))).(flt_arith1 
(Bind b) e c0 u (clear_cle c0 (CHead e (Bind b) u) (clear_gen_flat f c0 
(CHead e (Bind b) u) t H1)) (Flat f) t O))]) (getl_gen_O (CHead c0 k t) 
(CHead e (Bind b) u) H0))) | (S n) \Rightarrow (\lambda (H0: (getl (S n) 
(CHead c0 k t) (CHead e (Bind b) u))).(let H_y \def (H e u (r k n) 
(getl_gen_S k c0 (CHead e (Bind b) u) t n H0)) in (flt_arith2 e c0 u (r k n) 
H_y k t (S n))))])))))))) c)).

