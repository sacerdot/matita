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

include "basic_1/flt/props.ma".

theorem getl_flt:
 \forall (b: B).(\forall (c: C).(\forall (e: C).(\forall (u: T).(\forall (i: 
nat).((getl i c (CHead e (Bind b) u)) \to (flt e u c (TLRef i)))))))
\def
 \lambda (b: B).(\lambda (c: C).(let TMP_2 \def (\lambda (c0: C).(\forall (e: 
C).(\forall (u: T).(\forall (i: nat).((getl i c0 (CHead e (Bind b) u)) \to 
(let TMP_1 \def (TLRef i) in (flt e u c0 TMP_1))))))) in (let TMP_8 \def 
(\lambda (n: nat).(\lambda (e: C).(\lambda (u: T).(\lambda (i: nat).(\lambda 
(H: (getl i (CSort n) (CHead e (Bind b) u))).(let TMP_3 \def (Bind b) in (let 
TMP_4 \def (CHead e TMP_3 u) in (let TMP_5 \def (CSort n) in (let TMP_6 \def 
(TLRef i) in (let TMP_7 \def (flt e u TMP_5 TMP_6) in (getl_gen_sort n i 
TMP_4 H TMP_7))))))))))) in (let TMP_79 \def (\lambda (c0: C).(\lambda (H: 
((\forall (e: C).(\forall (u: T).(\forall (i: nat).((getl i c0 (CHead e (Bind 
b) u)) \to (flt e u c0 (TLRef i)))))))).(\lambda (k: K).(\lambda (t: 
T).(\lambda (e: C).(\lambda (u: T).(\lambda (i: nat).(let TMP_11 \def 
(\lambda (n: nat).((getl n (CHead c0 k t) (CHead e (Bind b) u)) \to (let 
TMP_9 \def (CHead c0 k t) in (let TMP_10 \def (TLRef n) in (flt e u TMP_9 
TMP_10))))) in (let TMP_71 \def (\lambda (H0: (getl O (CHead c0 k t) (CHead e 
(Bind b) u))).(let TMP_14 \def (\lambda (k0: K).((clear (CHead c0 k0 t) 
(CHead e (Bind b) u)) \to (let TMP_12 \def (CHead c0 k0 t) in (let TMP_13 
\def (TLRef O) in (flt e u TMP_12 TMP_13))))) in (let TMP_57 \def (\lambda 
(b0: B).(\lambda (H1: (clear (CHead c0 (Bind b0) t) (CHead e (Bind b) 
u))).(let TMP_15 \def (\lambda (e0: C).(match e0 with [(CSort _) \Rightarrow 
e | (CHead c1 _ _) \Rightarrow c1])) in (let TMP_16 \def (Bind b) in (let 
TMP_17 \def (CHead e TMP_16 u) in (let TMP_18 \def (Bind b0) in (let TMP_19 
\def (CHead c0 TMP_18 t) in (let TMP_20 \def (Bind b) in (let TMP_21 \def 
(CHead e TMP_20 u) in (let TMP_22 \def (clear_gen_bind b0 c0 TMP_21 t H1) in 
(let H2 \def (f_equal C C TMP_15 TMP_17 TMP_19 TMP_22) in (let TMP_23 \def 
(\lambda (e0: C).(match e0 with [(CSort _) \Rightarrow b | (CHead _ k0 _) 
\Rightarrow (match k0 with [(Bind b1) \Rightarrow b1 | (Flat _) \Rightarrow 
b])])) in (let TMP_24 \def (Bind b) in (let TMP_25 \def (CHead e TMP_24 u) in 
(let TMP_26 \def (Bind b0) in (let TMP_27 \def (CHead c0 TMP_26 t) in (let 
TMP_28 \def (Bind b) in (let TMP_29 \def (CHead e TMP_28 u) in (let TMP_30 
\def (clear_gen_bind b0 c0 TMP_29 t H1) in (let H3 \def (f_equal C B TMP_23 
TMP_25 TMP_27 TMP_30) in (let TMP_31 \def (\lambda (e0: C).(match e0 with 
[(CSort _) \Rightarrow u | (CHead _ _ t0) \Rightarrow t0])) in (let TMP_32 
\def (Bind b) in (let TMP_33 \def (CHead e TMP_32 u) in (let TMP_34 \def 
(Bind b0) in (let TMP_35 \def (CHead c0 TMP_34 t) in (let TMP_36 \def (Bind 
b) in (let TMP_37 \def (CHead e TMP_36 u) in (let TMP_38 \def (clear_gen_bind 
b0 c0 TMP_37 t H1) in (let H4 \def (f_equal C T TMP_31 TMP_33 TMP_35 TMP_38) 
in (let TMP_55 \def (\lambda (H5: (eq B b b0)).(\lambda (H6: (eq C e 
c0)).(let TMP_42 \def (\lambda (t0: T).(let TMP_39 \def (Bind b0) in (let 
TMP_40 \def (CHead c0 TMP_39 t) in (let TMP_41 \def (TLRef O) in (flt e t0 
TMP_40 TMP_41))))) in (let TMP_46 \def (\lambda (c1: C).(let TMP_43 \def 
(Bind b0) in (let TMP_44 \def (CHead c0 TMP_43 t) in (let TMP_45 \def (TLRef 
O) in (flt c1 t TMP_44 TMP_45))))) in (let TMP_50 \def (\lambda (b1: B).(let 
TMP_47 \def (Bind b1) in (let TMP_48 \def (CHead c0 TMP_47 t) in (let TMP_49 
\def (TLRef O) in (flt c0 t TMP_48 TMP_49))))) in (let TMP_51 \def (Bind b) 
in (let TMP_52 \def (flt_arith0 TMP_51 c0 t O) in (let TMP_53 \def (eq_ind B 
b TMP_50 TMP_52 b0 H5) in (let TMP_54 \def (eq_ind_r C c0 TMP_46 TMP_53 e H6) 
in (eq_ind_r T t TMP_42 TMP_54 u H4)))))))))) in (let TMP_56 \def (TMP_55 H3) 
in (TMP_56 H2)))))))))))))))))))))))))))))))) in (let TMP_66 \def (\lambda 
(f: F).(\lambda (H1: (clear (CHead c0 (Flat f) t) (CHead e (Bind b) u))).(let 
TMP_58 \def (Bind b) in (let TMP_59 \def (Bind b) in (let TMP_60 \def (CHead 
e TMP_59 u) in (let TMP_61 \def (Bind b) in (let TMP_62 \def (CHead e TMP_61 
u) in (let TMP_63 \def (clear_gen_flat f c0 TMP_62 t H1) in (let TMP_64 \def 
(clear_cle c0 TMP_60 TMP_63) in (let TMP_65 \def (Flat f) in (flt_arith1 
TMP_58 e c0 u TMP_64 TMP_65 t O))))))))))) in (let TMP_67 \def (CHead c0 k t) 
in (let TMP_68 \def (Bind b) in (let TMP_69 \def (CHead e TMP_68 u) in (let 
TMP_70 \def (getl_gen_O TMP_67 TMP_69 H0) in (K_ind TMP_14 TMP_57 TMP_66 k 
TMP_70))))))))) in (let TMP_78 \def (\lambda (n: nat).(\lambda (_: (((getl n 
(CHead c0 k t) (CHead e (Bind b) u)) \to (flt e u (CHead c0 k t) (TLRef 
n))))).(\lambda (H1: (getl (S n) (CHead c0 k t) (CHead e (Bind b) u))).(let 
TMP_72 \def (r k n) in (let TMP_73 \def (Bind b) in (let TMP_74 \def (CHead e 
TMP_73 u) in (let TMP_75 \def (getl_gen_S k c0 TMP_74 t n H1) in (let H_y 
\def (H e u TMP_72 TMP_75) in (let TMP_76 \def (r k n) in (let TMP_77 \def (S 
n) in (flt_arith2 e c0 u TMP_76 H_y k t TMP_77))))))))))) in (nat_ind TMP_11 
TMP_71 TMP_78 i))))))))))) in (C_ind TMP_2 TMP_8 TMP_79 c))))).

