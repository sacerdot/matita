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

include "basic_1/drop1/fwd.ma".

include "basic_1/drop/props.ma".

include "basic_1/getl/defs.ma".

theorem drop1_skip_bind:
 \forall (b: B).(\forall (e: C).(\forall (hds: PList).(\forall (c: 
C).(\forall (u: T).((drop1 hds c e) \to (drop1 (Ss hds) (CHead c (Bind b) 
(lift1 hds u)) (CHead e (Bind b) u)))))))
\def
 \lambda (b: B).(\lambda (e: C).(\lambda (hds: PList).(let TMP_7 \def 
(\lambda (p: PList).(\forall (c: C).(\forall (u: T).((drop1 p c e) \to (let 
TMP_1 \def (Ss p) in (let TMP_2 \def (Bind b) in (let TMP_3 \def (lift1 p u) 
in (let TMP_4 \def (CHead c TMP_2 TMP_3) in (let TMP_5 \def (Bind b) in (let 
TMP_6 \def (CHead e TMP_5 u) in (drop1 TMP_1 TMP_4 TMP_6))))))))))) in (let 
TMP_16 \def (\lambda (c: C).(\lambda (u: T).(\lambda (H: (drop1 PNil c 
e)).(let H_y \def (drop1_gen_pnil c e H) in (let TMP_12 \def (\lambda (c0: 
C).(let TMP_8 \def (Bind b) in (let TMP_9 \def (CHead c0 TMP_8 u) in (let 
TMP_10 \def (Bind b) in (let TMP_11 \def (CHead e TMP_10 u) in (drop1 PNil 
TMP_9 TMP_11)))))) in (let TMP_13 \def (Bind b) in (let TMP_14 \def (CHead e 
TMP_13 u) in (let TMP_15 \def (drop1_nil TMP_14) in (eq_ind_r C e TMP_12 
TMP_15 c H_y))))))))) in (let TMP_44 \def (\lambda (n: nat).(\lambda (n0: 
nat).(\lambda (p: PList).(\lambda (H: ((\forall (c: C).(\forall (u: 
T).((drop1 p c e) \to (drop1 (Ss p) (CHead c (Bind b) (lift1 p u)) (CHead e 
(Bind b) u))))))).(\lambda (c: C).(\lambda (u: T).(\lambda (H0: (drop1 (PCons 
n n0 p) c e)).(let H_x \def (drop1_gen_pcons c e p n n0 H0) in (let H1 \def 
H_x in (let TMP_17 \def (\lambda (c2: C).(drop n n0 c c2)) in (let TMP_18 
\def (\lambda (c2: C).(drop1 p c2 e)) in (let TMP_19 \def (S n0) in (let 
TMP_20 \def (Ss p) in (let TMP_21 \def (PCons n TMP_19 TMP_20) in (let TMP_22 
\def (Bind b) in (let TMP_23 \def (lift1 p u) in (let TMP_24 \def (lift n n0 
TMP_23) in (let TMP_25 \def (CHead c TMP_22 TMP_24) in (let TMP_26 \def (Bind 
b) in (let TMP_27 \def (CHead e TMP_26 u) in (let TMP_28 \def (drop1 TMP_21 
TMP_25 TMP_27) in (let TMP_43 \def (\lambda (x: C).(\lambda (H2: (drop n n0 c 
x)).(\lambda (H3: (drop1 p x e)).(let TMP_29 \def (Bind b) in (let TMP_30 
\def (lift1 p u) in (let TMP_31 \def (lift n n0 TMP_30) in (let TMP_32 \def 
(CHead c TMP_29 TMP_31) in (let TMP_33 \def (Bind b) in (let TMP_34 \def 
(lift1 p u) in (let TMP_35 \def (CHead x TMP_33 TMP_34) in (let TMP_36 \def 
(S n0) in (let TMP_37 \def (lift1 p u) in (let TMP_38 \def (drop_skip_bind n 
n0 c x H2 b TMP_37) in (let TMP_39 \def (Bind b) in (let TMP_40 \def (CHead e 
TMP_39 u) in (let TMP_41 \def (Ss p) in (let TMP_42 \def (H x u H3) in 
(drop1_cons TMP_32 TMP_35 n TMP_36 TMP_38 TMP_40 TMP_41 
TMP_42)))))))))))))))))) in (ex2_ind C TMP_17 TMP_18 TMP_28 TMP_43 
H1))))))))))))))))))))))) in (PList_ind TMP_7 TMP_16 TMP_44 hds)))))).

theorem drop1_cons_tail:
 \forall (c2: C).(\forall (c3: C).(\forall (h: nat).(\forall (d: nat).((drop 
h d c2 c3) \to (\forall (hds: PList).(\forall (c1: C).((drop1 hds c1 c2) \to 
(drop1 (PConsTail hds h d) c1 c3))))))))
\def
 \lambda (c2: C).(\lambda (c3: C).(\lambda (h: nat).(\lambda (d: 
nat).(\lambda (H: (drop h d c2 c3)).(\lambda (hds: PList).(let TMP_2 \def 
(\lambda (p: PList).(\forall (c1: C).((drop1 p c1 c2) \to (let TMP_1 \def 
(PConsTail p h d) in (drop1 TMP_1 c1 c3))))) in (let TMP_7 \def (\lambda (c1: 
C).(\lambda (H0: (drop1 PNil c1 c2)).(let H_y \def (drop1_gen_pnil c1 c2 H0) 
in (let TMP_4 \def (\lambda (c: C).(let TMP_3 \def (PCons h d PNil) in (drop1 
TMP_3 c c3))) in (let TMP_5 \def (drop1_nil c3) in (let TMP_6 \def 
(drop1_cons c2 c3 h d H c3 PNil TMP_5) in (eq_ind_r C c2 TMP_4 TMP_6 c1 
H_y))))))) in (let TMP_16 \def (\lambda (n: nat).(\lambda (n0: nat).(\lambda 
(p: PList).(\lambda (H0: ((\forall (c1: C).((drop1 p c1 c2) \to (drop1 
(PConsTail p h d) c1 c3))))).(\lambda (c1: C).(\lambda (H1: (drop1 (PCons n 
n0 p) c1 c2)).(let H_x \def (drop1_gen_pcons c1 c2 p n n0 H1) in (let H2 \def 
H_x in (let TMP_8 \def (\lambda (c4: C).(drop n n0 c1 c4)) in (let TMP_9 \def 
(\lambda (c4: C).(drop1 p c4 c2)) in (let TMP_10 \def (PConsTail p h d) in 
(let TMP_11 \def (PCons n n0 TMP_10) in (let TMP_12 \def (drop1 TMP_11 c1 c3) 
in (let TMP_15 \def (\lambda (x: C).(\lambda (H3: (drop n n0 c1 x)).(\lambda 
(H4: (drop1 p x c2)).(let TMP_13 \def (PConsTail p h d) in (let TMP_14 \def 
(H0 x H4) in (drop1_cons c1 x n n0 H3 c3 TMP_13 TMP_14)))))) in (ex2_ind C 
TMP_8 TMP_9 TMP_12 TMP_15 H2))))))))))))))) in (PList_ind TMP_2 TMP_7 TMP_16 
hds))))))))).

theorem drop1_trans:
 \forall (is1: PList).(\forall (c1: C).(\forall (c0: C).((drop1 is1 c1 c0) 
\to (\forall (is2: PList).(\forall (c2: C).((drop1 is2 c0 c2) \to (drop1 
(papp is1 is2) c1 c2)))))))
\def
 \lambda (is1: PList).(let TMP_2 \def (\lambda (p: PList).(\forall (c1: 
C).(\forall (c0: C).((drop1 p c1 c0) \to (\forall (is2: PList).(\forall (c2: 
C).((drop1 is2 c0 c2) \to (let TMP_1 \def (papp p is2) in (drop1 TMP_1 c1 
c2))))))))) in (let TMP_4 \def (\lambda (c1: C).(\lambda (c0: C).(\lambda (H: 
(drop1 PNil c1 c0)).(\lambda (is2: PList).(\lambda (c2: C).(\lambda (H0: 
(drop1 is2 c0 c2)).(let H_y \def (drop1_gen_pnil c1 c0 H) in (let TMP_3 \def 
(\lambda (c: C).(drop1 is2 c c2)) in (let H1 \def (eq_ind_r C c0 TMP_3 H0 c1 
H_y) in H1))))))))) in (let TMP_13 \def (\lambda (n: nat).(\lambda (n0: 
nat).(\lambda (p: PList).(\lambda (H: ((\forall (c1: C).(\forall (c0: 
C).((drop1 p c1 c0) \to (\forall (is2: PList).(\forall (c2: C).((drop1 is2 c0 
c2) \to (drop1 (papp p is2) c1 c2))))))))).(\lambda (c1: C).(\lambda (c0: 
C).(\lambda (H0: (drop1 (PCons n n0 p) c1 c0)).(\lambda (is2: PList).(\lambda 
(c2: C).(\lambda (H1: (drop1 is2 c0 c2)).(let H_x \def (drop1_gen_pcons c1 c0 
p n n0 H0) in (let H2 \def H_x in (let TMP_5 \def (\lambda (c3: C).(drop n n0 
c1 c3)) in (let TMP_6 \def (\lambda (c3: C).(drop1 p c3 c0)) in (let TMP_7 
\def (papp p is2) in (let TMP_8 \def (PCons n n0 TMP_7) in (let TMP_9 \def 
(drop1 TMP_8 c1 c2) in (let TMP_12 \def (\lambda (x: C).(\lambda (H3: (drop n 
n0 c1 x)).(\lambda (H4: (drop1 p x c0)).(let TMP_10 \def (papp p is2) in (let 
TMP_11 \def (H x c0 H4 is2 c2 H1) in (drop1_cons c1 x n n0 H3 c2 TMP_10 
TMP_11)))))) in (ex2_ind C TMP_5 TMP_6 TMP_9 TMP_12 H2))))))))))))))))))) in 
(PList_ind TMP_2 TMP_4 TMP_13 is1)))).

