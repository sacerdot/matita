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

include "Basic-1/drop1/fwd.ma".

include "Basic-1/getl/drop.ma".

theorem drop1_getl_trans:
 \forall (hds: PList).(\forall (c1: C).(\forall (c2: C).((drop1 hds c2 c1) 
\to (\forall (b: B).(\forall (e1: C).(\forall (v: T).(\forall (i: nat).((getl 
i c1 (CHead e1 (Bind b) v)) \to (ex2 C (\lambda (e2: C).(drop1 (ptrans hds i) 
e2 e1)) (\lambda (e2: C).(getl (trans hds i) c2 (CHead e2 (Bind b) (lift1 
(ptrans hds i) v)))))))))))))
\def
 \lambda (hds: PList).(PList_ind (\lambda (p: PList).(\forall (c1: 
C).(\forall (c2: C).((drop1 p c2 c1) \to (\forall (b: B).(\forall (e1: 
C).(\forall (v: T).(\forall (i: nat).((getl i c1 (CHead e1 (Bind b) v)) \to 
(ex2 C (\lambda (e2: C).(drop1 (ptrans p i) e2 e1)) (\lambda (e2: C).(getl 
(trans p i) c2 (CHead e2 (Bind b) (lift1 (ptrans p i) v)))))))))))))) 
(\lambda (c1: C).(\lambda (c2: C).(\lambda (H: (drop1 PNil c2 c1)).(\lambda 
(b: B).(\lambda (e1: C).(\lambda (v: T).(\lambda (i: nat).(\lambda (H0: (getl 
i c1 (CHead e1 (Bind b) v))).(let H_y \def (drop1_gen_pnil c2 c1 H) in 
(eq_ind_r C c1 (\lambda (c: C).(ex2 C (\lambda (e2: C).(drop1 PNil e2 e1)) 
(\lambda (e2: C).(getl i c (CHead e2 (Bind b) v))))) (ex_intro2 C (\lambda 
(e2: C).(drop1 PNil e2 e1)) (\lambda (e2: C).(getl i c1 (CHead e2 (Bind b) 
v))) e1 (drop1_nil e1) H0) c2 H_y)))))))))) (\lambda (h: nat).(\lambda (d: 
nat).(\lambda (hds0: PList).(\lambda (H: ((\forall (c1: C).(\forall (c2: 
C).((drop1 hds0 c2 c1) \to (\forall (b: B).(\forall (e1: C).(\forall (v: 
T).(\forall (i: nat).((getl i c1 (CHead e1 (Bind b) v)) \to (ex2 C (\lambda 
(e2: C).(drop1 (ptrans hds0 i) e2 e1)) (\lambda (e2: C).(getl (trans hds0 i) 
c2 (CHead e2 (Bind b) (lift1 (ptrans hds0 i) v))))))))))))))).(\lambda (c1: 
C).(\lambda (c2: C).(\lambda (H0: (drop1 (PCons h d hds0) c2 c1)).(\lambda 
(b: B).(\lambda (e1: C).(\lambda (v: T).(\lambda (i: nat).(\lambda (H1: (getl 
i c1 (CHead e1 (Bind b) v))).(let H_x \def (drop1_gen_pcons c2 c1 hds0 h d 
H0) in (let H2 \def H_x in (ex2_ind C (\lambda (c3: C).(drop h d c2 c3)) 
(\lambda (c3: C).(drop1 hds0 c3 c1)) (ex2 C (\lambda (e2: C).(drop1 (match 
(blt (trans hds0 i) d) with [true \Rightarrow (PCons h (minus d (S (trans 
hds0 i))) (ptrans hds0 i)) | false \Rightarrow (ptrans hds0 i)]) e2 e1)) 
(\lambda (e2: C).(getl (match (blt (trans hds0 i) d) with [true \Rightarrow 
(trans hds0 i) | false \Rightarrow (plus (trans hds0 i) h)]) c2 (CHead e2 
(Bind b) (lift1 (match (blt (trans hds0 i) d) with [true \Rightarrow (PCons h 
(minus d (S (trans hds0 i))) (ptrans hds0 i)) | false \Rightarrow (ptrans 
hds0 i)]) v))))) (\lambda (x: C).(\lambda (H3: (drop h d c2 x)).(\lambda (H4: 
(drop1 hds0 x c1)).(xinduction bool (blt (trans hds0 i) d) (\lambda (b0: 
bool).(ex2 C (\lambda (e2: C).(drop1 (match b0 with [true \Rightarrow (PCons 
h (minus d (S (trans hds0 i))) (ptrans hds0 i)) | false \Rightarrow (ptrans 
hds0 i)]) e2 e1)) (\lambda (e2: C).(getl (match b0 with [true \Rightarrow 
(trans hds0 i) | false \Rightarrow (plus (trans hds0 i) h)]) c2 (CHead e2 
(Bind b) (lift1 (match b0 with [true \Rightarrow (PCons h (minus d (S (trans 
hds0 i))) (ptrans hds0 i)) | false \Rightarrow (ptrans hds0 i)]) v)))))) 
(\lambda (x_x: bool).(bool_ind (\lambda (b0: bool).((eq bool (blt (trans hds0 
i) d) b0) \to (ex2 C (\lambda (e2: C).(drop1 (match b0 with [true \Rightarrow 
(PCons h (minus d (S (trans hds0 i))) (ptrans hds0 i)) | false \Rightarrow 
(ptrans hds0 i)]) e2 e1)) (\lambda (e2: C).(getl (match b0 with [true 
\Rightarrow (trans hds0 i) | false \Rightarrow (plus (trans hds0 i) h)]) c2 
(CHead e2 (Bind b) (lift1 (match b0 with [true \Rightarrow (PCons h (minus d 
(S (trans hds0 i))) (ptrans hds0 i)) | false \Rightarrow (ptrans hds0 i)]) 
v))))))) (\lambda (H5: (eq bool (blt (trans hds0 i) d) true)).(let H_x0 \def 
(H c1 x H4 b e1 v i H1) in (let H6 \def H_x0 in (ex2_ind C (\lambda (e2: 
C).(drop1 (ptrans hds0 i) e2 e1)) (\lambda (e2: C).(getl (trans hds0 i) x 
(CHead e2 (Bind b) (lift1 (ptrans hds0 i) v)))) (ex2 C (\lambda (e2: 
C).(drop1 (PCons h (minus d (S (trans hds0 i))) (ptrans hds0 i)) e2 e1)) 
(\lambda (e2: C).(getl (trans hds0 i) c2 (CHead e2 (Bind b) (lift1 (PCons h 
(minus d (S (trans hds0 i))) (ptrans hds0 i)) v))))) (\lambda (x0: 
C).(\lambda (H7: (drop1 (ptrans hds0 i) x0 e1)).(\lambda (H8: (getl (trans 
hds0 i) x (CHead x0 (Bind b) (lift1 (ptrans hds0 i) v)))).(let H_x1 \def 
(drop_getl_trans_lt (trans hds0 i) d (blt_lt d (trans hds0 i) H5) c2 x h H3 b 
x0 (lift1 (ptrans hds0 i) v) H8) in (let H9 \def H_x1 in (ex2_ind C (\lambda 
(e2: C).(getl (trans hds0 i) c2 (CHead e2 (Bind b) (lift h (minus d (S (trans 
hds0 i))) (lift1 (ptrans hds0 i) v))))) (\lambda (e2: C).(drop h (minus d (S 
(trans hds0 i))) e2 x0)) (ex2 C (\lambda (e2: C).(drop1 (PCons h (minus d (S 
(trans hds0 i))) (ptrans hds0 i)) e2 e1)) (\lambda (e2: C).(getl (trans hds0 
i) c2 (CHead e2 (Bind b) (lift1 (PCons h (minus d (S (trans hds0 i))) (ptrans 
hds0 i)) v))))) (\lambda (x1: C).(\lambda (H10: (getl (trans hds0 i) c2 
(CHead x1 (Bind b) (lift h (minus d (S (trans hds0 i))) (lift1 (ptrans hds0 
i) v))))).(\lambda (H11: (drop h (minus d (S (trans hds0 i))) x1 
x0)).(ex_intro2 C (\lambda (e2: C).(drop1 (PCons h (minus d (S (trans hds0 
i))) (ptrans hds0 i)) e2 e1)) (\lambda (e2: C).(getl (trans hds0 i) c2 (CHead 
e2 (Bind b) (lift1 (PCons h (minus d (S (trans hds0 i))) (ptrans hds0 i)) 
v)))) x1 (drop1_cons x1 x0 h (minus d (S (trans hds0 i))) H11 e1 (ptrans hds0 
i) H7) H10)))) H9)))))) H6)))) (\lambda (H5: (eq bool (blt (trans hds0 i) d) 
false)).(let H_x0 \def (H c1 x H4 b e1 v i H1) in (let H6 \def H_x0 in 
(ex2_ind C (\lambda (e2: C).(drop1 (ptrans hds0 i) e2 e1)) (\lambda (e2: 
C).(getl (trans hds0 i) x (CHead e2 (Bind b) (lift1 (ptrans hds0 i) v)))) 
(ex2 C (\lambda (e2: C).(drop1 (ptrans hds0 i) e2 e1)) (\lambda (e2: C).(getl 
(plus (trans hds0 i) h) c2 (CHead e2 (Bind b) (lift1 (ptrans hds0 i) v))))) 
(\lambda (x0: C).(\lambda (H7: (drop1 (ptrans hds0 i) x0 e1)).(\lambda (H8: 
(getl (trans hds0 i) x (CHead x0 (Bind b) (lift1 (ptrans hds0 i) v)))).(let 
H9 \def (drop_getl_trans_ge (trans hds0 i) c2 x d h H3 (CHead x0 (Bind b) 
(lift1 (ptrans hds0 i) v)) H8) in (ex_intro2 C (\lambda (e2: C).(drop1 
(ptrans hds0 i) e2 e1)) (\lambda (e2: C).(getl (plus (trans hds0 i) h) c2 
(CHead e2 (Bind b) (lift1 (ptrans hds0 i) v)))) x0 H7 (H9 (bge_le d (trans 
hds0 i) H5))))))) H6)))) x_x)))))) H2))))))))))))))) hds).
(* COMMENTS
Initial nodes: 1674
END *)

