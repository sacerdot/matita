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

set "baseuri" "cic:/matita/LAMBDA-TYPES/LambdaDelta-1/drop1/getl".

include "drop1/defs.ma".

include "getl/drop.ma".

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
i c1 (CHead e1 (Bind b) v))).(let H1 \def (match H in drop1 return (\lambda 
(p: PList).(\lambda (c: C).(\lambda (c0: C).(\lambda (_: (drop1 p c c0)).((eq 
PList p PNil) \to ((eq C c c2) \to ((eq C c0 c1) \to (ex2 C (\lambda (e2: 
C).(drop1 PNil e2 e1)) (\lambda (e2: C).(getl i c2 (CHead e2 (Bind b) 
v))))))))))) with [(drop1_nil c) \Rightarrow (\lambda (_: (eq PList PNil 
PNil)).(\lambda (H2: (eq C c c2)).(\lambda (H3: (eq C c c1)).(eq_ind C c2 
(\lambda (c0: C).((eq C c0 c1) \to (ex2 C (\lambda (e2: C).(drop1 PNil e2 
e1)) (\lambda (e2: C).(getl i c2 (CHead e2 (Bind b) v)))))) (\lambda (H4: (eq 
C c2 c1)).(eq_ind C c1 (\lambda (c0: C).(ex2 C (\lambda (e2: C).(drop1 PNil 
e2 e1)) (\lambda (e2: C).(getl i c0 (CHead e2 (Bind b) v))))) (ex_intro2 C 
(\lambda (e2: C).(drop1 PNil e2 e1)) (\lambda (e2: C).(getl i c1 (CHead e2 
(Bind b) v))) e1 (drop1_nil e1) H0) c2 (sym_eq C c2 c1 H4))) c (sym_eq C c c2 
H2) H3)))) | (drop1_cons c0 c3 h d H1 c4 hds0 H2) \Rightarrow (\lambda (H3: 
(eq PList (PCons h d hds0) PNil)).(\lambda (H4: (eq C c0 c2)).(\lambda (H5: 
(eq C c4 c1)).((let H6 \def (eq_ind PList (PCons h d hds0) (\lambda (e: 
PList).(match e in PList return (\lambda (_: PList).Prop) with [PNil 
\Rightarrow False | (PCons _ _ _) \Rightarrow True])) I PNil H3) in 
(False_ind ((eq C c0 c2) \to ((eq C c4 c1) \to ((drop h d c0 c3) \to ((drop1 
hds0 c3 c4) \to (ex2 C (\lambda (e2: C).(drop1 PNil e2 e1)) (\lambda (e2: 
C).(getl i c2 (CHead e2 (Bind b) v)))))))) H6)) H4 H5 H1 H2))))]) in (H1 
(refl_equal PList PNil) (refl_equal C c2) (refl_equal C c1))))))))))) 
(\lambda (h: nat).(\lambda (d: nat).(\lambda (hds0: PList).(\lambda (H: 
((\forall (c1: C).(\forall (c2: C).((drop1 hds0 c2 c1) \to (\forall (b: 
B).(\forall (e1: C).(\forall (v: T).(\forall (i: nat).((getl i c1 (CHead e1 
(Bind b) v)) \to (ex2 C (\lambda (e2: C).(drop1 (ptrans hds0 i) e2 e1)) 
(\lambda (e2: C).(getl (trans hds0 i) c2 (CHead e2 (Bind b) (lift1 (ptrans 
hds0 i) v))))))))))))))).(\lambda (c1: C).(\lambda (c2: C).(\lambda (H0: 
(drop1 (PCons h d hds0) c2 c1)).(\lambda (b: B).(\lambda (e1: C).(\lambda (v: 
T).(\lambda (i: nat).(\lambda (H1: (getl i c1 (CHead e1 (Bind b) v))).(let H2 
\def (match H0 in drop1 return (\lambda (p: PList).(\lambda (c: C).(\lambda 
(c0: C).(\lambda (_: (drop1 p c c0)).((eq PList p (PCons h d hds0)) \to ((eq 
C c c2) \to ((eq C c0 c1) \to (ex2 C (\lambda (e2: C).(drop1 (match (blt 
(trans hds0 i) d) with [true \Rightarrow (PCons h (minus d (S (trans hds0 
i))) (ptrans hds0 i)) | false \Rightarrow (ptrans hds0 i)]) e2 e1)) (\lambda 
(e2: C).(getl (match (blt (trans hds0 i) d) with [true \Rightarrow (trans 
hds0 i) | false \Rightarrow (plus (trans hds0 i) h)]) c2 (CHead e2 (Bind b) 
(lift1 (match (blt (trans hds0 i) d) with [true \Rightarrow (PCons h (minus d 
(S (trans hds0 i))) (ptrans hds0 i)) | false \Rightarrow (ptrans hds0 i)]) 
v)))))))))))) with [(drop1_nil c) \Rightarrow (\lambda (H2: (eq PList PNil 
(PCons h d hds0))).(\lambda (H3: (eq C c c2)).(\lambda (H4: (eq C c 
c1)).((let H5 \def (eq_ind PList PNil (\lambda (e: PList).(match e in PList 
return (\lambda (_: PList).Prop) with [PNil \Rightarrow True | (PCons _ _ _) 
\Rightarrow False])) I (PCons h d hds0) H2) in (False_ind ((eq C c c2) \to 
((eq C c c1) \to (ex2 C (\lambda (e2: C).(drop1 (match (blt (trans hds0 i) d) 
with [true \Rightarrow (PCons h (minus d (S (trans hds0 i))) (ptrans hds0 i)) 
| false \Rightarrow (ptrans hds0 i)]) e2 e1)) (\lambda (e2: C).(getl (match 
(blt (trans hds0 i) d) with [true \Rightarrow (trans hds0 i) | false 
\Rightarrow (plus (trans hds0 i) h)]) c2 (CHead e2 (Bind b) (lift1 (match 
(blt (trans hds0 i) d) with [true \Rightarrow (PCons h (minus d (S (trans 
hds0 i))) (ptrans hds0 i)) | false \Rightarrow (ptrans hds0 i)]) v))))))) 
H5)) H3 H4)))) | (drop1_cons c0 c3 h0 d0 H2 c4 hds1 H3) \Rightarrow (\lambda 
(H4: (eq PList (PCons h0 d0 hds1) (PCons h d hds0))).(\lambda (H5: (eq C c0 
c2)).(\lambda (H6: (eq C c4 c1)).((let H7 \def (f_equal PList PList (\lambda 
(e: PList).(match e in PList return (\lambda (_: PList).PList) with [PNil 
\Rightarrow hds1 | (PCons _ _ p) \Rightarrow p])) (PCons h0 d0 hds1) (PCons h 
d hds0) H4) in ((let H8 \def (f_equal PList nat (\lambda (e: PList).(match e 
in PList return (\lambda (_: PList).nat) with [PNil \Rightarrow d0 | (PCons _ 
n _) \Rightarrow n])) (PCons h0 d0 hds1) (PCons h d hds0) H4) in ((let H9 
\def (f_equal PList nat (\lambda (e: PList).(match e in PList return (\lambda 
(_: PList).nat) with [PNil \Rightarrow h0 | (PCons n _ _) \Rightarrow n])) 
(PCons h0 d0 hds1) (PCons h d hds0) H4) in (eq_ind nat h (\lambda (n: 
nat).((eq nat d0 d) \to ((eq PList hds1 hds0) \to ((eq C c0 c2) \to ((eq C c4 
c1) \to ((drop n d0 c0 c3) \to ((drop1 hds1 c3 c4) \to (ex2 C (\lambda (e2: 
C).(drop1 (match (blt (trans hds0 i) d) with [true \Rightarrow (PCons h 
(minus d (S (trans hds0 i))) (ptrans hds0 i)) | false \Rightarrow (ptrans 
hds0 i)]) e2 e1)) (\lambda (e2: C).(getl (match (blt (trans hds0 i) d) with 
[true \Rightarrow (trans hds0 i) | false \Rightarrow (plus (trans hds0 i) 
h)]) c2 (CHead e2 (Bind b) (lift1 (match (blt (trans hds0 i) d) with [true 
\Rightarrow (PCons h (minus d (S (trans hds0 i))) (ptrans hds0 i)) | false 
\Rightarrow (ptrans hds0 i)]) v)))))))))))) (\lambda (H10: (eq nat d0 
d)).(eq_ind nat d (\lambda (n: nat).((eq PList hds1 hds0) \to ((eq C c0 c2) 
\to ((eq C c4 c1) \to ((drop h n c0 c3) \to ((drop1 hds1 c3 c4) \to (ex2 C 
(\lambda (e2: C).(drop1 (match (blt (trans hds0 i) d) with [true \Rightarrow 
(PCons h (minus d (S (trans hds0 i))) (ptrans hds0 i)) | false \Rightarrow 
(ptrans hds0 i)]) e2 e1)) (\lambda (e2: C).(getl (match (blt (trans hds0 i) 
d) with [true \Rightarrow (trans hds0 i) | false \Rightarrow (plus (trans 
hds0 i) h)]) c2 (CHead e2 (Bind b) (lift1 (match (blt (trans hds0 i) d) with 
[true \Rightarrow (PCons h (minus d (S (trans hds0 i))) (ptrans hds0 i)) | 
false \Rightarrow (ptrans hds0 i)]) v))))))))))) (\lambda (H11: (eq PList 
hds1 hds0)).(eq_ind PList hds0 (\lambda (p: PList).((eq C c0 c2) \to ((eq C 
c4 c1) \to ((drop h d c0 c3) \to ((drop1 p c3 c4) \to (ex2 C (\lambda (e2: 
C).(drop1 (match (blt (trans hds0 i) d) with [true \Rightarrow (PCons h 
(minus d (S (trans hds0 i))) (ptrans hds0 i)) | false \Rightarrow (ptrans 
hds0 i)]) e2 e1)) (\lambda (e2: C).(getl (match (blt (trans hds0 i) d) with 
[true \Rightarrow (trans hds0 i) | false \Rightarrow (plus (trans hds0 i) 
h)]) c2 (CHead e2 (Bind b) (lift1 (match (blt (trans hds0 i) d) with [true 
\Rightarrow (PCons h (minus d (S (trans hds0 i))) (ptrans hds0 i)) | false 
\Rightarrow (ptrans hds0 i)]) v)))))))))) (\lambda (H12: (eq C c0 
c2)).(eq_ind C c2 (\lambda (c: C).((eq C c4 c1) \to ((drop h d c c3) \to 
((drop1 hds0 c3 c4) \to (ex2 C (\lambda (e2: C).(drop1 (match (blt (trans 
hds0 i) d) with [true \Rightarrow (PCons h (minus d (S (trans hds0 i))) 
(ptrans hds0 i)) | false \Rightarrow (ptrans hds0 i)]) e2 e1)) (\lambda (e2: 
C).(getl (match (blt (trans hds0 i) d) with [true \Rightarrow (trans hds0 i) 
| false \Rightarrow (plus (trans hds0 i) h)]) c2 (CHead e2 (Bind b) (lift1 
(match (blt (trans hds0 i) d) with [true \Rightarrow (PCons h (minus d (S 
(trans hds0 i))) (ptrans hds0 i)) | false \Rightarrow (ptrans hds0 i)]) 
v))))))))) (\lambda (H13: (eq C c4 c1)).(eq_ind C c1 (\lambda (c: C).((drop h 
d c2 c3) \to ((drop1 hds0 c3 c) \to (ex2 C (\lambda (e2: C).(drop1 (match 
(blt (trans hds0 i) d) with [true \Rightarrow (PCons h (minus d (S (trans 
hds0 i))) (ptrans hds0 i)) | false \Rightarrow (ptrans hds0 i)]) e2 e1)) 
(\lambda (e2: C).(getl (match (blt (trans hds0 i) d) with [true \Rightarrow 
(trans hds0 i) | false \Rightarrow (plus (trans hds0 i) h)]) c2 (CHead e2 
(Bind b) (lift1 (match (blt (trans hds0 i) d) with [true \Rightarrow (PCons h 
(minus d (S (trans hds0 i))) (ptrans hds0 i)) | false \Rightarrow (ptrans 
hds0 i)]) v)))))))) (\lambda (H14: (drop h d c2 c3)).(\lambda (H15: (drop1 
hds0 c3 c1)).(xinduction bool (blt (trans hds0 i) d) (\lambda (b0: bool).(ex2 
C (\lambda (e2: C).(drop1 (match b0 with [true \Rightarrow (PCons h (minus d 
(S (trans hds0 i))) (ptrans hds0 i)) | false \Rightarrow (ptrans hds0 i)]) e2 
e1)) (\lambda (e2: C).(getl (match b0 with [true \Rightarrow (trans hds0 i) | 
false \Rightarrow (plus (trans hds0 i) h)]) c2 (CHead e2 (Bind b) (lift1 
(match b0 with [true \Rightarrow (PCons h (minus d (S (trans hds0 i))) 
(ptrans hds0 i)) | false \Rightarrow (ptrans hds0 i)]) v)))))) (\lambda (x_x: 
bool).(bool_ind (\lambda (b0: bool).((eq bool (blt (trans hds0 i) d) b0) \to 
(ex2 C (\lambda (e2: C).(drop1 (match b0 with [true \Rightarrow (PCons h 
(minus d (S (trans hds0 i))) (ptrans hds0 i)) | false \Rightarrow (ptrans 
hds0 i)]) e2 e1)) (\lambda (e2: C).(getl (match b0 with [true \Rightarrow 
(trans hds0 i) | false \Rightarrow (plus (trans hds0 i) h)]) c2 (CHead e2 
(Bind b) (lift1 (match b0 with [true \Rightarrow (PCons h (minus d (S (trans 
hds0 i))) (ptrans hds0 i)) | false \Rightarrow (ptrans hds0 i)]) v))))))) 
(\lambda (H16: (eq bool (blt (trans hds0 i) d) true)).(let H_x \def (H c1 c3 
H15 b e1 v i H1) in (let H17 \def H_x in (ex2_ind C (\lambda (e2: C).(drop1 
(ptrans hds0 i) e2 e1)) (\lambda (e2: C).(getl (trans hds0 i) c3 (CHead e2 
(Bind b) (lift1 (ptrans hds0 i) v)))) (ex2 C (\lambda (e2: C).(drop1 (PCons h 
(minus d (S (trans hds0 i))) (ptrans hds0 i)) e2 e1)) (\lambda (e2: C).(getl 
(trans hds0 i) c2 (CHead e2 (Bind b) (lift1 (PCons h (minus d (S (trans hds0 
i))) (ptrans hds0 i)) v))))) (\lambda (x: C).(\lambda (H18: (drop1 (ptrans 
hds0 i) x e1)).(\lambda (H19: (getl (trans hds0 i) c3 (CHead x (Bind b) 
(lift1 (ptrans hds0 i) v)))).(let H_x0 \def (drop_getl_trans_lt (trans hds0 
i) d (le_S_n (S (trans hds0 i)) d (lt_le_S (S (trans hds0 i)) (S d) (blt_lt 
(S d) (S (trans hds0 i)) H16))) c2 c3 h H14 b x (lift1 (ptrans hds0 i) v) 
H19) in (let H20 \def H_x0 in (ex2_ind C (\lambda (e2: C).(getl (trans hds0 
i) c2 (CHead e2 (Bind b) (lift h (minus d (S (trans hds0 i))) (lift1 (ptrans 
hds0 i) v))))) (\lambda (e2: C).(drop h (minus d (S (trans hds0 i))) e2 x)) 
(ex2 C (\lambda (e2: C).(drop1 (PCons h (minus d (S (trans hds0 i))) (ptrans 
hds0 i)) e2 e1)) (\lambda (e2: C).(getl (trans hds0 i) c2 (CHead e2 (Bind b) 
(lift1 (PCons h (minus d (S (trans hds0 i))) (ptrans hds0 i)) v))))) (\lambda 
(x0: C).(\lambda (H21: (getl (trans hds0 i) c2 (CHead x0 (Bind b) (lift h 
(minus d (S (trans hds0 i))) (lift1 (ptrans hds0 i) v))))).(\lambda (H22: 
(drop h (minus d (S (trans hds0 i))) x0 x)).(ex_intro2 C (\lambda (e2: 
C).(drop1 (PCons h (minus d (S (trans hds0 i))) (ptrans hds0 i)) e2 e1)) 
(\lambda (e2: C).(getl (trans hds0 i) c2 (CHead e2 (Bind b) (lift1 (PCons h 
(minus d (S (trans hds0 i))) (ptrans hds0 i)) v)))) x0 (drop1_cons x0 x h 
(minus d (S (trans hds0 i))) H22 e1 (ptrans hds0 i) H18) H21)))) H20)))))) 
H17)))) (\lambda (H16: (eq bool (blt (trans hds0 i) d) false)).(let H_x \def 
(H c1 c3 H15 b e1 v i H1) in (let H17 \def H_x in (ex2_ind C (\lambda (e2: 
C).(drop1 (ptrans hds0 i) e2 e1)) (\lambda (e2: C).(getl (trans hds0 i) c3 
(CHead e2 (Bind b) (lift1 (ptrans hds0 i) v)))) (ex2 C (\lambda (e2: 
C).(drop1 (ptrans hds0 i) e2 e1)) (\lambda (e2: C).(getl (plus (trans hds0 i) 
h) c2 (CHead e2 (Bind b) (lift1 (ptrans hds0 i) v))))) (\lambda (x: 
C).(\lambda (H18: (drop1 (ptrans hds0 i) x e1)).(\lambda (H19: (getl (trans 
hds0 i) c3 (CHead x (Bind b) (lift1 (ptrans hds0 i) v)))).(let H20 \def 
(drop_getl_trans_ge (trans hds0 i) c2 c3 d h H14 (CHead x (Bind b) (lift1 
(ptrans hds0 i) v)) H19) in (ex_intro2 C (\lambda (e2: C).(drop1 (ptrans hds0 
i) e2 e1)) (\lambda (e2: C).(getl (plus (trans hds0 i) h) c2 (CHead e2 (Bind 
b) (lift1 (ptrans hds0 i) v)))) x H18 (H20 (bge_le d (trans hds0 i) 
H16))))))) H17)))) x_x))))) c4 (sym_eq C c4 c1 H13))) c0 (sym_eq C c0 c2 
H12))) hds1 (sym_eq PList hds1 hds0 H11))) d0 (sym_eq nat d0 d H10))) h0 
(sym_eq nat h0 h H9))) H8)) H7)) H5 H6 H2 H3))))]) in (H2 (refl_equal PList 
(PCons h d hds0)) (refl_equal C c2) (refl_equal C c1))))))))))))))) hds).

