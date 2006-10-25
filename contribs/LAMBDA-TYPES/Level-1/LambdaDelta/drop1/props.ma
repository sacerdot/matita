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

set "baseuri" "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/drop1/props".

include "drop1/defs.ma".

include "drop/props.ma".

include "getl/defs.ma".

theorem drop1_skip_bind:
 \forall (b: B).(\forall (e: C).(\forall (hds: PList).(\forall (c: 
C).(\forall (u: T).((drop1 hds c e) \to (drop1 (Ss hds) (CHead c (Bind b) 
(lift1 hds u)) (CHead e (Bind b) u)))))))
\def
 \lambda (b: B).(\lambda (e: C).(\lambda (hds: PList).(PList_ind (\lambda (p: 
PList).(\forall (c: C).(\forall (u: T).((drop1 p c e) \to (drop1 (Ss p) 
(CHead c (Bind b) (lift1 p u)) (CHead e (Bind b) u)))))) (\lambda (c: 
C).(\lambda (u: T).(\lambda (H: (drop1 PNil c e)).(let H0 \def (match H in 
drop1 return (\lambda (p: PList).(\lambda (c0: C).(\lambda (c1: C).(\lambda 
(_: (drop1 p c0 c1)).((eq PList p PNil) \to ((eq C c0 c) \to ((eq C c1 e) \to 
(drop1 PNil (CHead c (Bind b) u) (CHead e (Bind b) u))))))))) with 
[(drop1_nil c0) \Rightarrow (\lambda (_: (eq PList PNil PNil)).(\lambda (H1: 
(eq C c0 c)).(\lambda (H2: (eq C c0 e)).(eq_ind C c (\lambda (c1: C).((eq C 
c1 e) \to (drop1 PNil (CHead c (Bind b) u) (CHead e (Bind b) u)))) (\lambda 
(H3: (eq C c e)).(eq_ind C e (\lambda (c1: C).(drop1 PNil (CHead c1 (Bind b) 
u) (CHead e (Bind b) u))) (drop1_nil (CHead e (Bind b) u)) c (sym_eq C c e 
H3))) c0 (sym_eq C c0 c H1) H2)))) | (drop1_cons c1 c2 h d H0 c3 hds0 H1) 
\Rightarrow (\lambda (H2: (eq PList (PCons h d hds0) PNil)).(\lambda (H3: (eq 
C c1 c)).(\lambda (H4: (eq C c3 e)).((let H5 \def (eq_ind PList (PCons h d 
hds0) (\lambda (e0: PList).(match e0 in PList return (\lambda (_: 
PList).Prop) with [PNil \Rightarrow False | (PCons _ _ _) \Rightarrow True])) 
I PNil H2) in (False_ind ((eq C c1 c) \to ((eq C c3 e) \to ((drop h d c1 c2) 
\to ((drop1 hds0 c2 c3) \to (drop1 PNil (CHead c (Bind b) u) (CHead e (Bind 
b) u)))))) H5)) H3 H4 H0 H1))))]) in (H0 (refl_equal PList PNil) (refl_equal 
C c) (refl_equal C e)))))) (\lambda (n: nat).(\lambda (n0: nat).(\lambda (p: 
PList).(\lambda (H: ((\forall (c: C).(\forall (u: T).((drop1 p c e) \to 
(drop1 (Ss p) (CHead c (Bind b) (lift1 p u)) (CHead e (Bind b) 
u))))))).(\lambda (c: C).(\lambda (u: T).(\lambda (H0: (drop1 (PCons n n0 p) 
c e)).(let H1 \def (match H0 in drop1 return (\lambda (p0: PList).(\lambda 
(c0: C).(\lambda (c1: C).(\lambda (_: (drop1 p0 c0 c1)).((eq PList p0 (PCons 
n n0 p)) \to ((eq C c0 c) \to ((eq C c1 e) \to (drop1 (PCons n (S n0) (Ss p)) 
(CHead c (Bind b) (lift n n0 (lift1 p u))) (CHead e (Bind b) u))))))))) with 
[(drop1_nil c0) \Rightarrow (\lambda (H1: (eq PList PNil (PCons n n0 
p))).(\lambda (H2: (eq C c0 c)).(\lambda (H3: (eq C c0 e)).((let H4 \def 
(eq_ind PList PNil (\lambda (e0: PList).(match e0 in PList return (\lambda 
(_: PList).Prop) with [PNil \Rightarrow True | (PCons _ _ _) \Rightarrow 
False])) I (PCons n n0 p) H1) in (False_ind ((eq C c0 c) \to ((eq C c0 e) \to 
(drop1 (PCons n (S n0) (Ss p)) (CHead c (Bind b) (lift n n0 (lift1 p u))) 
(CHead e (Bind b) u)))) H4)) H2 H3)))) | (drop1_cons c1 c2 h d H1 c3 hds0 H2) 
\Rightarrow (\lambda (H3: (eq PList (PCons h d hds0) (PCons n n0 
p))).(\lambda (H4: (eq C c1 c)).(\lambda (H5: (eq C c3 e)).((let H6 \def 
(f_equal PList PList (\lambda (e0: PList).(match e0 in PList return (\lambda 
(_: PList).PList) with [PNil \Rightarrow hds0 | (PCons _ _ p0) \Rightarrow 
p0])) (PCons h d hds0) (PCons n n0 p) H3) in ((let H7 \def (f_equal PList nat 
(\lambda (e0: PList).(match e0 in PList return (\lambda (_: PList).nat) with 
[PNil \Rightarrow d | (PCons _ n1 _) \Rightarrow n1])) (PCons h d hds0) 
(PCons n n0 p) H3) in ((let H8 \def (f_equal PList nat (\lambda (e0: 
PList).(match e0 in PList return (\lambda (_: PList).nat) with [PNil 
\Rightarrow h | (PCons n1 _ _) \Rightarrow n1])) (PCons h d hds0) (PCons n n0 
p) H3) in (eq_ind nat n (\lambda (n1: nat).((eq nat d n0) \to ((eq PList hds0 
p) \to ((eq C c1 c) \to ((eq C c3 e) \to ((drop n1 d c1 c2) \to ((drop1 hds0 
c2 c3) \to (drop1 (PCons n (S n0) (Ss p)) (CHead c (Bind b) (lift n n0 (lift1 
p u))) (CHead e (Bind b) u))))))))) (\lambda (H9: (eq nat d n0)).(eq_ind nat 
n0 (\lambda (n1: nat).((eq PList hds0 p) \to ((eq C c1 c) \to ((eq C c3 e) 
\to ((drop n n1 c1 c2) \to ((drop1 hds0 c2 c3) \to (drop1 (PCons n (S n0) (Ss 
p)) (CHead c (Bind b) (lift n n0 (lift1 p u))) (CHead e (Bind b) u)))))))) 
(\lambda (H10: (eq PList hds0 p)).(eq_ind PList p (\lambda (p0: PList).((eq C 
c1 c) \to ((eq C c3 e) \to ((drop n n0 c1 c2) \to ((drop1 p0 c2 c3) \to 
(drop1 (PCons n (S n0) (Ss p)) (CHead c (Bind b) (lift n n0 (lift1 p u))) 
(CHead e (Bind b) u))))))) (\lambda (H11: (eq C c1 c)).(eq_ind C c (\lambda 
(c0: C).((eq C c3 e) \to ((drop n n0 c0 c2) \to ((drop1 p c2 c3) \to (drop1 
(PCons n (S n0) (Ss p)) (CHead c (Bind b) (lift n n0 (lift1 p u))) (CHead e 
(Bind b) u)))))) (\lambda (H12: (eq C c3 e)).(eq_ind C e (\lambda (c0: 
C).((drop n n0 c c2) \to ((drop1 p c2 c0) \to (drop1 (PCons n (S n0) (Ss p)) 
(CHead c (Bind b) (lift n n0 (lift1 p u))) (CHead e (Bind b) u))))) (\lambda 
(H13: (drop n n0 c c2)).(\lambda (H14: (drop1 p c2 e)).(drop1_cons (CHead c 
(Bind b) (lift n n0 (lift1 p u))) (CHead c2 (Bind b) (lift1 p u)) n (S n0) 
(drop_skip_bind n n0 c c2 H13 b (lift1 p u)) (CHead e (Bind b) u) (Ss p) (H 
c2 u H14)))) c3 (sym_eq C c3 e H12))) c1 (sym_eq C c1 c H11))) hds0 (sym_eq 
PList hds0 p H10))) d (sym_eq nat d n0 H9))) h (sym_eq nat h n H8))) H7)) 
H6)) H4 H5 H1 H2))))]) in (H1 (refl_equal PList (PCons n n0 p)) (refl_equal C 
c) (refl_equal C e)))))))))) hds))).

theorem drop1_cons_tail:
 \forall (c2: C).(\forall (c3: C).(\forall (h: nat).(\forall (d: nat).((drop 
h d c2 c3) \to (\forall (hds: PList).(\forall (c1: C).((drop1 hds c1 c2) \to 
(drop1 (PConsTail hds h d) c1 c3))))))))
\def
 \lambda (c2: C).(\lambda (c3: C).(\lambda (h: nat).(\lambda (d: 
nat).(\lambda (H: (drop h d c2 c3)).(\lambda (hds: PList).(PList_ind (\lambda 
(p: PList).(\forall (c1: C).((drop1 p c1 c2) \to (drop1 (PConsTail p h d) c1 
c3)))) (\lambda (c1: C).(\lambda (H0: (drop1 PNil c1 c2)).(let H1 \def (match 
H0 in drop1 return (\lambda (p: PList).(\lambda (c: C).(\lambda (c0: 
C).(\lambda (_: (drop1 p c c0)).((eq PList p PNil) \to ((eq C c c1) \to ((eq 
C c0 c2) \to (drop1 (PCons h d PNil) c1 c3)))))))) with [(drop1_nil c) 
\Rightarrow (\lambda (_: (eq PList PNil PNil)).(\lambda (H2: (eq C c 
c1)).(\lambda (H3: (eq C c c2)).(eq_ind C c1 (\lambda (c0: C).((eq C c0 c2) 
\to (drop1 (PCons h d PNil) c1 c3))) (\lambda (H4: (eq C c1 c2)).(eq_ind C c2 
(\lambda (c0: C).(drop1 (PCons h d PNil) c0 c3)) (drop1_cons c2 c3 h d H c3 
PNil (drop1_nil c3)) c1 (sym_eq C c1 c2 H4))) c (sym_eq C c c1 H2) H3)))) | 
(drop1_cons c0 c4 h0 d0 H1 c5 hds0 H2) \Rightarrow (\lambda (H3: (eq PList 
(PCons h0 d0 hds0) PNil)).(\lambda (H4: (eq C c0 c1)).(\lambda (H5: (eq C c5 
c2)).((let H6 \def (eq_ind PList (PCons h0 d0 hds0) (\lambda (e: 
PList).(match e in PList return (\lambda (_: PList).Prop) with [PNil 
\Rightarrow False | (PCons _ _ _) \Rightarrow True])) I PNil H3) in 
(False_ind ((eq C c0 c1) \to ((eq C c5 c2) \to ((drop h0 d0 c0 c4) \to 
((drop1 hds0 c4 c5) \to (drop1 (PCons h d PNil) c1 c3))))) H6)) H4 H5 H1 
H2))))]) in (H1 (refl_equal PList PNil) (refl_equal C c1) (refl_equal C 
c2))))) (\lambda (n: nat).(\lambda (n0: nat).(\lambda (p: PList).(\lambda 
(H0: ((\forall (c1: C).((drop1 p c1 c2) \to (drop1 (PConsTail p h d) c1 
c3))))).(\lambda (c1: C).(\lambda (H1: (drop1 (PCons n n0 p) c1 c2)).(let H2 
\def (match H1 in drop1 return (\lambda (p0: PList).(\lambda (c: C).(\lambda 
(c0: C).(\lambda (_: (drop1 p0 c c0)).((eq PList p0 (PCons n n0 p)) \to ((eq 
C c c1) \to ((eq C c0 c2) \to (drop1 (PCons n n0 (PConsTail p h d)) c1 
c3)))))))) with [(drop1_nil c) \Rightarrow (\lambda (H2: (eq PList PNil 
(PCons n n0 p))).(\lambda (H3: (eq C c c1)).(\lambda (H4: (eq C c c2)).((let 
H5 \def (eq_ind PList PNil (\lambda (e: PList).(match e in PList return 
(\lambda (_: PList).Prop) with [PNil \Rightarrow True | (PCons _ _ _) 
\Rightarrow False])) I (PCons n n0 p) H2) in (False_ind ((eq C c c1) \to ((eq 
C c c2) \to (drop1 (PCons n n0 (PConsTail p h d)) c1 c3))) H5)) H3 H4)))) | 
(drop1_cons c0 c4 h0 d0 H2 c5 hds0 H3) \Rightarrow (\lambda (H4: (eq PList 
(PCons h0 d0 hds0) (PCons n n0 p))).(\lambda (H5: (eq C c0 c1)).(\lambda (H6: 
(eq C c5 c2)).((let H7 \def (f_equal PList PList (\lambda (e: PList).(match e 
in PList return (\lambda (_: PList).PList) with [PNil \Rightarrow hds0 | 
(PCons _ _ p0) \Rightarrow p0])) (PCons h0 d0 hds0) (PCons n n0 p) H4) in 
((let H8 \def (f_equal PList nat (\lambda (e: PList).(match e in PList return 
(\lambda (_: PList).nat) with [PNil \Rightarrow d0 | (PCons _ n1 _) 
\Rightarrow n1])) (PCons h0 d0 hds0) (PCons n n0 p) H4) in ((let H9 \def 
(f_equal PList nat (\lambda (e: PList).(match e in PList return (\lambda (_: 
PList).nat) with [PNil \Rightarrow h0 | (PCons n1 _ _) \Rightarrow n1])) 
(PCons h0 d0 hds0) (PCons n n0 p) H4) in (eq_ind nat n (\lambda (n1: 
nat).((eq nat d0 n0) \to ((eq PList hds0 p) \to ((eq C c0 c1) \to ((eq C c5 
c2) \to ((drop n1 d0 c0 c4) \to ((drop1 hds0 c4 c5) \to (drop1 (PCons n n0 
(PConsTail p h d)) c1 c3)))))))) (\lambda (H10: (eq nat d0 n0)).(eq_ind nat 
n0 (\lambda (n1: nat).((eq PList hds0 p) \to ((eq C c0 c1) \to ((eq C c5 c2) 
\to ((drop n n1 c0 c4) \to ((drop1 hds0 c4 c5) \to (drop1 (PCons n n0 
(PConsTail p h d)) c1 c3))))))) (\lambda (H11: (eq PList hds0 p)).(eq_ind 
PList p (\lambda (p0: PList).((eq C c0 c1) \to ((eq C c5 c2) \to ((drop n n0 
c0 c4) \to ((drop1 p0 c4 c5) \to (drop1 (PCons n n0 (PConsTail p h d)) c1 
c3)))))) (\lambda (H12: (eq C c0 c1)).(eq_ind C c1 (\lambda (c: C).((eq C c5 
c2) \to ((drop n n0 c c4) \to ((drop1 p c4 c5) \to (drop1 (PCons n n0 
(PConsTail p h d)) c1 c3))))) (\lambda (H13: (eq C c5 c2)).(eq_ind C c2 
(\lambda (c: C).((drop n n0 c1 c4) \to ((drop1 p c4 c) \to (drop1 (PCons n n0 
(PConsTail p h d)) c1 c3)))) (\lambda (H14: (drop n n0 c1 c4)).(\lambda (H15: 
(drop1 p c4 c2)).(drop1_cons c1 c4 n n0 H14 c3 (PConsTail p h d) (H0 c4 
H15)))) c5 (sym_eq C c5 c2 H13))) c0 (sym_eq C c0 c1 H12))) hds0 (sym_eq 
PList hds0 p H11))) d0 (sym_eq nat d0 n0 H10))) h0 (sym_eq nat h0 n H9))) 
H8)) H7)) H5 H6 H2 H3))))]) in (H2 (refl_equal PList (PCons n n0 p)) 
(refl_equal C c1) (refl_equal C c2))))))))) hds)))))).

