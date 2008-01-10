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



include "nf2/props.ma".

include "drop1/defs.ma".

theorem nf2_lift1:
 \forall (e: C).(\forall (hds: PList).(\forall (c: C).(\forall (t: T).((drop1 
hds c e) \to ((nf2 e t) \to (nf2 c (lift1 hds t)))))))
\def
 \lambda (e: C).(\lambda (hds: PList).(PList_ind (\lambda (p: PList).(\forall 
(c: C).(\forall (t: T).((drop1 p c e) \to ((nf2 e t) \to (nf2 c (lift1 p 
t))))))) (\lambda (c: C).(\lambda (t: T).(\lambda (H: (drop1 PNil c 
e)).(\lambda (H0: (nf2 e t)).(let H1 \def (match H in drop1 return (\lambda 
(p: PList).(\lambda (c0: C).(\lambda (c1: C).(\lambda (_: (drop1 p c0 
c1)).((eq PList p PNil) \to ((eq C c0 c) \to ((eq C c1 e) \to (nf2 c 
t)))))))) with [(drop1_nil c0) \Rightarrow (\lambda (_: (eq PList PNil 
PNil)).(\lambda (H2: (eq C c0 c)).(\lambda (H3: (eq C c0 e)).(eq_ind C c 
(\lambda (c1: C).((eq C c1 e) \to (nf2 c t))) (\lambda (H4: (eq C c 
e)).(eq_ind C e (\lambda (c1: C).(nf2 c1 t)) H0 c (sym_eq C c e H4))) c0 
(sym_eq C c0 c H2) H3)))) | (drop1_cons c1 c2 h d H1 c3 hds0 H2) \Rightarrow 
(\lambda (H3: (eq PList (PCons h d hds0) PNil)).(\lambda (H4: (eq C c1 
c)).(\lambda (H5: (eq C c3 e)).((let H6 \def (eq_ind PList (PCons h d hds0) 
(\lambda (e0: PList).(match e0 in PList return (\lambda (_: PList).Prop) with 
[PNil \Rightarrow False | (PCons _ _ _) \Rightarrow True])) I PNil H3) in 
(False_ind ((eq C c1 c) \to ((eq C c3 e) \to ((drop h d c1 c2) \to ((drop1 
hds0 c2 c3) \to (nf2 c t))))) H6)) H4 H5 H1 H2))))]) in (H1 (refl_equal PList 
PNil) (refl_equal C c) (refl_equal C e))))))) (\lambda (n: nat).(\lambda (n0: 
nat).(\lambda (p: PList).(\lambda (H: ((\forall (c: C).(\forall (t: 
T).((drop1 p c e) \to ((nf2 e t) \to (nf2 c (lift1 p t)))))))).(\lambda (c: 
C).(\lambda (t: T).(\lambda (H0: (drop1 (PCons n n0 p) c e)).(\lambda (H1: 
(nf2 e t)).(let H2 \def (match H0 in drop1 return (\lambda (p0: 
PList).(\lambda (c0: C).(\lambda (c1: C).(\lambda (_: (drop1 p0 c0 c1)).((eq 
PList p0 (PCons n n0 p)) \to ((eq C c0 c) \to ((eq C c1 e) \to (nf2 c (lift n 
n0 (lift1 p t)))))))))) with [(drop1_nil c0) \Rightarrow (\lambda (H2: (eq 
PList PNil (PCons n n0 p))).(\lambda (H3: (eq C c0 c)).(\lambda (H4: (eq C c0 
e)).((let H5 \def (eq_ind PList PNil (\lambda (e0: PList).(match e0 in PList 
return (\lambda (_: PList).Prop) with [PNil \Rightarrow True | (PCons _ _ _) 
\Rightarrow False])) I (PCons n n0 p) H2) in (False_ind ((eq C c0 c) \to ((eq 
C c0 e) \to (nf2 c (lift n n0 (lift1 p t))))) H5)) H3 H4)))) | (drop1_cons c1 
c2 h d H2 c3 hds0 H3) \Rightarrow (\lambda (H4: (eq PList (PCons h d hds0) 
(PCons n n0 p))).(\lambda (H5: (eq C c1 c)).(\lambda (H6: (eq C c3 e)).((let 
H7 \def (f_equal PList PList (\lambda (e0: PList).(match e0 in PList return 
(\lambda (_: PList).PList) with [PNil \Rightarrow hds0 | (PCons _ _ p0) 
\Rightarrow p0])) (PCons h d hds0) (PCons n n0 p) H4) in ((let H8 \def 
(f_equal PList nat (\lambda (e0: PList).(match e0 in PList return (\lambda 
(_: PList).nat) with [PNil \Rightarrow d | (PCons _ n1 _) \Rightarrow n1])) 
(PCons h d hds0) (PCons n n0 p) H4) in ((let H9 \def (f_equal PList nat 
(\lambda (e0: PList).(match e0 in PList return (\lambda (_: PList).nat) with 
[PNil \Rightarrow h | (PCons n1 _ _) \Rightarrow n1])) (PCons h d hds0) 
(PCons n n0 p) H4) in (eq_ind nat n (\lambda (n1: nat).((eq nat d n0) \to 
((eq PList hds0 p) \to ((eq C c1 c) \to ((eq C c3 e) \to ((drop n1 d c1 c2) 
\to ((drop1 hds0 c2 c3) \to (nf2 c (lift n n0 (lift1 p t)))))))))) (\lambda 
(H10: (eq nat d n0)).(eq_ind nat n0 (\lambda (n1: nat).((eq PList hds0 p) \to 
((eq C c1 c) \to ((eq C c3 e) \to ((drop n n1 c1 c2) \to ((drop1 hds0 c2 c3) 
\to (nf2 c (lift n n0 (lift1 p t))))))))) (\lambda (H11: (eq PList hds0 
p)).(eq_ind PList p (\lambda (p0: PList).((eq C c1 c) \to ((eq C c3 e) \to 
((drop n n0 c1 c2) \to ((drop1 p0 c2 c3) \to (nf2 c (lift n n0 (lift1 p 
t)))))))) (\lambda (H12: (eq C c1 c)).(eq_ind C c (\lambda (c0: C).((eq C c3 
e) \to ((drop n n0 c0 c2) \to ((drop1 p c2 c3) \to (nf2 c (lift n n0 (lift1 p 
t))))))) (\lambda (H13: (eq C c3 e)).(eq_ind C e (\lambda (c0: C).((drop n n0 
c c2) \to ((drop1 p c2 c0) \to (nf2 c (lift n n0 (lift1 p t)))))) (\lambda 
(H14: (drop n n0 c c2)).(\lambda (H15: (drop1 p c2 e)).(nf2_lift c2 (lift1 p 
t) (H c2 t H15 H1) c n n0 H14))) c3 (sym_eq C c3 e H13))) c1 (sym_eq C c1 c 
H12))) hds0 (sym_eq PList hds0 p H11))) d (sym_eq nat d n0 H10))) h (sym_eq 
nat h n H9))) H8)) H7)) H5 H6 H2 H3))))]) in (H2 (refl_equal PList (PCons n 
n0 p)) (refl_equal C c) (refl_equal C e))))))))))) hds)).

