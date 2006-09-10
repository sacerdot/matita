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

set "baseuri" "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/arity/lift1".

include "arity/props.ma".

include "drop1/defs.ma".

theorem arity_lift1:
 \forall (g: G).(\forall (a: A).(\forall (c2: C).(\forall (hds: 
PList).(\forall (c1: C).(\forall (t: T).((drop1 hds c1 c2) \to ((arity g c2 t 
a) \to (arity g c1 (lift1 hds t) a))))))))
\def
 \lambda (g: G).(\lambda (a: A).(\lambda (c2: C).(\lambda (hds: 
PList).(PList_ind (\lambda (p: PList).(\forall (c1: C).(\forall (t: 
T).((drop1 p c1 c2) \to ((arity g c2 t a) \to (arity g c1 (lift1 p t) a)))))) 
(\lambda (c1: C).(\lambda (t: T).(\lambda (H: (drop1 PNil c1 c2)).(\lambda 
(H0: (arity g c2 t a)).(let H1 \def (match H in drop1 return (\lambda (p: 
PList).(\lambda (c: C).(\lambda (c0: C).(\lambda (_: (drop1 p c c0)).((eq 
PList p PNil) \to ((eq C c c1) \to ((eq C c0 c2) \to (arity g c1 t a)))))))) 
with [(drop1_nil c) \Rightarrow (\lambda (_: (eq PList PNil PNil)).(\lambda 
(H2: (eq C c c1)).(\lambda (H3: (eq C c c2)).(eq_ind C c1 (\lambda (c0: 
C).((eq C c0 c2) \to (arity g c1 t a))) (\lambda (H4: (eq C c1 c2)).(eq_ind C 
c2 (\lambda (c0: C).(arity g c0 t a)) H0 c1 (sym_eq C c1 c2 H4))) c (sym_eq C 
c c1 H2) H3)))) | (drop1_cons c0 c3 h d H1 c4 hds0 H2) \Rightarrow (\lambda 
(H3: (eq PList (PCons h d hds0) PNil)).(\lambda (H4: (eq C c0 c1)).(\lambda 
(H5: (eq C c4 c2)).((let H6 \def (eq_ind PList (PCons h d hds0) (\lambda (e: 
PList).(match e in PList return (\lambda (_: PList).Prop) with [PNil 
\Rightarrow False | (PCons _ _ _) \Rightarrow True])) I PNil H3) in 
(False_ind ((eq C c0 c1) \to ((eq C c4 c2) \to ((drop h d c0 c3) \to ((drop1 
hds0 c3 c4) \to (arity g c1 t a))))) H6)) H4 H5 H1 H2))))]) in (H1 
(refl_equal PList PNil) (refl_equal C c1) (refl_equal C c2))))))) (\lambda 
(n: nat).(\lambda (n0: nat).(\lambda (p: PList).(\lambda (H: ((\forall (c1: 
C).(\forall (t: T).((drop1 p c1 c2) \to ((arity g c2 t a) \to (arity g c1 
(lift1 p t) a))))))).(\lambda (c1: C).(\lambda (t: T).(\lambda (H0: (drop1 
(PCons n n0 p) c1 c2)).(\lambda (H1: (arity g c2 t a)).(let H2 \def (match H0 
in drop1 return (\lambda (p0: PList).(\lambda (c: C).(\lambda (c0: 
C).(\lambda (_: (drop1 p0 c c0)).((eq PList p0 (PCons n n0 p)) \to ((eq C c 
c1) \to ((eq C c0 c2) \to (arity g c1 (lift n n0 (lift1 p t)) a)))))))) with 
[(drop1_nil c) \Rightarrow (\lambda (H2: (eq PList PNil (PCons n n0 
p))).(\lambda (H3: (eq C c c1)).(\lambda (H4: (eq C c c2)).((let H5 \def 
(eq_ind PList PNil (\lambda (e: PList).(match e in PList return (\lambda (_: 
PList).Prop) with [PNil \Rightarrow True | (PCons _ _ _) \Rightarrow False])) 
I (PCons n n0 p) H2) in (False_ind ((eq C c c1) \to ((eq C c c2) \to (arity g 
c1 (lift n n0 (lift1 p t)) a))) H5)) H3 H4)))) | (drop1_cons c0 c3 h d H2 c4 
hds0 H3) \Rightarrow (\lambda (H4: (eq PList (PCons h d hds0) (PCons n n0 
p))).(\lambda (H5: (eq C c0 c1)).(\lambda (H6: (eq C c4 c2)).((let H7 \def 
(f_equal PList PList (\lambda (e: PList).(match e in PList return (\lambda 
(_: PList).PList) with [PNil \Rightarrow hds0 | (PCons _ _ p0) \Rightarrow 
p0])) (PCons h d hds0) (PCons n n0 p) H4) in ((let H8 \def (f_equal PList nat 
(\lambda (e: PList).(match e in PList return (\lambda (_: PList).nat) with 
[PNil \Rightarrow d | (PCons _ n1 _) \Rightarrow n1])) (PCons h d hds0) 
(PCons n n0 p) H4) in ((let H9 \def (f_equal PList nat (\lambda (e: 
PList).(match e in PList return (\lambda (_: PList).nat) with [PNil 
\Rightarrow h | (PCons n1 _ _) \Rightarrow n1])) (PCons h d hds0) (PCons n n0 
p) H4) in (eq_ind nat n (\lambda (n1: nat).((eq nat d n0) \to ((eq PList hds0 
p) \to ((eq C c0 c1) \to ((eq C c4 c2) \to ((drop n1 d c0 c3) \to ((drop1 
hds0 c3 c4) \to (arity g c1 (lift n n0 (lift1 p t)) a)))))))) (\lambda (H10: 
(eq nat d n0)).(eq_ind nat n0 (\lambda (n1: nat).((eq PList hds0 p) \to ((eq 
C c0 c1) \to ((eq C c4 c2) \to ((drop n n1 c0 c3) \to ((drop1 hds0 c3 c4) \to 
(arity g c1 (lift n n0 (lift1 p t)) a))))))) (\lambda (H11: (eq PList hds0 
p)).(eq_ind PList p (\lambda (p0: PList).((eq C c0 c1) \to ((eq C c4 c2) \to 
((drop n n0 c0 c3) \to ((drop1 p0 c3 c4) \to (arity g c1 (lift n n0 (lift1 p 
t)) a)))))) (\lambda (H12: (eq C c0 c1)).(eq_ind C c1 (\lambda (c: C).((eq C 
c4 c2) \to ((drop n n0 c c3) \to ((drop1 p c3 c4) \to (arity g c1 (lift n n0 
(lift1 p t)) a))))) (\lambda (H13: (eq C c4 c2)).(eq_ind C c2 (\lambda (c: 
C).((drop n n0 c1 c3) \to ((drop1 p c3 c) \to (arity g c1 (lift n n0 (lift1 p 
t)) a)))) (\lambda (H14: (drop n n0 c1 c3)).(\lambda (H15: (drop1 p c3 
c2)).(arity_lift g c3 (lift1 p t) a (H c3 t H15 H1) c1 n n0 H14))) c4 (sym_eq 
C c4 c2 H13))) c0 (sym_eq C c0 c1 H12))) hds0 (sym_eq PList hds0 p H11))) d 
(sym_eq nat d n0 H10))) h (sym_eq nat h n H9))) H8)) H7)) H5 H6 H2 H3))))]) 
in (H2 (refl_equal PList (PCons n n0 p)) (refl_equal C c1) (refl_equal C 
c2))))))))))) hds)))).

