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

set "baseuri" "cic:/matita/LAMBDA-TYPES/LambdaDelta-1/csubc/drop1".

include "csubc/drop.ma".

theorem drop1_csubc_trans:
 \forall (g: G).(\forall (hds: PList).(\forall (c2: C).(\forall (e2: 
C).((drop1 hds c2 e2) \to (\forall (e1: C).((csubc g e2 e1) \to (ex2 C 
(\lambda (c1: C).(drop1 hds c1 e1)) (\lambda (c1: C).(csubc g c2 c1)))))))))
\def
 \lambda (g: G).(\lambda (hds: PList).(PList_ind (\lambda (p: PList).(\forall 
(c2: C).(\forall (e2: C).((drop1 p c2 e2) \to (\forall (e1: C).((csubc g e2 
e1) \to (ex2 C (\lambda (c1: C).(drop1 p c1 e1)) (\lambda (c1: C).(csubc g c2 
c1))))))))) (\lambda (c2: C).(\lambda (e2: C).(\lambda (H: (drop1 PNil c2 
e2)).(\lambda (e1: C).(\lambda (H0: (csubc g e2 e1)).(let H1 \def (match H in 
drop1 return (\lambda (p: PList).(\lambda (c: C).(\lambda (c0: C).(\lambda 
(_: (drop1 p c c0)).((eq PList p PNil) \to ((eq C c c2) \to ((eq C c0 e2) \to 
(ex2 C (\lambda (c1: C).(drop1 PNil c1 e1)) (\lambda (c1: C).(csubc g c2 
c1)))))))))) with [(drop1_nil c) \Rightarrow (\lambda (_: (eq PList PNil 
PNil)).(\lambda (H2: (eq C c c2)).(\lambda (H3: (eq C c e2)).(eq_ind C c2 
(\lambda (c0: C).((eq C c0 e2) \to (ex2 C (\lambda (c1: C).(drop1 PNil c1 
e1)) (\lambda (c1: C).(csubc g c2 c1))))) (\lambda (H4: (eq C c2 e2)).(eq_ind 
C e2 (\lambda (c0: C).(ex2 C (\lambda (c1: C).(drop1 PNil c1 e1)) (\lambda 
(c1: C).(csubc g c0 c1)))) (let H5 \def (eq_ind_r C e2 (\lambda (c0: 
C).(csubc g c0 e1)) H0 c2 H4) in (eq_ind C c2 (\lambda (c0: C).(ex2 C 
(\lambda (c1: C).(drop1 PNil c1 e1)) (\lambda (c1: C).(csubc g c0 c1)))) 
(ex_intro2 C (\lambda (c1: C).(drop1 PNil c1 e1)) (\lambda (c1: C).(csubc g 
c2 c1)) e1 (drop1_nil e1) H5) e2 H4)) c2 (sym_eq C c2 e2 H4))) c (sym_eq C c 
c2 H2) H3)))) | (drop1_cons c1 c0 h d H1 c3 hds0 H2) \Rightarrow (\lambda 
(H3: (eq PList (PCons h d hds0) PNil)).(\lambda (H4: (eq C c1 c2)).(\lambda 
(H5: (eq C c3 e2)).((let H6 \def (eq_ind PList (PCons h d hds0) (\lambda (e: 
PList).(match e in PList return (\lambda (_: PList).Prop) with [PNil 
\Rightarrow False | (PCons _ _ _) \Rightarrow True])) I PNil H3) in 
(False_ind ((eq C c1 c2) \to ((eq C c3 e2) \to ((drop h d c1 c0) \to ((drop1 
hds0 c0 c3) \to (ex2 C (\lambda (c4: C).(drop1 PNil c4 e1)) (\lambda (c4: 
C).(csubc g c2 c4))))))) H6)) H4 H5 H1 H2))))]) in (H1 (refl_equal PList 
PNil) (refl_equal C c2) (refl_equal C e2)))))))) (\lambda (n: nat).(\lambda 
(n0: nat).(\lambda (p: PList).(\lambda (H: ((\forall (c2: C).(\forall (e2: 
C).((drop1 p c2 e2) \to (\forall (e1: C).((csubc g e2 e1) \to (ex2 C (\lambda 
(c1: C).(drop1 p c1 e1)) (\lambda (c1: C).(csubc g c2 c1)))))))))).(\lambda 
(c2: C).(\lambda (e2: C).(\lambda (H0: (drop1 (PCons n n0 p) c2 e2)).(\lambda 
(e1: C).(\lambda (H1: (csubc g e2 e1)).(let H2 \def (match H0 in drop1 return 
(\lambda (p0: PList).(\lambda (c: C).(\lambda (c0: C).(\lambda (_: (drop1 p0 
c c0)).((eq PList p0 (PCons n n0 p)) \to ((eq C c c2) \to ((eq C c0 e2) \to 
(ex2 C (\lambda (c1: C).(drop1 (PCons n n0 p) c1 e1)) (\lambda (c1: C).(csubc 
g c2 c1)))))))))) with [(drop1_nil c) \Rightarrow (\lambda (H2: (eq PList 
PNil (PCons n n0 p))).(\lambda (H3: (eq C c c2)).(\lambda (H4: (eq C c 
e2)).((let H5 \def (eq_ind PList PNil (\lambda (e: PList).(match e in PList 
return (\lambda (_: PList).Prop) with [PNil \Rightarrow True | (PCons _ _ _) 
\Rightarrow False])) I (PCons n n0 p) H2) in (False_ind ((eq C c c2) \to ((eq 
C c e2) \to (ex2 C (\lambda (c1: C).(drop1 (PCons n n0 p) c1 e1)) (\lambda 
(c1: C).(csubc g c2 c1))))) H5)) H3 H4)))) | (drop1_cons c1 c0 h d H2 c3 hds0 
H3) \Rightarrow (\lambda (H4: (eq PList (PCons h d hds0) (PCons n n0 
p))).(\lambda (H5: (eq C c1 c2)).(\lambda (H6: (eq C c3 e2)).((let H7 \def 
(f_equal PList PList (\lambda (e: PList).(match e in PList return (\lambda 
(_: PList).PList) with [PNil \Rightarrow hds0 | (PCons _ _ p0) \Rightarrow 
p0])) (PCons h d hds0) (PCons n n0 p) H4) in ((let H8 \def (f_equal PList nat 
(\lambda (e: PList).(match e in PList return (\lambda (_: PList).nat) with 
[PNil \Rightarrow d | (PCons _ n1 _) \Rightarrow n1])) (PCons h d hds0) 
(PCons n n0 p) H4) in ((let H9 \def (f_equal PList nat (\lambda (e: 
PList).(match e in PList return (\lambda (_: PList).nat) with [PNil 
\Rightarrow h | (PCons n1 _ _) \Rightarrow n1])) (PCons h d hds0) (PCons n n0 
p) H4) in (eq_ind nat n (\lambda (n1: nat).((eq nat d n0) \to ((eq PList hds0 
p) \to ((eq C c1 c2) \to ((eq C c3 e2) \to ((drop n1 d c1 c0) \to ((drop1 
hds0 c0 c3) \to (ex2 C (\lambda (c4: C).(drop1 (PCons n n0 p) c4 e1)) 
(\lambda (c4: C).(csubc g c2 c4)))))))))) (\lambda (H10: (eq nat d 
n0)).(eq_ind nat n0 (\lambda (n1: nat).((eq PList hds0 p) \to ((eq C c1 c2) 
\to ((eq C c3 e2) \to ((drop n n1 c1 c0) \to ((drop1 hds0 c0 c3) \to (ex2 C 
(\lambda (c4: C).(drop1 (PCons n n0 p) c4 e1)) (\lambda (c4: C).(csubc g c2 
c4))))))))) (\lambda (H11: (eq PList hds0 p)).(eq_ind PList p (\lambda (p0: 
PList).((eq C c1 c2) \to ((eq C c3 e2) \to ((drop n n0 c1 c0) \to ((drop1 p0 
c0 c3) \to (ex2 C (\lambda (c4: C).(drop1 (PCons n n0 p) c4 e1)) (\lambda 
(c4: C).(csubc g c2 c4)))))))) (\lambda (H12: (eq C c1 c2)).(eq_ind C c2 
(\lambda (c: C).((eq C c3 e2) \to ((drop n n0 c c0) \to ((drop1 p c0 c3) \to 
(ex2 C (\lambda (c4: C).(drop1 (PCons n n0 p) c4 e1)) (\lambda (c4: C).(csubc 
g c2 c4))))))) (\lambda (H13: (eq C c3 e2)).(eq_ind C e2 (\lambda (c: 
C).((drop n n0 c2 c0) \to ((drop1 p c0 c) \to (ex2 C (\lambda (c4: C).(drop1 
(PCons n n0 p) c4 e1)) (\lambda (c4: C).(csubc g c2 c4)))))) (\lambda (H14: 
(drop n n0 c2 c0)).(\lambda (H15: (drop1 p c0 e2)).(let H_x \def (H c0 e2 H15 
e1 H1) in (let H16 \def H_x in (ex2_ind C (\lambda (c4: C).(drop1 p c4 e1)) 
(\lambda (c4: C).(csubc g c0 c4)) (ex2 C (\lambda (c4: C).(drop1 (PCons n n0 
p) c4 e1)) (\lambda (c4: C).(csubc g c2 c4))) (\lambda (x: C).(\lambda (H17: 
(drop1 p x e1)).(\lambda (H18: (csubc g c0 x)).(let H_x0 \def 
(drop_csubc_trans g c2 c0 n0 n H14 x H18) in (let H19 \def H_x0 in (ex2_ind C 
(\lambda (c4: C).(drop n n0 c4 x)) (\lambda (c4: C).(csubc g c2 c4)) (ex2 C 
(\lambda (c4: C).(drop1 (PCons n n0 p) c4 e1)) (\lambda (c4: C).(csubc g c2 
c4))) (\lambda (x0: C).(\lambda (H20: (drop n n0 x0 x)).(\lambda (H21: (csubc 
g c2 x0)).(ex_intro2 C (\lambda (c4: C).(drop1 (PCons n n0 p) c4 e1)) 
(\lambda (c4: C).(csubc g c2 c4)) x0 (drop1_cons x0 x n n0 H20 e1 p H17) 
H21)))) H19)))))) H16))))) c3 (sym_eq C c3 e2 H13))) c1 (sym_eq C c1 c2 
H12))) hds0 (sym_eq PList hds0 p H11))) d (sym_eq nat d n0 H10))) h (sym_eq 
nat h n H9))) H8)) H7)) H5 H6 H2 H3))))]) in (H2 (refl_equal PList (PCons n 
n0 p)) (refl_equal C c2) (refl_equal C e2)))))))))))) hds)).

theorem csubc_drop1_conf_rev:
 \forall (g: G).(\forall (hds: PList).(\forall (c2: C).(\forall (e2: 
C).((drop1 hds c2 e2) \to (\forall (e1: C).((csubc g e1 e2) \to (ex2 C 
(\lambda (c1: C).(drop1 hds c1 e1)) (\lambda (c1: C).(csubc g c1 c2)))))))))
\def
 \lambda (g: G).(\lambda (hds: PList).(PList_ind (\lambda (p: PList).(\forall 
(c2: C).(\forall (e2: C).((drop1 p c2 e2) \to (\forall (e1: C).((csubc g e1 
e2) \to (ex2 C (\lambda (c1: C).(drop1 p c1 e1)) (\lambda (c1: C).(csubc g c1 
c2))))))))) (\lambda (c2: C).(\lambda (e2: C).(\lambda (H: (drop1 PNil c2 
e2)).(\lambda (e1: C).(\lambda (H0: (csubc g e1 e2)).(let H1 \def (match H in 
drop1 return (\lambda (p: PList).(\lambda (c: C).(\lambda (c0: C).(\lambda 
(_: (drop1 p c c0)).((eq PList p PNil) \to ((eq C c c2) \to ((eq C c0 e2) \to 
(ex2 C (\lambda (c1: C).(drop1 PNil c1 e1)) (\lambda (c1: C).(csubc g c1 
c2)))))))))) with [(drop1_nil c) \Rightarrow (\lambda (_: (eq PList PNil 
PNil)).(\lambda (H2: (eq C c c2)).(\lambda (H3: (eq C c e2)).(eq_ind C c2 
(\lambda (c0: C).((eq C c0 e2) \to (ex2 C (\lambda (c1: C).(drop1 PNil c1 
e1)) (\lambda (c1: C).(csubc g c1 c2))))) (\lambda (H4: (eq C c2 e2)).(eq_ind 
C e2 (\lambda (c0: C).(ex2 C (\lambda (c1: C).(drop1 PNil c1 e1)) (\lambda 
(c1: C).(csubc g c1 c0)))) (let H5 \def (eq_ind_r C e2 (\lambda (c0: 
C).(csubc g e1 c0)) H0 c2 H4) in (eq_ind C c2 (\lambda (c0: C).(ex2 C 
(\lambda (c1: C).(drop1 PNil c1 e1)) (\lambda (c1: C).(csubc g c1 c0)))) 
(ex_intro2 C (\lambda (c1: C).(drop1 PNil c1 e1)) (\lambda (c1: C).(csubc g 
c1 c2)) e1 (drop1_nil e1) H5) e2 H4)) c2 (sym_eq C c2 e2 H4))) c (sym_eq C c 
c2 H2) H3)))) | (drop1_cons c1 c0 h d H1 c3 hds0 H2) \Rightarrow (\lambda 
(H3: (eq PList (PCons h d hds0) PNil)).(\lambda (H4: (eq C c1 c2)).(\lambda 
(H5: (eq C c3 e2)).((let H6 \def (eq_ind PList (PCons h d hds0) (\lambda (e: 
PList).(match e in PList return (\lambda (_: PList).Prop) with [PNil 
\Rightarrow False | (PCons _ _ _) \Rightarrow True])) I PNil H3) in 
(False_ind ((eq C c1 c2) \to ((eq C c3 e2) \to ((drop h d c1 c0) \to ((drop1 
hds0 c0 c3) \to (ex2 C (\lambda (c4: C).(drop1 PNil c4 e1)) (\lambda (c4: 
C).(csubc g c4 c2))))))) H6)) H4 H5 H1 H2))))]) in (H1 (refl_equal PList 
PNil) (refl_equal C c2) (refl_equal C e2)))))))) (\lambda (n: nat).(\lambda 
(n0: nat).(\lambda (p: PList).(\lambda (H: ((\forall (c2: C).(\forall (e2: 
C).((drop1 p c2 e2) \to (\forall (e1: C).((csubc g e1 e2) \to (ex2 C (\lambda 
(c1: C).(drop1 p c1 e1)) (\lambda (c1: C).(csubc g c1 c2)))))))))).(\lambda 
(c2: C).(\lambda (e2: C).(\lambda (H0: (drop1 (PCons n n0 p) c2 e2)).(\lambda 
(e1: C).(\lambda (H1: (csubc g e1 e2)).(let H2 \def (match H0 in drop1 return 
(\lambda (p0: PList).(\lambda (c: C).(\lambda (c0: C).(\lambda (_: (drop1 p0 
c c0)).((eq PList p0 (PCons n n0 p)) \to ((eq C c c2) \to ((eq C c0 e2) \to 
(ex2 C (\lambda (c1: C).(drop1 (PCons n n0 p) c1 e1)) (\lambda (c1: C).(csubc 
g c1 c2)))))))))) with [(drop1_nil c) \Rightarrow (\lambda (H2: (eq PList 
PNil (PCons n n0 p))).(\lambda (H3: (eq C c c2)).(\lambda (H4: (eq C c 
e2)).((let H5 \def (eq_ind PList PNil (\lambda (e: PList).(match e in PList 
return (\lambda (_: PList).Prop) with [PNil \Rightarrow True | (PCons _ _ _) 
\Rightarrow False])) I (PCons n n0 p) H2) in (False_ind ((eq C c c2) \to ((eq 
C c e2) \to (ex2 C (\lambda (c1: C).(drop1 (PCons n n0 p) c1 e1)) (\lambda 
(c1: C).(csubc g c1 c2))))) H5)) H3 H4)))) | (drop1_cons c1 c0 h d H2 c3 hds0 
H3) \Rightarrow (\lambda (H4: (eq PList (PCons h d hds0) (PCons n n0 
p))).(\lambda (H5: (eq C c1 c2)).(\lambda (H6: (eq C c3 e2)).((let H7 \def 
(f_equal PList PList (\lambda (e: PList).(match e in PList return (\lambda 
(_: PList).PList) with [PNil \Rightarrow hds0 | (PCons _ _ p0) \Rightarrow 
p0])) (PCons h d hds0) (PCons n n0 p) H4) in ((let H8 \def (f_equal PList nat 
(\lambda (e: PList).(match e in PList return (\lambda (_: PList).nat) with 
[PNil \Rightarrow d | (PCons _ n1 _) \Rightarrow n1])) (PCons h d hds0) 
(PCons n n0 p) H4) in ((let H9 \def (f_equal PList nat (\lambda (e: 
PList).(match e in PList return (\lambda (_: PList).nat) with [PNil 
\Rightarrow h | (PCons n1 _ _) \Rightarrow n1])) (PCons h d hds0) (PCons n n0 
p) H4) in (eq_ind nat n (\lambda (n1: nat).((eq nat d n0) \to ((eq PList hds0 
p) \to ((eq C c1 c2) \to ((eq C c3 e2) \to ((drop n1 d c1 c0) \to ((drop1 
hds0 c0 c3) \to (ex2 C (\lambda (c4: C).(drop1 (PCons n n0 p) c4 e1)) 
(\lambda (c4: C).(csubc g c4 c2)))))))))) (\lambda (H10: (eq nat d 
n0)).(eq_ind nat n0 (\lambda (n1: nat).((eq PList hds0 p) \to ((eq C c1 c2) 
\to ((eq C c3 e2) \to ((drop n n1 c1 c0) \to ((drop1 hds0 c0 c3) \to (ex2 C 
(\lambda (c4: C).(drop1 (PCons n n0 p) c4 e1)) (\lambda (c4: C).(csubc g c4 
c2))))))))) (\lambda (H11: (eq PList hds0 p)).(eq_ind PList p (\lambda (p0: 
PList).((eq C c1 c2) \to ((eq C c3 e2) \to ((drop n n0 c1 c0) \to ((drop1 p0 
c0 c3) \to (ex2 C (\lambda (c4: C).(drop1 (PCons n n0 p) c4 e1)) (\lambda 
(c4: C).(csubc g c4 c2)))))))) (\lambda (H12: (eq C c1 c2)).(eq_ind C c2 
(\lambda (c: C).((eq C c3 e2) \to ((drop n n0 c c0) \to ((drop1 p c0 c3) \to 
(ex2 C (\lambda (c4: C).(drop1 (PCons n n0 p) c4 e1)) (\lambda (c4: C).(csubc 
g c4 c2))))))) (\lambda (H13: (eq C c3 e2)).(eq_ind C e2 (\lambda (c: 
C).((drop n n0 c2 c0) \to ((drop1 p c0 c) \to (ex2 C (\lambda (c4: C).(drop1 
(PCons n n0 p) c4 e1)) (\lambda (c4: C).(csubc g c4 c2)))))) (\lambda (H14: 
(drop n n0 c2 c0)).(\lambda (H15: (drop1 p c0 e2)).(let H_x \def (H c0 e2 H15 
e1 H1) in (let H16 \def H_x in (ex2_ind C (\lambda (c4: C).(drop1 p c4 e1)) 
(\lambda (c4: C).(csubc g c4 c0)) (ex2 C (\lambda (c4: C).(drop1 (PCons n n0 
p) c4 e1)) (\lambda (c4: C).(csubc g c4 c2))) (\lambda (x: C).(\lambda (H17: 
(drop1 p x e1)).(\lambda (H18: (csubc g x c0)).(let H_x0 \def 
(csubc_drop_conf_rev g c2 c0 n0 n H14 x H18) in (let H19 \def H_x0 in 
(ex2_ind C (\lambda (c4: C).(drop n n0 c4 x)) (\lambda (c4: C).(csubc g c4 
c2)) (ex2 C (\lambda (c4: C).(drop1 (PCons n n0 p) c4 e1)) (\lambda (c4: 
C).(csubc g c4 c2))) (\lambda (x0: C).(\lambda (H20: (drop n n0 x0 
x)).(\lambda (H21: (csubc g x0 c2)).(ex_intro2 C (\lambda (c4: C).(drop1 
(PCons n n0 p) c4 e1)) (\lambda (c4: C).(csubc g c4 c2)) x0 (drop1_cons x0 x 
n n0 H20 e1 p H17) H21)))) H19)))))) H16))))) c3 (sym_eq C c3 e2 H13))) c1 
(sym_eq C c1 c2 H12))) hds0 (sym_eq PList hds0 p H11))) d (sym_eq nat d n0 
H10))) h (sym_eq nat h n H9))) H8)) H7)) H5 H6 H2 H3))))]) in (H2 (refl_equal 
PList (PCons n n0 p)) (refl_equal C c2) (refl_equal C e2)))))))))))) hds)).

