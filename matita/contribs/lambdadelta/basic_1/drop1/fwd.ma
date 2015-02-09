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

include "basic_1/drop1/defs.ma".

let rec drop1_ind (P: (PList \to (C \to (C \to Prop)))) (f: (\forall (c: 
C).(P PNil c c))) (f0: (\forall (c1: C).(\forall (c2: C).(\forall (h: 
nat).(\forall (d: nat).((drop h d c1 c2) \to (\forall (c3: C).(\forall (hds: 
PList).((drop1 hds c2 c3) \to ((P hds c2 c3) \to (P (PCons h d hds) c1 
c3))))))))))) (p: PList) (c: C) (c0: C) (d: drop1 p c c0) on d: P p c c0 \def 
match d with [(drop1_nil c1) \Rightarrow (f c1) | (drop1_cons c1 c2 h d0 d1 
c3 hds d2) \Rightarrow (let TMP_1 \def ((drop1_ind P f f0) hds c2 c3 d2) in 
(f0 c1 c2 h d0 d1 c3 hds d2 TMP_1))].

theorem drop1_gen_pnil:
 \forall (c1: C).(\forall (c2: C).((drop1 PNil c1 c2) \to (eq C c1 c2)))
\def
 \lambda (c1: C).(\lambda (c2: C).(\lambda (H: (drop1 PNil c1 c2)).(let TMP_1 
\def (\lambda (p: PList).(drop1 p c1 c2)) in (let TMP_2 \def (\lambda (_: 
PList).(eq C c1 c2)) in (let TMP_9 \def (\lambda (y: PList).(\lambda (H0: 
(drop1 y c1 c2)).(let TMP_3 \def (\lambda (p: PList).(\lambda (c: C).(\lambda 
(c0: C).((eq PList p PNil) \to (eq C c c0))))) in (let TMP_4 \def (\lambda 
(c: C).(\lambda (_: (eq PList PNil PNil)).(refl_equal C c))) in (let TMP_8 
\def (\lambda (c3: C).(\lambda (c4: C).(\lambda (h: nat).(\lambda (d: 
nat).(\lambda (_: (drop h d c3 c4)).(\lambda (c5: C).(\lambda (hds: 
PList).(\lambda (_: (drop1 hds c4 c5)).(\lambda (_: (((eq PList hds PNil) \to 
(eq C c4 c5)))).(\lambda (H4: (eq PList (PCons h d hds) PNil)).(let TMP_5 
\def (PCons h d hds) in (let TMP_6 \def (\lambda (ee: PList).(match ee with 
[PNil \Rightarrow False | (PCons _ _ _) \Rightarrow True])) in (let H5 \def 
(eq_ind PList TMP_5 TMP_6 I PNil H4) in (let TMP_7 \def (eq C c3 c5) in 
(False_ind TMP_7 H5))))))))))))))) in (drop1_ind TMP_3 TMP_4 TMP_8 y c1 c2 
H0)))))) in (insert_eq PList PNil TMP_1 TMP_2 TMP_9 H)))))).

theorem drop1_gen_pcons:
 \forall (c1: C).(\forall (c3: C).(\forall (hds: PList).(\forall (h: 
nat).(\forall (d: nat).((drop1 (PCons h d hds) c1 c3) \to (ex2 C (\lambda 
(c2: C).(drop h d c1 c2)) (\lambda (c2: C).(drop1 hds c2 c3))))))))
\def
 \lambda (c1: C).(\lambda (c3: C).(\lambda (hds: PList).(\lambda (h: 
nat).(\lambda (d: nat).(\lambda (H: (drop1 (PCons h d hds) c1 c3)).(let TMP_1 
\def (PCons h d hds) in (let TMP_2 \def (\lambda (p: PList).(drop1 p c1 c3)) 
in (let TMP_5 \def (\lambda (_: PList).(let TMP_3 \def (\lambda (c2: C).(drop 
h d c1 c2)) in (let TMP_4 \def (\lambda (c2: C).(drop1 hds c2 c3)) in (ex2 C 
TMP_3 TMP_4)))) in (let TMP_35 \def (\lambda (y: PList).(\lambda (H0: (drop1 
y c1 c3)).(let TMP_8 \def (\lambda (p: PList).(\lambda (c: C).(\lambda (c0: 
C).((eq PList p (PCons h d hds)) \to (let TMP_6 \def (\lambda (c2: C).(drop h 
d c c2)) in (let TMP_7 \def (\lambda (c2: C).(drop1 hds c2 c0)) in (ex2 C 
TMP_6 TMP_7))))))) in (let TMP_14 \def (\lambda (c: C).(\lambda (H1: (eq 
PList PNil (PCons h d hds))).(let TMP_9 \def (\lambda (ee: PList).(match ee 
with [PNil \Rightarrow True | (PCons _ _ _) \Rightarrow False])) in (let 
TMP_10 \def (PCons h d hds) in (let H2 \def (eq_ind PList PNil TMP_9 I TMP_10 
H1) in (let TMP_11 \def (\lambda (c2: C).(drop h d c c2)) in (let TMP_12 \def 
(\lambda (c2: C).(drop1 hds c2 c)) in (let TMP_13 \def (ex2 C TMP_11 TMP_12) 
in (False_ind TMP_13 H2))))))))) in (let TMP_34 \def (\lambda (c2: 
C).(\lambda (c4: C).(\lambda (h0: nat).(\lambda (d0: nat).(\lambda (H1: (drop 
h0 d0 c2 c4)).(\lambda (c5: C).(\lambda (hds0: PList).(\lambda (H2: (drop1 
hds0 c4 c5)).(\lambda (H3: (((eq PList hds0 (PCons h d hds)) \to (ex2 C 
(\lambda (c6: C).(drop h d c4 c6)) (\lambda (c6: C).(drop1 hds c6 
c5)))))).(\lambda (H4: (eq PList (PCons h0 d0 hds0) (PCons h d hds))).(let 
TMP_15 \def (\lambda (e: PList).(match e with [PNil \Rightarrow h0 | (PCons n 
_ _) \Rightarrow n])) in (let TMP_16 \def (PCons h0 d0 hds0) in (let TMP_17 
\def (PCons h d hds) in (let H5 \def (f_equal PList nat TMP_15 TMP_16 TMP_17 
H4) in (let TMP_18 \def (\lambda (e: PList).(match e with [PNil \Rightarrow 
d0 | (PCons _ n _) \Rightarrow n])) in (let TMP_19 \def (PCons h0 d0 hds0) in 
(let TMP_20 \def (PCons h d hds) in (let H6 \def (f_equal PList nat TMP_18 
TMP_19 TMP_20 H4) in (let TMP_21 \def (\lambda (e: PList).(match e with [PNil 
\Rightarrow hds0 | (PCons _ _ p) \Rightarrow p])) in (let TMP_22 \def (PCons 
h0 d0 hds0) in (let TMP_23 \def (PCons h d hds) in (let H7 \def (f_equal 
PList PList TMP_21 TMP_22 TMP_23 H4) in (let TMP_32 \def (\lambda (H8: (eq 
nat d0 d)).(\lambda (H9: (eq nat h0 h)).(let TMP_26 \def (\lambda (p: 
PList).((eq PList p (PCons h d hds)) \to (let TMP_24 \def (\lambda (c6: 
C).(drop h d c4 c6)) in (let TMP_25 \def (\lambda (c6: C).(drop1 hds c6 c5)) 
in (ex2 C TMP_24 TMP_25))))) in (let H10 \def (eq_ind PList hds0 TMP_26 H3 
hds H7) in (let TMP_27 \def (\lambda (p: PList).(drop1 p c4 c5)) in (let H11 
\def (eq_ind PList hds0 TMP_27 H2 hds H7) in (let TMP_28 \def (\lambda (n: 
nat).(drop h0 n c2 c4)) in (let H12 \def (eq_ind nat d0 TMP_28 H1 d H8) in 
(let TMP_29 \def (\lambda (n: nat).(drop n d c2 c4)) in (let H13 \def (eq_ind 
nat h0 TMP_29 H12 h H9) in (let TMP_30 \def (\lambda (c6: C).(drop h d c2 
c6)) in (let TMP_31 \def (\lambda (c6: C).(drop1 hds c6 c5)) in (ex_intro2 C 
TMP_30 TMP_31 c4 H13 H11))))))))))))) in (let TMP_33 \def (TMP_32 H6) in 
(TMP_33 H5))))))))))))))))))))))))) in (drop1_ind TMP_8 TMP_14 TMP_34 y c1 c3 
H0)))))) in (insert_eq PList TMP_1 TMP_2 TMP_5 TMP_35 H)))))))))).

