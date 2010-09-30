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

include "Basic-1/drop1/defs.ma".

theorem drop1_gen_pnil:
 \forall (c1: C).(\forall (c2: C).((drop1 PNil c1 c2) \to (eq C c1 c2)))
\def
 \lambda (c1: C).(\lambda (c2: C).(\lambda (H: (drop1 PNil c1 c2)).(insert_eq 
PList PNil (\lambda (p: PList).(drop1 p c1 c2)) (\lambda (_: PList).(eq C c1 
c2)) (\lambda (y: PList).(\lambda (H0: (drop1 y c1 c2)).(drop1_ind (\lambda 
(p: PList).(\lambda (c: C).(\lambda (c0: C).((eq PList p PNil) \to (eq C c 
c0))))) (\lambda (c: C).(\lambda (_: (eq PList PNil PNil)).(refl_equal C c))) 
(\lambda (c3: C).(\lambda (c4: C).(\lambda (h: nat).(\lambda (d: 
nat).(\lambda (_: (drop h d c3 c4)).(\lambda (c5: C).(\lambda (hds: 
PList).(\lambda (_: (drop1 hds c4 c5)).(\lambda (_: (((eq PList hds PNil) \to 
(eq C c4 c5)))).(\lambda (H4: (eq PList (PCons h d hds) PNil)).(let H5 \def 
(eq_ind PList (PCons h d hds) (\lambda (ee: PList).(match ee in PList return 
(\lambda (_: PList).Prop) with [PNil \Rightarrow False | (PCons _ _ _) 
\Rightarrow True])) I PNil H4) in (False_ind (eq C c3 c5) H5)))))))))))) y c1 
c2 H0))) H))).
(* COMMENTS
Initial nodes: 198
END *)

theorem drop1_gen_pcons:
 \forall (c1: C).(\forall (c3: C).(\forall (hds: PList).(\forall (h: 
nat).(\forall (d: nat).((drop1 (PCons h d hds) c1 c3) \to (ex2 C (\lambda 
(c2: C).(drop h d c1 c2)) (\lambda (c2: C).(drop1 hds c2 c3))))))))
\def
 \lambda (c1: C).(\lambda (c3: C).(\lambda (hds: PList).(\lambda (h: 
nat).(\lambda (d: nat).(\lambda (H: (drop1 (PCons h d hds) c1 c3)).(insert_eq 
PList (PCons h d hds) (\lambda (p: PList).(drop1 p c1 c3)) (\lambda (_: 
PList).(ex2 C (\lambda (c2: C).(drop h d c1 c2)) (\lambda (c2: C).(drop1 hds 
c2 c3)))) (\lambda (y: PList).(\lambda (H0: (drop1 y c1 c3)).(drop1_ind 
(\lambda (p: PList).(\lambda (c: C).(\lambda (c0: C).((eq PList p (PCons h d 
hds)) \to (ex2 C (\lambda (c2: C).(drop h d c c2)) (\lambda (c2: C).(drop1 
hds c2 c0))))))) (\lambda (c: C).(\lambda (H1: (eq PList PNil (PCons h d 
hds))).(let H2 \def (eq_ind PList PNil (\lambda (ee: PList).(match ee in 
PList return (\lambda (_: PList).Prop) with [PNil \Rightarrow True | (PCons _ 
_ _) \Rightarrow False])) I (PCons h d hds) H1) in (False_ind (ex2 C (\lambda 
(c2: C).(drop h d c c2)) (\lambda (c2: C).(drop1 hds c2 c))) H2)))) (\lambda 
(c2: C).(\lambda (c4: C).(\lambda (h0: nat).(\lambda (d0: nat).(\lambda (H1: 
(drop h0 d0 c2 c4)).(\lambda (c5: C).(\lambda (hds0: PList).(\lambda (H2: 
(drop1 hds0 c4 c5)).(\lambda (H3: (((eq PList hds0 (PCons h d hds)) \to (ex2 
C (\lambda (c6: C).(drop h d c4 c6)) (\lambda (c6: C).(drop1 hds c6 
c5)))))).(\lambda (H4: (eq PList (PCons h0 d0 hds0) (PCons h d hds))).(let H5 
\def (f_equal PList nat (\lambda (e: PList).(match e in PList return (\lambda 
(_: PList).nat) with [PNil \Rightarrow h0 | (PCons n _ _) \Rightarrow n])) 
(PCons h0 d0 hds0) (PCons h d hds) H4) in ((let H6 \def (f_equal PList nat 
(\lambda (e: PList).(match e in PList return (\lambda (_: PList).nat) with 
[PNil \Rightarrow d0 | (PCons _ n _) \Rightarrow n])) (PCons h0 d0 hds0) 
(PCons h d hds) H4) in ((let H7 \def (f_equal PList PList (\lambda (e: 
PList).(match e in PList return (\lambda (_: PList).PList) with [PNil 
\Rightarrow hds0 | (PCons _ _ p) \Rightarrow p])) (PCons h0 d0 hds0) (PCons h 
d hds) H4) in (\lambda (H8: (eq nat d0 d)).(\lambda (H9: (eq nat h0 h)).(let 
H10 \def (eq_ind PList hds0 (\lambda (p: PList).((eq PList p (PCons h d hds)) 
\to (ex2 C (\lambda (c6: C).(drop h d c4 c6)) (\lambda (c6: C).(drop1 hds c6 
c5))))) H3 hds H7) in (let H11 \def (eq_ind PList hds0 (\lambda (p: 
PList).(drop1 p c4 c5)) H2 hds H7) in (let H12 \def (eq_ind nat d0 (\lambda 
(n: nat).(drop h0 n c2 c4)) H1 d H8) in (let H13 \def (eq_ind nat h0 (\lambda 
(n: nat).(drop n d c2 c4)) H12 h H9) in (ex_intro2 C (\lambda (c6: C).(drop h 
d c2 c6)) (\lambda (c6: C).(drop1 hds c6 c5)) c4 H13 H11)))))))) H6)) 
H5)))))))))))) y c1 c3 H0))) H)))))).
(* COMMENTS
Initial nodes: 587
END *)

