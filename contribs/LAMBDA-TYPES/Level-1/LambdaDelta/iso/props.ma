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

set "baseuri" "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/iso/props".

include "iso/defs.ma".

theorem iso_trans:
 \forall (t1: T).(\forall (t2: T).((iso t1 t2) \to (\forall (t3: T).((iso t2 
t3) \to (iso t1 t3)))))
\def
 \lambda (t1: T).(\lambda (t2: T).(\lambda (H: (iso t1 t2)).(iso_ind (\lambda 
(t: T).(\lambda (t0: T).(\forall (t3: T).((iso t0 t3) \to (iso t t3))))) 
(\lambda (n1: nat).(\lambda (n2: nat).(\lambda (t3: T).(\lambda (H0: (iso 
(TSort n2) t3)).(let H1 \def (match H0 in iso return (\lambda (t: T).(\lambda 
(t0: T).(\lambda (_: (iso t t0)).((eq T t (TSort n2)) \to ((eq T t0 t3) \to 
(iso (TSort n1) t3)))))) with [(iso_sort n0 n3) \Rightarrow (\lambda (H1: (eq 
T (TSort n0) (TSort n2))).(\lambda (H2: (eq T (TSort n3) t3)).((let H3 \def 
(f_equal T nat (\lambda (e: T).(match e in T return (\lambda (_: T).nat) with 
[(TSort n) \Rightarrow n | (TLRef _) \Rightarrow n0 | (THead _ _ _) 
\Rightarrow n0])) (TSort n0) (TSort n2) H1) in (eq_ind nat n2 (\lambda (_: 
nat).((eq T (TSort n3) t3) \to (iso (TSort n1) t3))) (\lambda (H4: (eq T 
(TSort n3) t3)).(eq_ind T (TSort n3) (\lambda (t: T).(iso (TSort n1) t)) 
(iso_sort n1 n3) t3 H4)) n0 (sym_eq nat n0 n2 H3))) H2))) | (iso_lref i1 i2) 
\Rightarrow (\lambda (H1: (eq T (TLRef i1) (TSort n2))).(\lambda (H2: (eq T 
(TLRef i2) t3)).((let H3 \def (eq_ind T (TLRef i1) (\lambda (e: T).(match e 
in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef 
_) \Rightarrow True | (THead _ _ _) \Rightarrow False])) I (TSort n2) H1) in 
(False_ind ((eq T (TLRef i2) t3) \to (iso (TSort n1) t3)) H3)) H2))) | 
(iso_head k v1 v2 t0 t4) \Rightarrow (\lambda (H1: (eq T (THead k v1 t0) 
(TSort n2))).(\lambda (H2: (eq T (THead k v2 t4) t3)).((let H3 \def (eq_ind T 
(THead k v1 t0) (\lambda (e: T).(match e in T return (\lambda (_: T).Prop) 
with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | (THead _ _ 
_) \Rightarrow True])) I (TSort n2) H1) in (False_ind ((eq T (THead k v2 t4) 
t3) \to (iso (TSort n1) t3)) H3)) H2)))]) in (H1 (refl_equal T (TSort n2)) 
(refl_equal T t3))))))) (\lambda (i1: nat).(\lambda (i2: nat).(\lambda (t3: 
T).(\lambda (H0: (iso (TLRef i2) t3)).(let H1 \def (match H0 in iso return 
(\lambda (t: T).(\lambda (t0: T).(\lambda (_: (iso t t0)).((eq T t (TLRef 
i2)) \to ((eq T t0 t3) \to (iso (TLRef i1) t3)))))) with [(iso_sort n1 n2) 
\Rightarrow (\lambda (H1: (eq T (TSort n1) (TLRef i2))).(\lambda (H2: (eq T 
(TSort n2) t3)).((let H3 \def (eq_ind T (TSort n1) (\lambda (e: T).(match e 
in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow True | (TLRef 
_) \Rightarrow False | (THead _ _ _) \Rightarrow False])) I (TLRef i2) H1) in 
(False_ind ((eq T (TSort n2) t3) \to (iso (TLRef i1) t3)) H3)) H2))) | 
(iso_lref i0 i3) \Rightarrow (\lambda (H1: (eq T (TLRef i0) (TLRef 
i2))).(\lambda (H2: (eq T (TLRef i3) t3)).((let H3 \def (f_equal T nat 
(\lambda (e: T).(match e in T return (\lambda (_: T).nat) with [(TSort _) 
\Rightarrow i0 | (TLRef n) \Rightarrow n | (THead _ _ _) \Rightarrow i0])) 
(TLRef i0) (TLRef i2) H1) in (eq_ind nat i2 (\lambda (_: nat).((eq T (TLRef 
i3) t3) \to (iso (TLRef i1) t3))) (\lambda (H4: (eq T (TLRef i3) t3)).(eq_ind 
T (TLRef i3) (\lambda (t: T).(iso (TLRef i1) t)) (iso_lref i1 i3) t3 H4)) i0 
(sym_eq nat i0 i2 H3))) H2))) | (iso_head k v1 v2 t0 t4) \Rightarrow (\lambda 
(H1: (eq T (THead k v1 t0) (TLRef i2))).(\lambda (H2: (eq T (THead k v2 t4) 
t3)).((let H3 \def (eq_ind T (THead k v1 t0) (\lambda (e: T).(match e in T 
return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow False | (THead _ _ _) \Rightarrow True])) I (TLRef i2) H1) in 
(False_ind ((eq T (THead k v2 t4) t3) \to (iso (TLRef i1) t3)) H3)) H2)))]) 
in (H1 (refl_equal T (TLRef i2)) (refl_equal T t3))))))) (\lambda (k: 
K).(\lambda (v1: T).(\lambda (v2: T).(\lambda (t3: T).(\lambda (t4: 
T).(\lambda (t5: T).(\lambda (H0: (iso (THead k v2 t4) t5)).(let H1 \def 
(match H0 in iso return (\lambda (t: T).(\lambda (t0: T).(\lambda (_: (iso t 
t0)).((eq T t (THead k v2 t4)) \to ((eq T t0 t5) \to (iso (THead k v1 t3) 
t5)))))) with [(iso_sort n1 n2) \Rightarrow (\lambda (H1: (eq T (TSort n1) 
(THead k v2 t4))).(\lambda (H2: (eq T (TSort n2) t5)).((let H3 \def (eq_ind T 
(TSort n1) (\lambda (e: T).(match e in T return (\lambda (_: T).Prop) with 
[(TSort _) \Rightarrow True | (TLRef _) \Rightarrow False | (THead _ _ _) 
\Rightarrow False])) I (THead k v2 t4) H1) in (False_ind ((eq T (TSort n2) 
t5) \to (iso (THead k v1 t3) t5)) H3)) H2))) | (iso_lref i1 i2) \Rightarrow 
(\lambda (H1: (eq T (TLRef i1) (THead k v2 t4))).(\lambda (H2: (eq T (TLRef 
i2) t5)).((let H3 \def (eq_ind T (TLRef i1) (\lambda (e: T).(match e in T 
return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow True | (THead _ _ _) \Rightarrow False])) I (THead k v2 t4) H1) 
in (False_ind ((eq T (TLRef i2) t5) \to (iso (THead k v1 t3) t5)) H3)) H2))) 
| (iso_head k0 v0 v3 t0 t6) \Rightarrow (\lambda (H1: (eq T (THead k0 v0 t0) 
(THead k v2 t4))).(\lambda (H2: (eq T (THead k0 v3 t6) t5)).((let H3 \def 
(f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) with 
[(TSort _) \Rightarrow t0 | (TLRef _) \Rightarrow t0 | (THead _ _ t) 
\Rightarrow t])) (THead k0 v0 t0) (THead k v2 t4) H1) in ((let H4 \def 
(f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) with 
[(TSort _) \Rightarrow v0 | (TLRef _) \Rightarrow v0 | (THead _ t _) 
\Rightarrow t])) (THead k0 v0 t0) (THead k v2 t4) H1) in ((let H5 \def 
(f_equal T K (\lambda (e: T).(match e in T return (\lambda (_: T).K) with 
[(TSort _) \Rightarrow k0 | (TLRef _) \Rightarrow k0 | (THead k1 _ _) 
\Rightarrow k1])) (THead k0 v0 t0) (THead k v2 t4) H1) in (eq_ind K k 
(\lambda (k1: K).((eq T v0 v2) \to ((eq T t0 t4) \to ((eq T (THead k1 v3 t6) 
t5) \to (iso (THead k v1 t3) t5))))) (\lambda (H6: (eq T v0 v2)).(eq_ind T v2 
(\lambda (_: T).((eq T t0 t4) \to ((eq T (THead k v3 t6) t5) \to (iso (THead 
k v1 t3) t5)))) (\lambda (H7: (eq T t0 t4)).(eq_ind T t4 (\lambda (_: T).((eq 
T (THead k v3 t6) t5) \to (iso (THead k v1 t3) t5))) (\lambda (H8: (eq T 
(THead k v3 t6) t5)).(eq_ind T (THead k v3 t6) (\lambda (t: T).(iso (THead k 
v1 t3) t)) (iso_head k v1 v3 t3 t6) t5 H8)) t0 (sym_eq T t0 t4 H7))) v0 
(sym_eq T v0 v2 H6))) k0 (sym_eq K k0 k H5))) H4)) H3)) H2)))]) in (H1 
(refl_equal T (THead k v2 t4)) (refl_equal T t5)))))))))) t1 t2 H))).

