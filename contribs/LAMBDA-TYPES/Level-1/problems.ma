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

(* Problematic objects for disambiguation/typechecking ********************)
(* FG: PLEASE COMMENT THE NON WORKING OBJECTS *****************************)

set "baseuri" "cic:/matita/LAMBDA-TYPES/Level-1/problems".

include "LambdaDelta/theory.ma".

(*

(* Problem 2: disambiguation errors with these objects *)

iso_trans (in iso/props)

theorem iso_trans:
 \forall (t1: T).(\forall (t2: T).((iso t1 t2) \to (\forall (t3: T).((iso t2 
t3) \to (iso t1 t3)))))
\def
 \lambda (t1: T).(\lambda (t2: T).(\lambda (H: (iso t1 t2)).(iso_ind (\lambda 
(t: T).(\lambda (t0: T).(\forall (t3: T).((iso t0 t3) \to (iso t t3))))) 
(\lambda (n1: nat).(\lambda (n2: nat).(\lambda (t3: T).(\lambda (H0: (iso 
(TSort n2) t3)).(let H1 \def (match H0 in iso return (\lambda (t: T).(\lambda 
(t0: T).(\lambda (_: (iso t t0)).((eq T t (TSort n2)) \to ((eq T t0 t3) \to 
(iso (TSort n1) t3)))))) with [(iso_sort n0 n3) \Rightarrow (\lambda (H0: (eq 
T (TSort n0) (TSort n2))).(\lambda (H1: (eq T (TSort n3) t3)).((let H2 \def 
(f_equal T nat (\lambda (e: T).(match e in T return (\lambda (_: T).nat) with 
[(TSort n) \Rightarrow n | (TLRef _) \Rightarrow n0 | (THead _ _ _) 
\Rightarrow n0])) (TSort n0) (TSort n2) H0) in (eq_ind nat n2 (\lambda (_: 
nat).((eq T (TSort n3) t3) \to (iso (TSort n1) t3))) (\lambda (H3: (eq T 
(TSort n3) t3)).(eq_ind T (TSort n3) (\lambda (t: T).(iso (TSort n1) t)) 
(iso_sort n1 n3) t3 H3)) n0 (sym_eq nat n0 n2 H2))) H1))) | (iso_lref i1 i2) 
\Rightarrow (\lambda (H0: (eq T (TLRef i1) (TSort n2))).(\lambda (H1: (eq T 
(TLRef i2) t3)).((let H2 \def (eq_ind T (TLRef i1) (\lambda (e: T).(match e 
in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef 
_) \Rightarrow True | (THead _ _ _) \Rightarrow False])) I (TSort n2) H0) in 
(False_ind ((eq T (TLRef i2) t3) \to (iso (TSort n1) t3)) H2)) H1))) | 
(iso_head k v1 v2 t1 t2) \Rightarrow (\lambda (H0: (eq T (THead k v1 t1) 
(TSort n2))).(\lambda (H1: (eq T (THead k v2 t2) t3)).((let H2 \def (eq_ind T 
(THead k v1 t1) (\lambda (e: T).(match e in T return (\lambda (_: T).Prop) 
with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | (THead _ _ 
_) \Rightarrow True])) I (TSort n2) H0) in (False_ind ((eq T (THead k v2 t2) 
t3) \to (iso (TSort n1) t3)) H2)) H1)))]) in (H1 (refl_equal T (TSort n2)) 
(refl_equal T t3))))))) (\lambda (i1: nat).(\lambda (i2: nat).(\lambda (t3: 
T).(\lambda (H0: (iso (TLRef i2) t3)).(let H1 \def (match H0 in iso return 
(\lambda (t: T).(\lambda (t0: T).(\lambda (_: (iso t t0)).((eq T t (TLRef 
i2)) \to ((eq T t0 t3) \to (iso (TLRef i1) t3)))))) with [(iso_sort n1 n2) 
\Rightarrow (\lambda (H0: (eq T (TSort n1) (TLRef i2))).(\lambda (H1: (eq T 
(TSort n2) t3)).((let H2 \def (eq_ind T (TSort n1) (\lambda (e: T).(match e 
in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow True | (TLRef 
_) \Rightarrow False | (THead _ _ _) \Rightarrow False])) I (TLRef i2) H0) in 
(False_ind ((eq T (TSort n2) t3) \to (iso (TLRef i1) t3)) H2)) H1))) | 
(iso_lref i0 i3) \Rightarrow (\lambda (H0: (eq T (TLRef i0) (TLRef 
i2))).(\lambda (H1: (eq T (TLRef i3) t3)).((let H2 \def (f_equal T nat 
(\lambda (e: T).(match e in T return (\lambda (_: T).nat) with [(TSort _) 
\Rightarrow i0 | (TLRef n) \Rightarrow n | (THead _ _ _) \Rightarrow i0])) 
(TLRef i0) (TLRef i2) H0) in (eq_ind nat i2 (\lambda (_: nat).((eq T (TLRef 
i3) t3) \to (iso (TLRef i1) t3))) (\lambda (H3: (eq T (TLRef i3) t3)).(eq_ind 
T (TLRef i3) (\lambda (t: T).(iso (TLRef i1) t)) (iso_lref i1 i3) t3 H3)) i0 
(sym_eq nat i0 i2 H2))) H1))) | (iso_head k v1 v2 t1 t2) \Rightarrow (\lambda 
(H0: (eq T (THead k v1 t1) (TLRef i2))).(\lambda (H1: (eq T (THead k v2 t2) 
t3)).((let H2 \def (eq_ind T (THead k v1 t1) (\lambda (e: T).(match e in T 
return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow False | (THead _ _ _) \Rightarrow True])) I (TLRef i2) H0) in 
(False_ind ((eq T (THead k v2 t2) t3) \to (iso (TLRef i1) t3)) H2)) H1)))]) 
in (H1 (refl_equal T (TLRef i2)) (refl_equal T t3))))))) (\lambda (k: 
K).(\lambda (v1: T).(\lambda (v2: T).(\lambda (t3: T).(\lambda (t4: 
T).(\lambda (t5: T).(\lambda (H0: (iso (THead k v2 t4) t5)).(let H1 \def 
(match H0 in iso return (\lambda (t: T).(\lambda (t0: T).(\lambda (_: (iso t 
t0)).((eq T t (THead k v2 t4)) \to ((eq T t0 t5) \to (iso (THead k v1 t3) 
t5)))))) with [(iso_sort n1 n2) \Rightarrow (\lambda (H0: (eq T (TSort n1) 
(THead k v2 t4))).(\lambda (H1: (eq T (TSort n2) t5)).((let H2 \def (eq_ind T 
(TSort n1) (\lambda (e: T).(match e in T return (\lambda (_: T).Prop) with 
[(TSort _) \Rightarrow True | (TLRef _) \Rightarrow False | (THead _ _ _) 
\Rightarrow False])) I (THead k v2 t4) H0) in (False_ind ((eq T (TSort n2) 
t5) \to (iso (THead k v1 t3) t5)) H2)) H1))) | (iso_lref i1 i2) \Rightarrow 
(\lambda (H0: (eq T (TLRef i1) (THead k v2 t4))).(\lambda (H1: (eq T (TLRef 
i2) t5)).((let H2 \def (eq_ind T (TLRef i1) (\lambda (e: T).(match e in T 
return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow True | (THead _ _ _) \Rightarrow False])) I (THead k v2 t4) H0) 
in (False_ind ((eq T (TLRef i2) t5) \to (iso (THead k v1 t3) t5)) H2)) H1))) 
| (iso_head k0 v0 v3 t0 t4) \Rightarrow (\lambda (H0: (eq T (THead k0 v0 t0) 
(THead k v2 t4))).(\lambda (H1: (eq T (THead k0 v3 t4) t5)).((let H2 \def 
(f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) with 
[(TSort _) \Rightarrow t0 | (TLRef _) \Rightarrow t0 | (THead _ _ t) 
\Rightarrow t])) (THead k0 v0 t0) (THead k v2 t4) H0) in ((let H3 \def 
(f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) with 
[(TSort _) \Rightarrow v0 | (TLRef _) \Rightarrow v0 | (THead _ t _) 
\Rightarrow t])) (THead k0 v0 t0) (THead k v2 t4) H0) in ((let H4 \def 
(f_equal T K (\lambda (e: T).(match e in T return (\lambda (_: T).K) with 
[(TSort _) \Rightarrow k0 | (TLRef _) \Rightarrow k0 | (THead k _ _) 
\Rightarrow k])) (THead k0 v0 t0) (THead k v2 t4) H0) in (eq_ind K k (\lambda 
(k1: K).((eq T v0 v2) \to ((eq T t0 t4) \to ((eq T (THead k1 v3 t4) t5) \to 
(iso (THead k v1 t3) t5))))) (\lambda (H5: (eq T v0 v2)).(eq_ind T v2 
(\lambda (_: T).((eq T t0 t4) \to ((eq T (THead k v3 t4) t5) \to (iso (THead 
k v1 t3) t5)))) (\lambda (H6: (eq T t0 t4)).(eq_ind T t4 (\lambda (_: T).((eq 
T (THead k v3 t4) t5) \to (iso (THead k v1 t3) t5))) (\lambda (H7: (eq T 
(THead k v3 t4) t5)).(eq_ind T (THead k v3 t4) (\lambda (t: T).(iso (THead k 
v1 t3) t)) (iso_head k v1 v3 t3 t4) t5 H7)) t0 (sym_eq T t0 t4 H6))) v0 
(sym_eq T v0 v2 H5))) k0 (sym_eq K k0 k H4))) H3)) H2)) H1)))]) in (H1 
(refl_equal T (THead k v2 t4)) (refl_equal T t5)))))))))) t1 t2 H))).


drop1_getl_trans

(* Problem 1: does not typecheck a match on an empty type *)

theorem subst0_confluence_neq:
 \forall (t0: T).(\forall (t1: T).(\forall (u1: T).(\forall (i1: nat).((subst0 i1 u1 t0 t1) \to (\forall (t2: T).(\forall (u2: T).(\forall (i2: nat).((subst0 i2 u2 t0 t2) \to ((not (eq nat i1 i2)) \to (ex2 T (\lambda (t: T).(subst0 i2 u2 t1 t)) (\lambda (t: T).(subst0 i1 u1 t2 t))))))))))))
\def
 \lambda (t0: T).(\lambda (t1: T).(\lambda (u1: T).(\lambda (i1: nat).(\lambda (H: (subst0 i1 u1 t0 t1)).(subst0_ind (\lambda (n: nat).(\lambda (t: T).(\lambda (t2: T).(\lambda (t3: T).(\forall (t4: T).(\forall (u2: T).(\forall (i2: nat).((subst0 i2 u2 t2 t4) \to ((not (eq nat n i2)) \to (ex2 T (\lambda (t5: T).(subst0 i2 u2 t3 t5)) (\lambda (t5: T).(subst0 n t t4 t5)))))))))))) (\lambda (v: T).(\lambda (i: nat).(\lambda (t2: T).(\lambda (u2: T).(\lambda (i2: nat).(\lambda (H0: (subst0 i2 u2 (TLRef i) t2)).(\lambda (H1: (not (eq nat i i2))).(and_ind (eq nat i i2) (eq T t2 (lift (S i) O u2)) (ex2 T (\lambda (t: T).(subst0 i2 u2 (lift (S i) O v) t)) (\lambda (t: T).(subst0 i v t2 t))) (\lambda (H2: (eq nat i i2)).(\lambda (H3: (eq T t2 (lift (S i) O u2))).(let H4 \def (eq_ind nat i (\lambda (n: nat).(not (eq nat n i2))) H1 i2 H2) in (eq_ind_r T (lift (S i) O u2) (\lambda (t: T).(ex2 T (\lambda (t3: T).(subst0 i2 u2 (lift (S i) O v) t3)) (\lambda (t3: T).(subst0 i v t t3)))) (let H5 \def (match (H4 (refl_equal nat i2)) return (\lambda (_: False).(ex2 T (\lambda (t: T).(subst0 i2 u2 (lift (S i) O v) t)) (\lambda (t: T).(subst0 i v (lift (S i) O u2) t)))) with []) in H5) t2 H3)))) (subst0_gen_lref u2 t2 i2 i H0))))))))) (\lambda (v: T).(\lambda (u2: T).(\lambda (u0: T).(\lambda (i: nat).(\lambda (H0: (subst0 i v u0 u2)).(\lambda (H1: ((\forall (t2: T).(\forall (u3: T).(\forall (i2: nat).((subst0 i2 u3 u0 t2) \to ((not (eq nat i i2)) \to (ex2 T (\lambda (t: T).(subst0 i2 u3 u2 t)) (\lambda (t: T).(subst0 i v t2 t)))))))))).(\lambda (t: T).(\lambda (k: K).(\lambda (t2: T).(\lambda (u3: T).(\lambda (i2: nat).(\lambda (H2: (subst0 i2 u3 (THead k u0 t) t2)).(\lambda (H3: (not (eq nat i i2))).(or3_ind (ex2 T (\lambda (u4: T).(eq T t2 (THead k u4 t))) (\lambda (u4: T).(subst0 i2 u3 u0 u4))) (ex2 T (\lambda (t3: T).(eq T t2 (THead k u0 t3))) (\lambda (t3: T).(subst0 (s k i2) u3 t t3))) (ex3_2 T T (\lambda (u4: T).(\lambda (t3: T).(eq T t2 (THead k u4 t3)))) (\lambda (u4: T).(\lambda (_: T).(subst0 i2 u3 u0 u4))) (\lambda (_: T).(\lambda (t3: T).(subst0 (s k i2) u3 t t3)))) (ex2 T (\lambda (t3: T).(subst0 i2 u3 (THead k u2 t) t3)) (\lambda (t3: T).(subst0 i v t2 t3))) (\lambda (H4: (ex2 T (\lambda (u2: T).(eq T t2 (THead k u2 t))) (\lambda (u2: T).(subst0 i2 u3 u0 u2)))).(ex2_ind T (\lambda (u4: T).(eq T t2 (THead k u4 t))) (\lambda (u4: T).(subst0 i2 u3 u0 u4)) (ex2 T (\lambda (t3: T).(subst0 i2 u3 (THead k u2 t) t3)) (\lambda (t3: T).(subst0 i v t2 t3))) (\lambda (x: T).(\lambda (H5: (eq T t2 (THead k x t))).(\lambda (H6: (subst0 i2 u3 u0 x)).(eq_ind_r T (THead k x t) (\lambda (t3: T).(ex2 T (\lambda (t4: T).(subst0 i2 u3 (THead k u2 t) t4)) (\lambda (t4: T).(subst0 i v t3 t4)))) (ex2_ind T (\lambda (t3: T).(subst0 i2 u3 u2 t3)) (\lambda (t3: T).(subst0 i v x t3)) (ex2 T (\lambda (t3: T).(subst0 i2 u3 (THead k u2 t) t3)) (\lambda (t3: T).(subst0 i v (THead k x t) t3))) (\lambda (x0: T).(\lambda (H7: (subst0 i2 u3 u2 x0)).(\lambda (H8: (subst0 i v x x0)).(ex_intro2 T (\lambda (t3: T).(subst0 i2 u3 (THead k u2 t) t3)) (\lambda (t3: T).(subst0 i v (THead k x t) t3)) (THead k x0 t) (subst0_fst u3 x0 u2 i2 H7 t k) (subst0_fst v x0 x i H8 t k))))) (H1 x u3 i2 H6 H3)) t2 H5)))) H4)) (\lambda (H4: (ex2 T (\lambda (t3: T).(eq T t2 (THead k u0 t3))) (\lambda (t2: T).(subst0 (s k i2) u3 t t2)))).(ex2_ind T (\lambda (t3: T).(eq T t2 (THead k u0 t3))) (\lambda (t3: T).(subst0 (s k i2) u3 t t3)) (ex2 T (\lambda (t3: T).(subst0 i2 u3 (THead k u2 t) t3)) (\lambda (t3: T).(subst0 i v t2 t3))) (\lambda (x: T).(\lambda (H5: (eq T t2 (THead k u0 x))).(\lambda (H6: (subst0 (s k i2) u3 t x)).(eq_ind_r T (THead k u0 x) (\lambda (t3: T).(ex2 T (\lambda (t4: T).(subst0 i2 u3 (THead k u2 t) t4)) (\lambda (t4: T).(subst0 i v t3 t4)))) (ex_intro2 T (\lambda (t3: T).(subst0 i2 u3 (THead k u2 t) t3)) (\lambda (t3: T).(subst0 i v (THead k u0 x) t3)) (THead k u2 x) (subst0_snd k u3 x t i2 H6 u2) (subst0_fst v u2 u0 i H0 x k)) t2 H5)))) H4)) (\lambda (H4: (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead k u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(subst0 i2 u3 u0 u2))) (\lambda (_: T).(\lambda (t2: T).(subst0 (s k i2) u3 t t2))))).(ex3_2_ind T T (\lambda (u4: T).(\lambda (t3: T).(eq T t2 (THead k u4 t3)))) (\lambda (u4: T).(\lambda (_: T).(subst0 i2 u3 u0 u4))) (\lambda (_: T).(\lambda (t3: T).(subst0 (s k i2) u3 t t3))) (ex2 T (\lambda (t3: T).(subst0 i2 u3 (THead k u2 t) t3)) (\lambda (t3: T).(subst0 i v t2 t3))) (\lambda (x0: T).(\lambda (x1: T).(\lambda (H5: (eq T t2 (THead k x0 x1))).(\lambda (H6: (subst0 i2 u3 u0 x0)).(\lambda (H7: (subst0 (s k i2) u3 t x1)).(eq_ind_r T (THead k x0 x1) (\lambda (t3: T).(ex2 T (\lambda (t4: T).(subst0 i2 u3 (THead k u2 t) t4)) (\lambda (t4: T).(subst0 i v t3 t4)))) (ex2_ind T (\lambda (t3: T).(subst0 i2 u3 u2 t3)) (\lambda (t3: T).(subst0 i v x0 t3)) (ex2 T (\lambda (t3: T).(subst0 i2 u3 (THead k u2 t) t3)) (\lambda (t3: T).(subst0 i v (THead k x0 x1) t3))) (\lambda (x: T).(\lambda (H8: (subst0 i2 u3 u2 x)).(\lambda (H9: (subst0 i v x0 x)).(ex_intro2 T (\lambda (t3: T).(subst0 i2 u3 (THead k u2 t) t3)) (\lambda (t3: T).(subst0 i v (THead k x0 x1) t3)) (THead k x x1) (subst0_both u3 u2 x i2 H8 k t x1 H7) (subst0_fst v x x0 i H9 x1 k))))) (H1 x0 u3 i2 H6 H3)) t2 H5)))))) H4)) (subst0_gen_head k u3 u0 t t2 i2 H2))))))))))))))) (\lambda (k: K).(\lambda (v: T).(\lambda (t2: T).(\lambda (t3: T).(\lambda (i: nat).(\lambda (H0: (subst0 (s k i) v t3 t2)).(\lambda (H1: ((\forall (t4: T).(\forall (u2: T).(\forall (i2: nat).((subst0 i2 u2 t3 t4) \to ((not (eq nat (s k i) i2)) \to (ex2 T (\lambda (t: T).(subst0 i2 u2 t2 t)) (\lambda (t: T).(subst0 (s k i) v t4 t)))))))))).(\lambda (u: T).(\lambda (t4: T).(\lambda (u2: T).(\lambda (i2: nat).(\lambda (H2: (subst0 i2 u2 (THead k u t3) t4)).(\lambda (H3: (not (eq nat i i2))).(or3_ind (ex2 T (\lambda (u3: T).(eq T t4 (THead k u3 t3))) (\lambda (u3: T).(subst0 i2 u2 u u3))) (ex2 T (\lambda (t5: T).(eq T t4 (THead k u t5))) (\lambda (t5: T).(subst0 (s k i2) u2 t3 t5))) (ex3_2 T T (\lambda (u3: T).(\lambda (t5: T).(eq T t4 (THead k u3 t5)))) (\lambda (u3: T).(\lambda (_: T).(subst0 i2 u2 u u3))) (\lambda (_: T).(\lambda (t5: T).(subst0 (s k i2) u2 t3 t5)))) (ex2 T (\lambda (t: T).(subst0 i2 u2 (THead k u t2) t)) (\lambda (t: T).(subst0 i v t4 t))) (\lambda (H4: (ex2 T (\lambda (u2: T).(eq T t4 (THead k u2 t3))) (\lambda (u3: T).(subst0 i2 u2 u u3)))).(ex2_ind T (\lambda (u3: T).(eq T t4 (THead k u3 t3))) (\lambda (u3: T).(subst0 i2 u2 u u3)) (ex2 T (\lambda (t: T).(subst0 i2 u2 (THead k u t2) t)) (\lambda (t: T).(subst0 i v t4 t))) (\lambda (x: T).(\lambda (H5: (eq T t4 (THead k x t3))).(\lambda (H6: (subst0 i2 u2 u x)).(eq_ind_r T (THead k x t3) (\lambda (t: T).(ex2 T (\lambda (t5: T).(subst0 i2 u2 (THead k u t2) t5)) (\lambda (t5: T).(subst0 i v t t5)))) (ex_intro2 T (\lambda (t: T).(subst0 i2 u2 (THead k u t2) t)) (\lambda (t: T).(subst0 i v (THead k x t3) t)) (THead k x t2) (subst0_fst u2 x u i2 H6 t2 k) (subst0_snd k v t2 t3 i H0 x)) t4 H5)))) H4)) (\lambda (H4: (ex2 T (\lambda (t2: T).(eq T t4 (THead k u t2))) (\lambda (t2: T).(subst0 (s k i2) u2 t3 t2)))).(ex2_ind T (\lambda (t5: T).(eq T t4 (THead k u t5))) (\lambda (t5: T).(subst0 (s k i2) u2 t3 t5)) (ex2 T (\lambda (t: T).(subst0 i2 u2 (THead k u t2) t)) (\lambda (t: T).(subst0 i v t4 t))) (\lambda (x: T).(\lambda (H5: (eq T t4 (THead k u x))).(\lambda (H6: (subst0 (s k i2) u2 t3 x)).(eq_ind_r T (THead k u x) (\lambda (t: T).(ex2 T (\lambda (t5: T).(subst0 i2 u2 (THead k u t2) t5)) (\lambda (t5: T).(subst0 i v t t5)))) (ex2_ind T (\lambda (t: T).(subst0 (s k i2) u2 t2 t)) (\lambda (t: T).(subst0 (s k i) v x t)) (ex2 T (\lambda (t: T).(subst0 i2 u2 (THead k u t2) t)) (\lambda (t: T).(subst0 i v (THead k u x) t))) (\lambda (x0: T).(\lambda (H7: (subst0 (s k i2) u2 t2 x0)).(\lambda (H8: (subst0 (s k i) v x x0)).(ex_intro2 T (\lambda (t: T).(subst0 i2 u2 (THead k u t2) t)) (\lambda (t: T).(subst0 i v (THead k u x) t)) (THead k u x0) (subst0_snd k u2 x0 t2 i2 H7 u) (subst0_snd k v x0 x i H8 u))))) (H1 x u2 (s k i2) H6 (\lambda (H7: (eq nat (s k i) (s k i2))).(H3 (s_inj k i i2 H7))))) t4 H5)))) H4)) (\lambda (H4: (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T t4 (THead k u2 t2)))) (\lambda (u3: T).(\lambda (_: T).(subst0 i2 u2 u u3))) (\lambda (_: T).(\lambda (t2: T).(subst0 (s k i2) u2 t3 t2))))).(ex3_2_ind T T (\lambda (u3: T).(\lambda (t5: T).(eq T t4 (THead k u3 t5)))) (\lambda (u3: T).(\lambda (_: T).(subst0 i2 u2 u u3))) (\lambda (_: T).(\lambda (t5: T).(subst0 (s k i2) u2 t3 t5))) (ex2 T (\lambda (t: T).(subst0 i2 u2 (THead k u t2) t)) (\lambda (t: T).(subst0 i v t4 t))) (\lambda (x0: T).(\lambda (x1: T).(\lambda (H5: (eq T t4 (THead k x0 x1))).(\lambda (H6: (subst0 i2 u2 u x0)).(\lambda (H7: (subst0 (s k i2) u2 t3 x1)).(eq_ind_r T (THead k x0 x1) (\lambda (t: T).(ex2 T (\lambda (t5: T).(subst0 i2 u2 (THead k u t2) t5)) (\lambda (t5: T).(subst0 i v t t5)))) (ex2_ind T (\lambda (t: T).(subst0 (s k i2) u2 t2 t)) (\lambda (t: T).(subst0 (s k i) v x1 t)) (ex2 T (\lambda (t: T).(subst0 i2 u2 (THead k u t2) t)) (\lambda (t: T).(subst0 i v (THead k x0 x1) t))) (\lambda (x: T).(\lambda (H8: (subst0 (s k i2) u2 t2 x)).(\lambda (H9: (subst0 (s k i) v x1 x)).(ex_intro2 T (\lambda (t: T).(subst0 i2 u2 (THead k u t2) t)) (\lambda (t: T).(subst0 i v (THead k x0 x1) t)) (THead k x0 x) (subst0_both u2 u x0 i2 H6 k t2 x H8) (subst0_snd k v x x1 i H9 x0))))) (H1 x1 u2 (s k i2) H7 (\lambda (H8: (eq nat (s k i) (s k i2))).(H3 (s_inj k i i2 H8))))) t4 H5)))))) H4)) (subst0_gen_head k u2 u t3 t4 i2 H2))))))))))))))) (\lambda (v: T).(\lambda (u0: T).(\lambda (u2: T).(\lambda (i: nat).(\lambda (H0: (subst0 i v u0 u2)).(\lambda (H1: ((\forall (t2: T).(\forall (u3: T).(\forall (i2: nat).((subst0 i2 u3 u0 t2) \to ((not (eq nat i i2)) \to (ex2 T (\lambda (t: T).(subst0 i2 u3 u2 t)) (\lambda (t: T).(subst0 i v t2 t)))))))))).(\lambda (k: K).(\lambda (t2: T).(\lambda (t3: T).(\lambda (H2: (subst0 (s k i) v t2 t3)).(\lambda (H3: ((\forall (t4: T).(\forall (u2: T).(\forall (i2: nat).((subst0 i2 u2 t2 t4) \to ((not (eq nat (s k i) i2)) \to (ex2 T (\lambda (t: T).(subst0 i2 u2 t3 t)) (\lambda (t: T).(subst0 (s k i) v t4 t)))))))))).(\lambda (t4: T).(\lambda (u3: T).(\lambda (i2: nat).(\lambda (H4: (subst0 i2 u3 (THead k u0 t2) t4)).(\lambda (H5: (not (eq nat i i2))).(or3_ind (ex2 T (\lambda (u4: T).(eq T t4 (THead k u4 t2))) (\lambda (u4: T).(subst0 i2 u3 u0 u4))) (ex2 T (\lambda (t5: T).(eq T t4 (THead k u0 t5))) (\lambda (t5: T).(subst0 (s k i2) u3 t2 t5))) (ex3_2 T T (\lambda (u4: T).(\lambda (t5: T).(eq T t4 (THead k u4 t5)))) (\lambda (u4: T).(\lambda (_: T).(subst0 i2 u3 u0 u4))) (\lambda (_: T).(\lambda (t5: T).(subst0 (s k i2) u3 t2 t5)))) (ex2 T (\lambda (t: T).(subst0 i2 u3 (THead k u2 t3) t)) (\lambda (t: T).(subst0 i v t4 t))) (\lambda (H6: (ex2 T (\lambda (u2: T).(eq T t4 (THead k u2 t2))) (\lambda (u2: T).(subst0 i2 u3 u0 u2)))).(ex2_ind T (\lambda (u4: T).(eq T t4 (THead k u4 t2))) (\lambda (u4: T).(subst0 i2 u3 u0 u4)) (ex2 T (\lambda (t: T).(subst0 i2 u3 (THead k u2 t3) t)) (\lambda (t: T).(subst0 i v t4 t))) (\lambda (x: T).(\lambda (H7: (eq T t4 (THead k x t2))).(\lambda (H8: (subst0 i2 u3 u0 x)).(eq_ind_r T (THead k x t2) (\lambda (t: T).(ex2 T (\lambda (t5: T).(subst0 i2 u3 (THead k u2 t3) t5)) (\lambda (t5: T).(subst0 i v t t5)))) (ex2_ind T (\lambda (t: T).(subst0 i2 u3 u2 t)) (\lambda (t: T).(subst0 i v x t)) (ex2 T (\lambda (t: T).(subst0 i2 u3 (THead k u2 t3) t)) (\lambda (t: T).(subst0 i v (THead k x t2) t))) (\lambda (x0: T).(\lambda (H9: (subst0 i2 u3 u2 x0)).(\lambda (H10: (subst0 i v x x0)).(ex_intro2 T (\lambda (t: T).(subst0 i2 u3 (THead k u2 t3) t)) (\lambda (t: T).(subst0 i v (THead k x t2) t)) (THead k x0 t3) (subst0_fst u3 x0 u2 i2 H9 t3 k) (subst0_both v x x0 i H10 k t2 t3 H2))))) (H1 x u3 i2 H8 H5)) t4 H7)))) H6)) (\lambda (H6: (ex2 T (\lambda (t2: T).(eq T t4 (THead k u0 t2))) (\lambda (t3: T).(subst0 (s k i2) u3 t2 t3)))).(ex2_ind T (\lambda (t5: T).(eq T t4 (THead k u0 t5))) (\lambda (t5: T).(subst0 (s k i2) u3 t2 t5)) (ex2 T (\lambda (t: T).(subst0 i2 u3 (THead k u2 t3) t)) (\lambda (t: T).(subst0 i v t4 t))) (\lambda (x: T).(\lambda (H7: (eq T t4 (THead k u0 x))).(\lambda (H8: (subst0 (s k i2) u3 t2 x)).(eq_ind_r T (THead k u0 x) (\lambda (t: T).(ex2 T (\lambda (t5: T).(subst0 i2 u3 (THead k u2 t3) t5)) (\lambda (t5: T).(subst0 i v t t5)))) (ex2_ind T (\lambda (t: T).(subst0 (s k i2) u3 t3 t)) (\lambda (t: T).(subst0 (s k i) v x t)) (ex2 T (\lambda (t: T).(subst0 i2 u3 (THead k u2 t3) t)) (\lambda (t: T).(subst0 i v (THead k u0 x) t))) (\lambda (x0: T).(\lambda (H9: (subst0 (s k i2) u3 t3 x0)).(\lambda (H10: (subst0 (s k i) v x x0)).(ex_intro2 T (\lambda (t: T).(subst0 i2 u3 (THead k u2 t3) t)) (\lambda (t: T).(subst0 i v (THead k u0 x) t)) (THead k u2 x0) (subst0_snd k u3 x0 t3 i2 H9 u2) (subst0_both v u0 u2 i H0 k x x0 H10))))) (H3 x u3 (s k i2) H8 (\lambda (H9: (eq nat (s k i) (s k i2))).(H5 (s_inj k i i2 H9))))) t4 H7)))) H6)) (\lambda (H6: (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T t4 (THead k u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(subst0 i2 u3 u0 u2))) (\lambda (_: T).(\lambda (t3: T).(subst0 (s k i2) u3 t2 t3))))).(ex3_2_ind T T (\lambda (u4: T).(\lambda (t5: T).(eq T t4 (THead k u4 t5)))) (\lambda (u4: T).(\lambda (_: T).(subst0 i2 u3 u0 u4))) (\lambda (_: T).(\lambda (t5: T).(subst0 (s k i2) u3 t2 t5))) (ex2 T (\lambda (t: T).(subst0 i2 u3 (THead k u2 t3) t)) (\lambda (t: T).(subst0 i v t4 t))) (\lambda (x0: T).(\lambda (x1: T).(\lambda (H7: (eq T t4 (THead k x0 x1))).(\lambda (H8: (subst0 i2 u3 u0 x0)).(\lambda (H9: (subst0 (s k i2) u3 t2 x1)).(eq_ind_r T (THead k x0 x1) (\lambda (t: T).(ex2 T (\lambda (t5: T).(subst0 i2 u3 (THead k u2 t3) t5)) (\lambda (t5: T).(subst0 i v t t5)))) (ex2_ind T (\lambda (t: T).(subst0 i2 u3 u2 t)) (\lambda (t: T).(subst0 i v x0 t)) (ex2 T (\lambda (t: T).(subst0 i2 u3 (THead k u2 t3) t)) (\lambda (t: T).(subst0 i v (THead k x0 x1) t))) (\lambda (x: T).(\lambda (H10: (subst0 i2 u3 u2 x)).(\lambda (H11: (subst0 i v x0 x)).(ex2_ind T (\lambda (t: T).(subst0 (s k i2) u3 t3 t)) (\lambda (t: T).(subst0 (s k i) v x1 t)) (ex2 T (\lambda (t: T).(subst0 i2 u3 (THead k u2 t3) t)) (\lambda (t: T).(subst0 i v (THead k x0 x1) t))) (\lambda (x2: T).(\lambda (H12: (subst0 (s k i2) u3 t3 x2)).(\lambda (H13: (subst0 (s k i) v x1 x2)).(ex_intro2 T (\lambda (t: T).(subst0 i2 u3 (THead k u2 t3) t)) (\lambda (t: T).(subst0 i v (THead k x0 x1) t)) (THead k x x2) (subst0_both u3 u2 x i2 H10 k t3 x2 H12) (subst0_both v x0 x i H11 k x1 x2 H13))))) (H3 x1 u3 (s k i2) H9 (\lambda (H12: (eq nat (s k i) (s k i2))).(H5 (s_inj k i i2 H12)))))))) (H1 x0 u3 i2 H8 H5)) t4 H7)))))) H6)) (subst0_gen_head k u3 u0 t2 t4 i2 H4)))))))))))))))))) i1 u1 t0 t1 H))))).

(* Problem 3: assertion failure raised by type checker on this object *)

tau1

*)
