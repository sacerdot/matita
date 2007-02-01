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

set "baseuri" "cic:/matita/LAMBDA-TYPES/LambdaDelta-1/lift/fwd".

include "lift/defs.ma".

theorem lift_sort:
 \forall (n: nat).(\forall (h: nat).(\forall (d: nat).(eq T (lift h d (TSort 
n)) (TSort n))))
\def
 \lambda (n: nat).(\lambda (_: nat).(\lambda (_: nat).(refl_equal T (TSort 
n)))).

theorem lift_lref_lt:
 \forall (n: nat).(\forall (h: nat).(\forall (d: nat).((lt n d) \to (eq T 
(lift h d (TLRef n)) (TLRef n)))))
\def
 \lambda (n: nat).(\lambda (h: nat).(\lambda (d: nat).(\lambda (H: (lt n 
d)).(eq_ind bool true (\lambda (b: bool).(eq T (TLRef (match b with [true 
\Rightarrow n | false \Rightarrow (plus n h)])) (TLRef n))) (refl_equal T 
(TLRef n)) (blt n d) (sym_eq bool (blt n d) true (lt_blt d n H)))))).

theorem lift_lref_ge:
 \forall (n: nat).(\forall (h: nat).(\forall (d: nat).((le d n) \to (eq T 
(lift h d (TLRef n)) (TLRef (plus n h))))))
\def
 \lambda (n: nat).(\lambda (h: nat).(\lambda (d: nat).(\lambda (H: (le d 
n)).(eq_ind bool false (\lambda (b: bool).(eq T (TLRef (match b with [true 
\Rightarrow n | false \Rightarrow (plus n h)])) (TLRef (plus n h)))) 
(refl_equal T (TLRef (plus n h))) (blt n d) (sym_eq bool (blt n d) false 
(le_bge d n H)))))).

theorem lift_head:
 \forall (k: K).(\forall (u: T).(\forall (t: T).(\forall (h: nat).(\forall 
(d: nat).(eq T (lift h d (THead k u t)) (THead k (lift h d u) (lift h (s k d) 
t)))))))
\def
 \lambda (k: K).(\lambda (u: T).(\lambda (t: T).(\lambda (h: nat).(\lambda 
(d: nat).(refl_equal T (THead k (lift h d u) (lift h (s k d) t))))))).

theorem lift_bind:
 \forall (b: B).(\forall (u: T).(\forall (t: T).(\forall (h: nat).(\forall 
(d: nat).(eq T (lift h d (THead (Bind b) u t)) (THead (Bind b) (lift h d u) 
(lift h (S d) t)))))))
\def
 \lambda (b: B).(\lambda (u: T).(\lambda (t: T).(\lambda (h: nat).(\lambda 
(d: nat).(refl_equal T (THead (Bind b) (lift h d u) (lift h (S d) t))))))).

theorem lift_flat:
 \forall (f: F).(\forall (u: T).(\forall (t: T).(\forall (h: nat).(\forall 
(d: nat).(eq T (lift h d (THead (Flat f) u t)) (THead (Flat f) (lift h d u) 
(lift h d t)))))))
\def
 \lambda (f: F).(\lambda (u: T).(\lambda (t: T).(\lambda (h: nat).(\lambda 
(d: nat).(refl_equal T (THead (Flat f) (lift h d u) (lift h d t))))))).

theorem lift_gen_sort:
 \forall (h: nat).(\forall (d: nat).(\forall (n: nat).(\forall (t: T).((eq T 
(TSort n) (lift h d t)) \to (eq T t (TSort n))))))
\def
 \lambda (h: nat).(\lambda (d: nat).(\lambda (n: nat).(\lambda (t: T).(T_ind 
(\lambda (t0: T).((eq T (TSort n) (lift h d t0)) \to (eq T t0 (TSort n)))) 
(\lambda (n0: nat).(\lambda (H: (eq T (TSort n) (lift h d (TSort 
n0)))).(sym_eq T (TSort n) (TSort n0) H))) (\lambda (n0: nat).(\lambda (H: 
(eq T (TSort n) (lift h d (TLRef n0)))).(lt_le_e n0 d (eq T (TLRef n0) (TSort 
n)) (\lambda (H0: (lt n0 d)).(let H1 \def (eq_ind T (lift h d (TLRef n0)) 
(\lambda (t0: T).(eq T (TSort n) t0)) H (TLRef n0) (lift_lref_lt n0 h d H0)) 
in (let H2 \def (match H1 in eq return (\lambda (t0: T).(\lambda (_: (eq ? ? 
t0)).((eq T t0 (TLRef n0)) \to (eq T (TLRef n0) (TSort n))))) with 
[refl_equal \Rightarrow (\lambda (H2: (eq T (TSort n) (TLRef n0))).(let H3 
\def (eq_ind T (TSort n) (\lambda (e: T).(match e in T return (\lambda (_: 
T).Prop) with [(TSort _) \Rightarrow True | (TLRef _) \Rightarrow False | 
(THead _ _ _) \Rightarrow False])) I (TLRef n0) H2) in (False_ind (eq T 
(TLRef n0) (TSort n)) H3)))]) in (H2 (refl_equal T (TLRef n0)))))) (\lambda 
(H0: (le d n0)).(let H1 \def (eq_ind T (lift h d (TLRef n0)) (\lambda (t0: 
T).(eq T (TSort n) t0)) H (TLRef (plus n0 h)) (lift_lref_ge n0 h d H0)) in 
(let H2 \def (match H1 in eq return (\lambda (t0: T).(\lambda (_: (eq ? ? 
t0)).((eq T t0 (TLRef (plus n0 h))) \to (eq T (TLRef n0) (TSort n))))) with 
[refl_equal \Rightarrow (\lambda (H2: (eq T (TSort n) (TLRef (plus n0 
h)))).(let H3 \def (eq_ind T (TSort n) (\lambda (e: T).(match e in T return 
(\lambda (_: T).Prop) with [(TSort _) \Rightarrow True | (TLRef _) 
\Rightarrow False | (THead _ _ _) \Rightarrow False])) I (TLRef (plus n0 h)) 
H2) in (False_ind (eq T (TLRef n0) (TSort n)) H3)))]) in (H2 (refl_equal T 
(TLRef (plus n0 h)))))))))) (\lambda (k: K).(\lambda (t0: T).(\lambda (_: 
(((eq T (TSort n) (lift h d t0)) \to (eq T t0 (TSort n))))).(\lambda (t1: 
T).(\lambda (_: (((eq T (TSort n) (lift h d t1)) \to (eq T t1 (TSort 
n))))).(\lambda (H1: (eq T (TSort n) (lift h d (THead k t0 t1)))).(let H2 
\def (eq_ind T (lift h d (THead k t0 t1)) (\lambda (t2: T).(eq T (TSort n) 
t2)) H1 (THead k (lift h d t0) (lift h (s k d) t1)) (lift_head k t0 t1 h d)) 
in (let H3 \def (match H2 in eq return (\lambda (t2: T).(\lambda (_: (eq ? ? 
t2)).((eq T t2 (THead k (lift h d t0) (lift h (s k d) t1))) \to (eq T (THead 
k t0 t1) (TSort n))))) with [refl_equal \Rightarrow (\lambda (H3: (eq T 
(TSort n) (THead k (lift h d t0) (lift h (s k d) t1)))).(let H4 \def (eq_ind 
T (TSort n) (\lambda (e: T).(match e in T return (\lambda (_: T).Prop) with 
[(TSort _) \Rightarrow True | (TLRef _) \Rightarrow False | (THead _ _ _) 
\Rightarrow False])) I (THead k (lift h d t0) (lift h (s k d) t1)) H3) in 
(False_ind (eq T (THead k t0 t1) (TSort n)) H4)))]) in (H3 (refl_equal T 
(THead k (lift h d t0) (lift h (s k d) t1)))))))))))) t)))).

theorem lift_gen_lref:
 \forall (t: T).(\forall (d: nat).(\forall (h: nat).(\forall (i: nat).((eq T 
(TLRef i) (lift h d t)) \to (or (land (lt i d) (eq T t (TLRef i))) (land (le 
(plus d h) i) (eq T t (TLRef (minus i h)))))))))
\def
 \lambda (t: T).(T_ind (\lambda (t0: T).(\forall (d: nat).(\forall (h: 
nat).(\forall (i: nat).((eq T (TLRef i) (lift h d t0)) \to (or (land (lt i d) 
(eq T t0 (TLRef i))) (land (le (plus d h) i) (eq T t0 (TLRef (minus i 
h)))))))))) (\lambda (n: nat).(\lambda (d: nat).(\lambda (h: nat).(\lambda 
(i: nat).(\lambda (H: (eq T (TLRef i) (lift h d (TSort n)))).(let H0 \def 
(eq_ind T (lift h d (TSort n)) (\lambda (t0: T).(eq T (TLRef i) t0)) H (TSort 
n) (lift_sort n h d)) in (let H1 \def (eq_ind T (TLRef i) (\lambda (ee: 
T).(match ee in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow 
False | (TLRef _) \Rightarrow True | (THead _ _ _) \Rightarrow False])) I 
(TSort n) H0) in (False_ind (or (land (lt i d) (eq T (TSort n) (TLRef i))) 
(land (le (plus d h) i) (eq T (TSort n) (TLRef (minus i h))))) H1)))))))) 
(\lambda (n: nat).(\lambda (d: nat).(\lambda (h: nat).(\lambda (i: 
nat).(\lambda (H: (eq T (TLRef i) (lift h d (TLRef n)))).(lt_le_e n d (or 
(land (lt i d) (eq T (TLRef n) (TLRef i))) (land (le (plus d h) i) (eq T 
(TLRef n) (TLRef (minus i h))))) (\lambda (H0: (lt n d)).(let H1 \def (eq_ind 
T (lift h d (TLRef n)) (\lambda (t0: T).(eq T (TLRef i) t0)) H (TLRef n) 
(lift_lref_lt n h d H0)) in (let H2 \def (f_equal T nat (\lambda (e: 
T).(match e in T return (\lambda (_: T).nat) with [(TSort _) \Rightarrow i | 
(TLRef n0) \Rightarrow n0 | (THead _ _ _) \Rightarrow i])) (TLRef i) (TLRef 
n) H1) in (eq_ind_r nat n (\lambda (n0: nat).(or (land (lt n0 d) (eq T (TLRef 
n) (TLRef n0))) (land (le (plus d h) n0) (eq T (TLRef n) (TLRef (minus n0 
h)))))) (or_introl (land (lt n d) (eq T (TLRef n) (TLRef n))) (land (le (plus 
d h) n) (eq T (TLRef n) (TLRef (minus n h)))) (conj (lt n d) (eq T (TLRef n) 
(TLRef n)) H0 (refl_equal T (TLRef n)))) i H2)))) (\lambda (H0: (le d 
n)).(let H1 \def (eq_ind T (lift h d (TLRef n)) (\lambda (t0: T).(eq T (TLRef 
i) t0)) H (TLRef (plus n h)) (lift_lref_ge n h d H0)) in (let H2 \def 
(f_equal T nat (\lambda (e: T).(match e in T return (\lambda (_: T).nat) with 
[(TSort _) \Rightarrow i | (TLRef n0) \Rightarrow n0 | (THead _ _ _) 
\Rightarrow i])) (TLRef i) (TLRef (plus n h)) H1) in (eq_ind_r nat (plus n h) 
(\lambda (n0: nat).(or (land (lt n0 d) (eq T (TLRef n) (TLRef n0))) (land (le 
(plus d h) n0) (eq T (TLRef n) (TLRef (minus n0 h)))))) (eq_ind_r nat n 
(\lambda (n0: nat).(or (land (lt (plus n h) d) (eq T (TLRef n) (TLRef (plus n 
h)))) (land (le (plus d h) (plus n h)) (eq T (TLRef n) (TLRef n0))))) 
(or_intror (land (lt (plus n h) d) (eq T (TLRef n) (TLRef (plus n h)))) (land 
(le (plus d h) (plus n h)) (eq T (TLRef n) (TLRef n))) (conj (le (plus d h) 
(plus n h)) (eq T (TLRef n) (TLRef n)) (plus_le_compat d n h h H0 (le_n h)) 
(refl_equal T (TLRef n)))) (minus (plus n h) h) (minus_plus_r n h)) i 
H2)))))))))) (\lambda (k: K).(\lambda (t0: T).(\lambda (_: ((\forall (d: 
nat).(\forall (h: nat).(\forall (i: nat).((eq T (TLRef i) (lift h d t0)) \to 
(or (land (lt i d) (eq T t0 (TLRef i))) (land (le (plus d h) i) (eq T t0 
(TLRef (minus i h))))))))))).(\lambda (t1: T).(\lambda (_: ((\forall (d: 
nat).(\forall (h: nat).(\forall (i: nat).((eq T (TLRef i) (lift h d t1)) \to 
(or (land (lt i d) (eq T t1 (TLRef i))) (land (le (plus d h) i) (eq T t1 
(TLRef (minus i h))))))))))).(\lambda (d: nat).(\lambda (h: nat).(\lambda (i: 
nat).(\lambda (H1: (eq T (TLRef i) (lift h d (THead k t0 t1)))).(let H2 \def 
(eq_ind T (lift h d (THead k t0 t1)) (\lambda (t2: T).(eq T (TLRef i) t2)) H1 
(THead k (lift h d t0) (lift h (s k d) t1)) (lift_head k t0 t1 h d)) in (let 
H3 \def (eq_ind T (TLRef i) (\lambda (ee: T).(match ee in T return (\lambda 
(_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow True | 
(THead _ _ _) \Rightarrow False])) I (THead k (lift h d t0) (lift h (s k d) 
t1)) H2) in (False_ind (or (land (lt i d) (eq T (THead k t0 t1) (TLRef i))) 
(land (le (plus d h) i) (eq T (THead k t0 t1) (TLRef (minus i h))))) 
H3)))))))))))) t).

theorem lift_gen_lref_lt:
 \forall (h: nat).(\forall (d: nat).(\forall (n: nat).((lt n d) \to (\forall 
(t: T).((eq T (TLRef n) (lift h d t)) \to (eq T t (TLRef n)))))))
\def
 \lambda (h: nat).(\lambda (d: nat).(\lambda (n: nat).(\lambda (H: (lt n 
d)).(\lambda (t: T).(T_ind (\lambda (t0: T).((eq T (TLRef n) (lift h d t0)) 
\to (eq T t0 (TLRef n)))) (\lambda (n0: nat).(\lambda (H0: (eq T (TLRef n) 
(lift h d (TSort n0)))).(sym_eq T (TLRef n) (TSort n0) H0))) (\lambda (n0: 
nat).(\lambda (H0: (eq T (TLRef n) (lift h d (TLRef n0)))).(lt_le_e n0 d (eq 
T (TLRef n0) (TLRef n)) (\lambda (H1: (lt n0 d)).(let H2 \def (eq_ind T (lift 
h d (TLRef n0)) (\lambda (t0: T).(eq T (TLRef n) t0)) H0 (TLRef n0) 
(lift_lref_lt n0 h d H1)) in (sym_eq T (TLRef n) (TLRef n0) H2))) (\lambda 
(H1: (le d n0)).(let H2 \def (eq_ind T (lift h d (TLRef n0)) (\lambda (t0: 
T).(eq T (TLRef n) t0)) H0 (TLRef (plus n0 h)) (lift_lref_ge n0 h d H1)) in 
(let H3 \def (match H2 in eq return (\lambda (t0: T).(\lambda (_: (eq ? ? 
t0)).((eq T t0 (TLRef (plus n0 h))) \to (eq T (TLRef n0) (TLRef n))))) with 
[refl_equal \Rightarrow (\lambda (H3: (eq T (TLRef n) (TLRef (plus n0 
h)))).(let H4 \def (f_equal T nat (\lambda (e: T).(match e in T return 
(\lambda (_: T).nat) with [(TSort _) \Rightarrow n | (TLRef n1) \Rightarrow 
n1 | (THead _ _ _) \Rightarrow n])) (TLRef n) (TLRef (plus n0 h)) H3) in 
(eq_ind nat (plus n0 h) (\lambda (n1: nat).(eq T (TLRef n0) (TLRef n1))) (let 
H5 \def (eq_ind nat n (\lambda (n1: nat).(lt n1 d)) H (plus n0 h) H4) in 
(le_false d n0 (eq T (TLRef n0) (TLRef (plus n0 h))) H1 (lt_le_S n0 d 
(le_lt_trans n0 (plus n0 h) d (le_plus_l n0 h) H5)))) n (sym_eq nat n (plus 
n0 h) H4))))]) in (H3 (refl_equal T (TLRef (plus n0 h)))))))))) (\lambda (k: 
K).(\lambda (t0: T).(\lambda (_: (((eq T (TLRef n) (lift h d t0)) \to (eq T 
t0 (TLRef n))))).(\lambda (t1: T).(\lambda (_: (((eq T (TLRef n) (lift h d 
t1)) \to (eq T t1 (TLRef n))))).(\lambda (H2: (eq T (TLRef n) (lift h d 
(THead k t0 t1)))).(let H3 \def (eq_ind T (lift h d (THead k t0 t1)) (\lambda 
(t2: T).(eq T (TLRef n) t2)) H2 (THead k (lift h d t0) (lift h (s k d) t1)) 
(lift_head k t0 t1 h d)) in (let H4 \def (match H3 in eq return (\lambda (t2: 
T).(\lambda (_: (eq ? ? t2)).((eq T t2 (THead k (lift h d t0) (lift h (s k d) 
t1))) \to (eq T (THead k t0 t1) (TLRef n))))) with [refl_equal \Rightarrow 
(\lambda (H4: (eq T (TLRef n) (THead k (lift h d t0) (lift h (s k d) 
t1)))).(let H5 \def (eq_ind T (TLRef n) (\lambda (e: T).(match e in T return 
(\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow True | (THead _ _ _) \Rightarrow False])) I (THead k (lift h d 
t0) (lift h (s k d) t1)) H4) in (False_ind (eq T (THead k t0 t1) (TLRef n)) 
H5)))]) in (H4 (refl_equal T (THead k (lift h d t0) (lift h (s k d) 
t1)))))))))))) t))))).

theorem lift_gen_lref_false:
 \forall (h: nat).(\forall (d: nat).(\forall (n: nat).((le d n) \to ((lt n 
(plus d h)) \to (\forall (t: T).((eq T (TLRef n) (lift h d t)) \to (\forall 
(P: Prop).P)))))))
\def
 \lambda (h: nat).(\lambda (d: nat).(\lambda (n: nat).(\lambda (H: (le d 
n)).(\lambda (H0: (lt n (plus d h))).(\lambda (t: T).(T_ind (\lambda (t0: 
T).((eq T (TLRef n) (lift h d t0)) \to (\forall (P: Prop).P))) (\lambda (n0: 
nat).(\lambda (H1: (eq T (TLRef n) (lift h d (TSort n0)))).(\lambda (P: 
Prop).(let H2 \def (match H1 in eq return (\lambda (t0: T).(\lambda (_: (eq ? 
? t0)).((eq T t0 (lift h d (TSort n0))) \to P))) with [refl_equal \Rightarrow 
(\lambda (H2: (eq T (TLRef n) (lift h d (TSort n0)))).(let H3 \def (eq_ind T 
(TLRef n) (\lambda (e: T).(match e in T return (\lambda (_: T).Prop) with 
[(TSort _) \Rightarrow False | (TLRef _) \Rightarrow True | (THead _ _ _) 
\Rightarrow False])) I (lift h d (TSort n0)) H2) in (False_ind P H3)))]) in 
(H2 (refl_equal T (lift h d (TSort n0)))))))) (\lambda (n0: nat).(\lambda 
(H1: (eq T (TLRef n) (lift h d (TLRef n0)))).(\lambda (P: Prop).(lt_le_e n0 d 
P (\lambda (H2: (lt n0 d)).(let H3 \def (eq_ind T (lift h d (TLRef n0)) 
(\lambda (t0: T).(eq T (TLRef n) t0)) H1 (TLRef n0) (lift_lref_lt n0 h d H2)) 
in (let H4 \def (match H3 in eq return (\lambda (t0: T).(\lambda (_: (eq ? ? 
t0)).((eq T t0 (TLRef n0)) \to P))) with [refl_equal \Rightarrow (\lambda 
(H4: (eq T (TLRef n) (TLRef n0))).(let H5 \def (f_equal T nat (\lambda (e: 
T).(match e in T return (\lambda (_: T).nat) with [(TSort _) \Rightarrow n | 
(TLRef n1) \Rightarrow n1 | (THead _ _ _) \Rightarrow n])) (TLRef n) (TLRef 
n0) H4) in (eq_ind nat n0 (\lambda (_: nat).P) (let H6 \def (eq_ind_r nat n0 
(\lambda (n1: nat).(lt n1 d)) H2 n H5) in (le_false d n P H H6)) n (sym_eq 
nat n n0 H5))))]) in (H4 (refl_equal T (TLRef n0)))))) (\lambda (H2: (le d 
n0)).(let H3 \def (eq_ind T (lift h d (TLRef n0)) (\lambda (t0: T).(eq T 
(TLRef n) t0)) H1 (TLRef (plus n0 h)) (lift_lref_ge n0 h d H2)) in (let H4 
\def (match H3 in eq return (\lambda (t0: T).(\lambda (_: (eq ? ? t0)).((eq T 
t0 (TLRef (plus n0 h))) \to P))) with [refl_equal \Rightarrow (\lambda (H4: 
(eq T (TLRef n) (TLRef (plus n0 h)))).(let H5 \def (f_equal T nat (\lambda 
(e: T).(match e in T return (\lambda (_: T).nat) with [(TSort _) \Rightarrow 
n | (TLRef n1) \Rightarrow n1 | (THead _ _ _) \Rightarrow n])) (TLRef n) 
(TLRef (plus n0 h)) H4) in (eq_ind nat (plus n0 h) (\lambda (_: nat).P) (let 
H6 \def (eq_ind nat n (\lambda (n1: nat).(lt n1 (plus d h))) H0 (plus n0 h) 
H5) in (le_false d n0 P H2 (lt_le_S n0 d (simpl_lt_plus_r h n0 d H6)))) n 
(sym_eq nat n (plus n0 h) H5))))]) in (H4 (refl_equal T (TLRef (plus n0 
h))))))))))) (\lambda (k: K).(\lambda (t0: T).(\lambda (_: (((eq T (TLRef n) 
(lift h d t0)) \to (\forall (P: Prop).P)))).(\lambda (t1: T).(\lambda (_: 
(((eq T (TLRef n) (lift h d t1)) \to (\forall (P: Prop).P)))).(\lambda (H3: 
(eq T (TLRef n) (lift h d (THead k t0 t1)))).(\lambda (P: Prop).(let H4 \def 
(eq_ind T (lift h d (THead k t0 t1)) (\lambda (t2: T).(eq T (TLRef n) t2)) H3 
(THead k (lift h d t0) (lift h (s k d) t1)) (lift_head k t0 t1 h d)) in (let 
H5 \def (match H4 in eq return (\lambda (t2: T).(\lambda (_: (eq ? ? 
t2)).((eq T t2 (THead k (lift h d t0) (lift h (s k d) t1))) \to P))) with 
[refl_equal \Rightarrow (\lambda (H5: (eq T (TLRef n) (THead k (lift h d t0) 
(lift h (s k d) t1)))).(let H6 \def (eq_ind T (TLRef n) (\lambda (e: 
T).(match e in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow 
False | (TLRef _) \Rightarrow True | (THead _ _ _) \Rightarrow False])) I 
(THead k (lift h d t0) (lift h (s k d) t1)) H5) in (False_ind P H6)))]) in 
(H5 (refl_equal T (THead k (lift h d t0) (lift h (s k d) t1))))))))))))) 
t)))))).

theorem lift_gen_lref_ge:
 \forall (h: nat).(\forall (d: nat).(\forall (n: nat).((le d n) \to (\forall 
(t: T).((eq T (TLRef (plus n h)) (lift h d t)) \to (eq T t (TLRef n)))))))
\def
 \lambda (h: nat).(\lambda (d: nat).(\lambda (n: nat).(\lambda (H: (le d 
n)).(\lambda (t: T).(T_ind (\lambda (t0: T).((eq T (TLRef (plus n h)) (lift h 
d t0)) \to (eq T t0 (TLRef n)))) (\lambda (n0: nat).(\lambda (H0: (eq T 
(TLRef (plus n h)) (lift h d (TSort n0)))).(let H1 \def (match H0 in eq 
return (\lambda (t0: T).(\lambda (_: (eq ? ? t0)).((eq T t0 (lift h d (TSort 
n0))) \to (eq T (TSort n0) (TLRef n))))) with [refl_equal \Rightarrow 
(\lambda (H1: (eq T (TLRef (plus n h)) (lift h d (TSort n0)))).(let H2 \def 
(eq_ind T (TLRef (plus n h)) (\lambda (e: T).(match e in T return (\lambda 
(_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow True | 
(THead _ _ _) \Rightarrow False])) I (lift h d (TSort n0)) H1) in (False_ind 
(eq T (TSort n0) (TLRef n)) H2)))]) in (H1 (refl_equal T (lift h d (TSort 
n0))))))) (\lambda (n0: nat).(\lambda (H0: (eq T (TLRef (plus n h)) (lift h d 
(TLRef n0)))).(lt_le_e n0 d (eq T (TLRef n0) (TLRef n)) (\lambda (H1: (lt n0 
d)).(let H2 \def (eq_ind T (lift h d (TLRef n0)) (\lambda (t0: T).(eq T 
(TLRef (plus n h)) t0)) H0 (TLRef n0) (lift_lref_lt n0 h d H1)) in (let H3 
\def (match H2 in eq return (\lambda (t0: T).(\lambda (_: (eq ? ? t0)).((eq T 
t0 (TLRef n0)) \to (eq T (TLRef n0) (TLRef n))))) with [refl_equal 
\Rightarrow (\lambda (H3: (eq T (TLRef (plus n h)) (TLRef n0))).(let H4 \def 
(f_equal T nat (\lambda (e: T).(match e in T return (\lambda (_: T).nat) with 
[(TSort _) \Rightarrow ((let rec plus (n1: nat) on n1: (nat \to nat) \def 
(\lambda (m: nat).(match n1 with [O \Rightarrow m | (S p) \Rightarrow (S 
(plus p m))])) in plus) n h) | (TLRef n1) \Rightarrow n1 | (THead _ _ _) 
\Rightarrow ((let rec plus (n1: nat) on n1: (nat \to nat) \def (\lambda (m: 
nat).(match n1 with [O \Rightarrow m | (S p) \Rightarrow (S (plus p m))])) in 
plus) n h)])) (TLRef (plus n h)) (TLRef n0) H3) in (eq_ind nat (plus n h) 
(\lambda (n1: nat).(eq T (TLRef n1) (TLRef n))) (let H5 \def (eq_ind_r nat n0 
(\lambda (n1: nat).(lt n1 d)) H1 (plus n h) H4) in (le_false d n (eq T (TLRef 
(plus n h)) (TLRef n)) H (lt_le_S n d (le_lt_trans n (plus n h) d (le_plus_l 
n h) H5)))) n0 H4)))]) in (H3 (refl_equal T (TLRef n0)))))) (\lambda (H1: (le 
d n0)).(let H2 \def (eq_ind T (lift h d (TLRef n0)) (\lambda (t0: T).(eq T 
(TLRef (plus n h)) t0)) H0 (TLRef (plus n0 h)) (lift_lref_ge n0 h d H1)) in 
(let H3 \def (match H2 in eq return (\lambda (t0: T).(\lambda (_: (eq ? ? 
t0)).((eq T t0 (TLRef (plus n0 h))) \to (eq T (TLRef n0) (TLRef n))))) with 
[refl_equal \Rightarrow (\lambda (H3: (eq T (TLRef (plus n h)) (TLRef (plus 
n0 h)))).(let H4 \def (f_equal T nat (\lambda (e: T).(match e in T return 
(\lambda (_: T).nat) with [(TSort _) \Rightarrow ((let rec plus (n1: nat) on 
n1: (nat \to nat) \def (\lambda (m: nat).(match n1 with [O \Rightarrow m | (S 
p) \Rightarrow (S (plus p m))])) in plus) n h) | (TLRef n1) \Rightarrow n1 | 
(THead _ _ _) \Rightarrow ((let rec plus (n1: nat) on n1: (nat \to nat) \def 
(\lambda (m: nat).(match n1 with [O \Rightarrow m | (S p) \Rightarrow (S 
(plus p m))])) in plus) n h)])) (TLRef (plus n h)) (TLRef (plus n0 h)) H3) in 
(eq_ind nat (plus n h) (\lambda (_: nat).(eq T (TLRef n0) (TLRef n))) 
(f_equal nat T TLRef n0 n (simpl_plus_r h n0 n (sym_eq nat (plus n h) (plus 
n0 h) H4))) (plus n0 h) H4)))]) in (H3 (refl_equal T (TLRef (plus n0 
h)))))))))) (\lambda (k: K).(\lambda (t0: T).(\lambda (_: (((eq T (TLRef 
(plus n h)) (lift h d t0)) \to (eq T t0 (TLRef n))))).(\lambda (t1: 
T).(\lambda (_: (((eq T (TLRef (plus n h)) (lift h d t1)) \to (eq T t1 (TLRef 
n))))).(\lambda (H2: (eq T (TLRef (plus n h)) (lift h d (THead k t0 
t1)))).(let H3 \def (eq_ind T (lift h d (THead k t0 t1)) (\lambda (t2: T).(eq 
T (TLRef (plus n h)) t2)) H2 (THead k (lift h d t0) (lift h (s k d) t1)) 
(lift_head k t0 t1 h d)) in (let H4 \def (match H3 in eq return (\lambda (t2: 
T).(\lambda (_: (eq ? ? t2)).((eq T t2 (THead k (lift h d t0) (lift h (s k d) 
t1))) \to (eq T (THead k t0 t1) (TLRef n))))) with [refl_equal \Rightarrow 
(\lambda (H4: (eq T (TLRef (plus n h)) (THead k (lift h d t0) (lift h (s k d) 
t1)))).(let H5 \def (eq_ind T (TLRef (plus n h)) (\lambda (e: T).(match e in 
T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow True | (THead _ _ _) \Rightarrow False])) I (THead k (lift h d 
t0) (lift h (s k d) t1)) H4) in (False_ind (eq T (THead k t0 t1) (TLRef n)) 
H5)))]) in (H4 (refl_equal T (THead k (lift h d t0) (lift h (s k d) 
t1)))))))))))) t))))).

theorem lift_gen_head:
 \forall (k: K).(\forall (u: T).(\forall (t: T).(\forall (x: T).(\forall (h: 
nat).(\forall (d: nat).((eq T (THead k u t) (lift h d x)) \to (ex3_2 T T 
(\lambda (y: T).(\lambda (z: T).(eq T x (THead k y z)))) (\lambda (y: 
T).(\lambda (_: T).(eq T u (lift h d y)))) (\lambda (_: T).(\lambda (z: 
T).(eq T t (lift h (s k d) z)))))))))))
\def
 \lambda (k: K).(\lambda (u: T).(\lambda (t: T).(\lambda (x: T).(T_ind 
(\lambda (t0: T).(\forall (h: nat).(\forall (d: nat).((eq T (THead k u t) 
(lift h d t0)) \to (ex3_2 T T (\lambda (y: T).(\lambda (z: T).(eq T t0 (THead 
k y z)))) (\lambda (y: T).(\lambda (_: T).(eq T u (lift h d y)))) (\lambda 
(_: T).(\lambda (z: T).(eq T t (lift h (s k d) z))))))))) (\lambda (n: 
nat).(\lambda (h: nat).(\lambda (d: nat).(\lambda (H: (eq T (THead k u t) 
(lift h d (TSort n)))).(let H0 \def (match H in eq return (\lambda (t0: 
T).(\lambda (_: (eq ? ? t0)).((eq T t0 (lift h d (TSort n))) \to (ex3_2 T T 
(\lambda (y: T).(\lambda (z: T).(eq T (TSort n) (THead k y z)))) (\lambda (y: 
T).(\lambda (_: T).(eq T u (lift h d y)))) (\lambda (_: T).(\lambda (z: 
T).(eq T t (lift h (s k d) z)))))))) with [refl_equal \Rightarrow (\lambda 
(H0: (eq T (THead k u t) (lift h d (TSort n)))).(let H1 \def (eq_ind T (THead 
k u t) (\lambda (e: T).(match e in T return (\lambda (_: T).Prop) with 
[(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | (THead _ _ _) 
\Rightarrow True])) I (lift h d (TSort n)) H0) in (False_ind (ex3_2 T T 
(\lambda (y: T).(\lambda (z: T).(eq T (TSort n) (THead k y z)))) (\lambda (y: 
T).(\lambda (_: T).(eq T u (lift h d y)))) (\lambda (_: T).(\lambda (z: 
T).(eq T t (lift h (s k d) z))))) H1)))]) in (H0 (refl_equal T (lift h d 
(TSort n))))))))) (\lambda (n: nat).(\lambda (h: nat).(\lambda (d: 
nat).(\lambda (H: (eq T (THead k u t) (lift h d (TLRef n)))).(lt_le_e n d 
(ex3_2 T T (\lambda (y: T).(\lambda (z: T).(eq T (TLRef n) (THead k y z)))) 
(\lambda (y: T).(\lambda (_: T).(eq T u (lift h d y)))) (\lambda (_: 
T).(\lambda (z: T).(eq T t (lift h (s k d) z))))) (\lambda (H0: (lt n 
d)).(let H1 \def (eq_ind T (lift h d (TLRef n)) (\lambda (t0: T).(eq T (THead 
k u t) t0)) H (TLRef n) (lift_lref_lt n h d H0)) in (let H2 \def (match H1 in 
eq return (\lambda (t0: T).(\lambda (_: (eq ? ? t0)).((eq T t0 (TLRef n)) \to 
(ex3_2 T T (\lambda (y: T).(\lambda (z: T).(eq T (TLRef n) (THead k y z)))) 
(\lambda (y: T).(\lambda (_: T).(eq T u (lift h d y)))) (\lambda (_: 
T).(\lambda (z: T).(eq T t (lift h (s k d) z)))))))) with [refl_equal 
\Rightarrow (\lambda (H2: (eq T (THead k u t) (TLRef n))).(let H3 \def 
(eq_ind T (THead k u t) (\lambda (e: T).(match e in T return (\lambda (_: 
T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | 
(THead _ _ _) \Rightarrow True])) I (TLRef n) H2) in (False_ind (ex3_2 T T 
(\lambda (y: T).(\lambda (z: T).(eq T (TLRef n) (THead k y z)))) (\lambda (y: 
T).(\lambda (_: T).(eq T u (lift h d y)))) (\lambda (_: T).(\lambda (z: 
T).(eq T t (lift h (s k d) z))))) H3)))]) in (H2 (refl_equal T (TLRef n)))))) 
(\lambda (H0: (le d n)).(let H1 \def (eq_ind T (lift h d (TLRef n)) (\lambda 
(t0: T).(eq T (THead k u t) t0)) H (TLRef (plus n h)) (lift_lref_ge n h d 
H0)) in (let H2 \def (match H1 in eq return (\lambda (t0: T).(\lambda (_: (eq 
? ? t0)).((eq T t0 (TLRef (plus n h))) \to (ex3_2 T T (\lambda (y: 
T).(\lambda (z: T).(eq T (TLRef n) (THead k y z)))) (\lambda (y: T).(\lambda 
(_: T).(eq T u (lift h d y)))) (\lambda (_: T).(\lambda (z: T).(eq T t (lift 
h (s k d) z)))))))) with [refl_equal \Rightarrow (\lambda (H2: (eq T (THead k 
u t) (TLRef (plus n h)))).(let H3 \def (eq_ind T (THead k u t) (\lambda (e: 
T).(match e in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow 
False | (TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow True])) I 
(TLRef (plus n h)) H2) in (False_ind (ex3_2 T T (\lambda (y: T).(\lambda (z: 
T).(eq T (TLRef n) (THead k y z)))) (\lambda (y: T).(\lambda (_: T).(eq T u 
(lift h d y)))) (\lambda (_: T).(\lambda (z: T).(eq T t (lift h (s k d) 
z))))) H3)))]) in (H2 (refl_equal T (TLRef (plus n h)))))))))))) (\lambda 
(k0: K).(\lambda (t0: T).(\lambda (_: ((\forall (h: nat).(\forall (d: 
nat).((eq T (THead k u t) (lift h d t0)) \to (ex3_2 T T (\lambda (y: 
T).(\lambda (z: T).(eq T t0 (THead k y z)))) (\lambda (y: T).(\lambda (_: 
T).(eq T u (lift h d y)))) (\lambda (_: T).(\lambda (z: T).(eq T t (lift h (s 
k d) z)))))))))).(\lambda (t1: T).(\lambda (_: ((\forall (h: nat).(\forall 
(d: nat).((eq T (THead k u t) (lift h d t1)) \to (ex3_2 T T (\lambda (y: 
T).(\lambda (z: T).(eq T t1 (THead k y z)))) (\lambda (y: T).(\lambda (_: 
T).(eq T u (lift h d y)))) (\lambda (_: T).(\lambda (z: T).(eq T t (lift h (s 
k d) z)))))))))).(\lambda (h: nat).(\lambda (d: nat).(\lambda (H1: (eq T 
(THead k u t) (lift h d (THead k0 t0 t1)))).(let H2 \def (eq_ind T (lift h d 
(THead k0 t0 t1)) (\lambda (t2: T).(eq T (THead k u t) t2)) H1 (THead k0 
(lift h d t0) (lift h (s k0 d) t1)) (lift_head k0 t0 t1 h d)) in (let H3 \def 
(match H2 in eq return (\lambda (t2: T).(\lambda (_: (eq ? ? t2)).((eq T t2 
(THead k0 (lift h d t0) (lift h (s k0 d) t1))) \to (ex3_2 T T (\lambda (y: 
T).(\lambda (z: T).(eq T (THead k0 t0 t1) (THead k y z)))) (\lambda (y: 
T).(\lambda (_: T).(eq T u (lift h d y)))) (\lambda (_: T).(\lambda (z: 
T).(eq T t (lift h (s k d) z)))))))) with [refl_equal \Rightarrow (\lambda 
(H3: (eq T (THead k u t) (THead k0 (lift h d t0) (lift h (s k0 d) t1)))).(let 
H4 \def (f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) 
with [(TSort _) \Rightarrow t | (TLRef _) \Rightarrow t | (THead _ _ t2) 
\Rightarrow t2])) (THead k u t) (THead k0 (lift h d t0) (lift h (s k0 d) t1)) 
H3) in ((let H5 \def (f_equal T T (\lambda (e: T).(match e in T return 
(\lambda (_: T).T) with [(TSort _) \Rightarrow u | (TLRef _) \Rightarrow u | 
(THead _ t2 _) \Rightarrow t2])) (THead k u t) (THead k0 (lift h d t0) (lift 
h (s k0 d) t1)) H3) in ((let H6 \def (f_equal T K (\lambda (e: T).(match e in 
T return (\lambda (_: T).K) with [(TSort _) \Rightarrow k | (TLRef _) 
\Rightarrow k | (THead k1 _ _) \Rightarrow k1])) (THead k u t) (THead k0 
(lift h d t0) (lift h (s k0 d) t1)) H3) in (eq_ind K k0 (\lambda (k1: K).((eq 
T u (lift h d t0)) \to ((eq T t (lift h (s k0 d) t1)) \to (ex3_2 T T (\lambda 
(y: T).(\lambda (z: T).(eq T (THead k0 t0 t1) (THead k1 y z)))) (\lambda (y: 
T).(\lambda (_: T).(eq T u (lift h d y)))) (\lambda (_: T).(\lambda (z: 
T).(eq T t (lift h (s k1 d) z)))))))) (\lambda (H7: (eq T u (lift h d 
t0))).(eq_ind T (lift h d t0) (\lambda (t2: T).((eq T t (lift h (s k0 d) t1)) 
\to (ex3_2 T T (\lambda (y: T).(\lambda (z: T).(eq T (THead k0 t0 t1) (THead 
k0 y z)))) (\lambda (y: T).(\lambda (_: T).(eq T t2 (lift h d y)))) (\lambda 
(_: T).(\lambda (z: T).(eq T t (lift h (s k0 d) z))))))) (\lambda (H8: (eq T 
t (lift h (s k0 d) t1))).(eq_ind T (lift h (s k0 d) t1) (\lambda (t2: 
T).(ex3_2 T T (\lambda (y: T).(\lambda (z: T).(eq T (THead k0 t0 t1) (THead 
k0 y z)))) (\lambda (y: T).(\lambda (_: T).(eq T (lift h d t0) (lift h d 
y)))) (\lambda (_: T).(\lambda (z: T).(eq T t2 (lift h (s k0 d) z)))))) 
(ex3_2_intro T T (\lambda (y: T).(\lambda (z: T).(eq T (THead k0 t0 t1) 
(THead k0 y z)))) (\lambda (y: T).(\lambda (_: T).(eq T (lift h d t0) (lift h 
d y)))) (\lambda (_: T).(\lambda (z: T).(eq T (lift h (s k0 d) t1) (lift h (s 
k0 d) z)))) t0 t1 (refl_equal T (THead k0 t0 t1)) (refl_equal T (lift h d 
t0)) (refl_equal T (lift h (s k0 d) t1))) t (sym_eq T t (lift h (s k0 d) t1) 
H8))) u (sym_eq T u (lift h d t0) H7))) k (sym_eq K k k0 H6))) H5)) H4)))]) 
in (H3 (refl_equal T (THead k0 (lift h d t0) (lift h (s k0 d) 
t1)))))))))))))) x)))).

theorem lift_gen_bind:
 \forall (b: B).(\forall (u: T).(\forall (t: T).(\forall (x: T).(\forall (h: 
nat).(\forall (d: nat).((eq T (THead (Bind b) u t) (lift h d x)) \to (ex3_2 T 
T (\lambda (y: T).(\lambda (z: T).(eq T x (THead (Bind b) y z)))) (\lambda 
(y: T).(\lambda (_: T).(eq T u (lift h d y)))) (\lambda (_: T).(\lambda (z: 
T).(eq T t (lift h (S d) z)))))))))))
\def
 \lambda (b: B).(\lambda (u: T).(\lambda (t: T).(\lambda (x: T).(T_ind 
(\lambda (t0: T).(\forall (h: nat).(\forall (d: nat).((eq T (THead (Bind b) u 
t) (lift h d t0)) \to (ex3_2 T T (\lambda (y: T).(\lambda (z: T).(eq T t0 
(THead (Bind b) y z)))) (\lambda (y: T).(\lambda (_: T).(eq T u (lift h d 
y)))) (\lambda (_: T).(\lambda (z: T).(eq T t (lift h (S d) z))))))))) 
(\lambda (n: nat).(\lambda (h: nat).(\lambda (d: nat).(\lambda (H: (eq T 
(THead (Bind b) u t) (lift h d (TSort n)))).(let H0 \def (match H in eq 
return (\lambda (t0: T).(\lambda (_: (eq ? ? t0)).((eq T t0 (lift h d (TSort 
n))) \to (ex3_2 T T (\lambda (y: T).(\lambda (z: T).(eq T (TSort n) (THead 
(Bind b) y z)))) (\lambda (y: T).(\lambda (_: T).(eq T u (lift h d y)))) 
(\lambda (_: T).(\lambda (z: T).(eq T t (lift h (S d) z)))))))) with 
[refl_equal \Rightarrow (\lambda (H0: (eq T (THead (Bind b) u t) (lift h d 
(TSort n)))).(let H1 \def (eq_ind T (THead (Bind b) u t) (\lambda (e: 
T).(match e in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow 
False | (TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow True])) I 
(lift h d (TSort n)) H0) in (False_ind (ex3_2 T T (\lambda (y: T).(\lambda 
(z: T).(eq T (TSort n) (THead (Bind b) y z)))) (\lambda (y: T).(\lambda (_: 
T).(eq T u (lift h d y)))) (\lambda (_: T).(\lambda (z: T).(eq T t (lift h (S 
d) z))))) H1)))]) in (H0 (refl_equal T (lift h d (TSort n))))))))) (\lambda 
(n: nat).(\lambda (h: nat).(\lambda (d: nat).(\lambda (H: (eq T (THead (Bind 
b) u t) (lift h d (TLRef n)))).(lt_le_e n d (ex3_2 T T (\lambda (y: 
T).(\lambda (z: T).(eq T (TLRef n) (THead (Bind b) y z)))) (\lambda (y: 
T).(\lambda (_: T).(eq T u (lift h d y)))) (\lambda (_: T).(\lambda (z: 
T).(eq T t (lift h (S d) z))))) (\lambda (H0: (lt n d)).(let H1 \def (eq_ind 
T (lift h d (TLRef n)) (\lambda (t0: T).(eq T (THead (Bind b) u t) t0)) H 
(TLRef n) (lift_lref_lt n h d H0)) in (let H2 \def (match H1 in eq return 
(\lambda (t0: T).(\lambda (_: (eq ? ? t0)).((eq T t0 (TLRef n)) \to (ex3_2 T 
T (\lambda (y: T).(\lambda (z: T).(eq T (TLRef n) (THead (Bind b) y z)))) 
(\lambda (y: T).(\lambda (_: T).(eq T u (lift h d y)))) (\lambda (_: 
T).(\lambda (z: T).(eq T t (lift h (S d) z)))))))) with [refl_equal 
\Rightarrow (\lambda (H2: (eq T (THead (Bind b) u t) (TLRef n))).(let H3 \def 
(eq_ind T (THead (Bind b) u t) (\lambda (e: T).(match e in T return (\lambda 
(_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False 
| (THead _ _ _) \Rightarrow True])) I (TLRef n) H2) in (False_ind (ex3_2 T T 
(\lambda (y: T).(\lambda (z: T).(eq T (TLRef n) (THead (Bind b) y z)))) 
(\lambda (y: T).(\lambda (_: T).(eq T u (lift h d y)))) (\lambda (_: 
T).(\lambda (z: T).(eq T t (lift h (S d) z))))) H3)))]) in (H2 (refl_equal T 
(TLRef n)))))) (\lambda (H0: (le d n)).(let H1 \def (eq_ind T (lift h d 
(TLRef n)) (\lambda (t0: T).(eq T (THead (Bind b) u t) t0)) H (TLRef (plus n 
h)) (lift_lref_ge n h d H0)) in (let H2 \def (match H1 in eq return (\lambda 
(t0: T).(\lambda (_: (eq ? ? t0)).((eq T t0 (TLRef (plus n h))) \to (ex3_2 T 
T (\lambda (y: T).(\lambda (z: T).(eq T (TLRef n) (THead (Bind b) y z)))) 
(\lambda (y: T).(\lambda (_: T).(eq T u (lift h d y)))) (\lambda (_: 
T).(\lambda (z: T).(eq T t (lift h (S d) z)))))))) with [refl_equal 
\Rightarrow (\lambda (H2: (eq T (THead (Bind b) u t) (TLRef (plus n 
h)))).(let H3 \def (eq_ind T (THead (Bind b) u t) (\lambda (e: T).(match e in 
T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow False | (THead _ _ _) \Rightarrow True])) I (TLRef (plus n h)) 
H2) in (False_ind (ex3_2 T T (\lambda (y: T).(\lambda (z: T).(eq T (TLRef n) 
(THead (Bind b) y z)))) (\lambda (y: T).(\lambda (_: T).(eq T u (lift h d 
y)))) (\lambda (_: T).(\lambda (z: T).(eq T t (lift h (S d) z))))) H3)))]) in 
(H2 (refl_equal T (TLRef (plus n h)))))))))))) (\lambda (k: K).(\lambda (t0: 
T).(\lambda (_: ((\forall (h: nat).(\forall (d: nat).((eq T (THead (Bind b) u 
t) (lift h d t0)) \to (ex3_2 T T (\lambda (y: T).(\lambda (z: T).(eq T t0 
(THead (Bind b) y z)))) (\lambda (y: T).(\lambda (_: T).(eq T u (lift h d 
y)))) (\lambda (_: T).(\lambda (z: T).(eq T t (lift h (S d) 
z)))))))))).(\lambda (t1: T).(\lambda (_: ((\forall (h: nat).(\forall (d: 
nat).((eq T (THead (Bind b) u t) (lift h d t1)) \to (ex3_2 T T (\lambda (y: 
T).(\lambda (z: T).(eq T t1 (THead (Bind b) y z)))) (\lambda (y: T).(\lambda 
(_: T).(eq T u (lift h d y)))) (\lambda (_: T).(\lambda (z: T).(eq T t (lift 
h (S d) z)))))))))).(\lambda (h: nat).(\lambda (d: nat).(\lambda (H1: (eq T 
(THead (Bind b) u t) (lift h d (THead k t0 t1)))).(let H2 \def (eq_ind T 
(lift h d (THead k t0 t1)) (\lambda (t2: T).(eq T (THead (Bind b) u t) t2)) 
H1 (THead k (lift h d t0) (lift h (s k d) t1)) (lift_head k t0 t1 h d)) in 
(let H3 \def (match H2 in eq return (\lambda (t2: T).(\lambda (_: (eq ? ? 
t2)).((eq T t2 (THead k (lift h d t0) (lift h (s k d) t1))) \to (ex3_2 T T 
(\lambda (y: T).(\lambda (z: T).(eq T (THead k t0 t1) (THead (Bind b) y z)))) 
(\lambda (y: T).(\lambda (_: T).(eq T u (lift h d y)))) (\lambda (_: 
T).(\lambda (z: T).(eq T t (lift h (S d) z)))))))) with [refl_equal 
\Rightarrow (\lambda (H3: (eq T (THead (Bind b) u t) (THead k (lift h d t0) 
(lift h (s k d) t1)))).(let H4 \def (f_equal T T (\lambda (e: T).(match e in 
T return (\lambda (_: T).T) with [(TSort _) \Rightarrow t | (TLRef _) 
\Rightarrow t | (THead _ _ t2) \Rightarrow t2])) (THead (Bind b) u t) (THead 
k (lift h d t0) (lift h (s k d) t1)) H3) in ((let H5 \def (f_equal T T 
(\lambda (e: T).(match e in T return (\lambda (_: T).T) with [(TSort _) 
\Rightarrow u | (TLRef _) \Rightarrow u | (THead _ t2 _) \Rightarrow t2])) 
(THead (Bind b) u t) (THead k (lift h d t0) (lift h (s k d) t1)) H3) in ((let 
H6 \def (f_equal T K (\lambda (e: T).(match e in T return (\lambda (_: T).K) 
with [(TSort _) \Rightarrow (Bind b) | (TLRef _) \Rightarrow (Bind b) | 
(THead k0 _ _) \Rightarrow k0])) (THead (Bind b) u t) (THead k (lift h d t0) 
(lift h (s k d) t1)) H3) in (eq_ind K (Bind b) (\lambda (k0: K).((eq T u 
(lift h d t0)) \to ((eq T t (lift h (s k0 d) t1)) \to (ex3_2 T T (\lambda (y: 
T).(\lambda (z: T).(eq T (THead k0 t0 t1) (THead (Bind b) y z)))) (\lambda 
(y: T).(\lambda (_: T).(eq T u (lift h d y)))) (\lambda (_: T).(\lambda (z: 
T).(eq T t (lift h (S d) z)))))))) (\lambda (H7: (eq T u (lift h d 
t0))).(eq_ind T (lift h d t0) (\lambda (t2: T).((eq T t (lift h (s (Bind b) 
d) t1)) \to (ex3_2 T T (\lambda (y: T).(\lambda (z: T).(eq T (THead (Bind b) 
t0 t1) (THead (Bind b) y z)))) (\lambda (y: T).(\lambda (_: T).(eq T t2 (lift 
h d y)))) (\lambda (_: T).(\lambda (z: T).(eq T t (lift h (S d) z))))))) 
(\lambda (H8: (eq T t (lift h (s (Bind b) d) t1))).(eq_ind T (lift h (s (Bind 
b) d) t1) (\lambda (t2: T).(ex3_2 T T (\lambda (y: T).(\lambda (z: T).(eq T 
(THead (Bind b) t0 t1) (THead (Bind b) y z)))) (\lambda (y: T).(\lambda (_: 
T).(eq T (lift h d t0) (lift h d y)))) (\lambda (_: T).(\lambda (z: T).(eq T 
t2 (lift h (S d) z)))))) (ex3_2_intro T T (\lambda (y: T).(\lambda (z: T).(eq 
T (THead (Bind b) t0 t1) (THead (Bind b) y z)))) (\lambda (y: T).(\lambda (_: 
T).(eq T (lift h d t0) (lift h d y)))) (\lambda (_: T).(\lambda (z: T).(eq T 
(lift h (s (Bind b) d) t1) (lift h (S d) z)))) t0 t1 (refl_equal T (THead 
(Bind b) t0 t1)) (refl_equal T (lift h d t0)) (refl_equal T (lift h (S d) 
t1))) t (sym_eq T t (lift h (s (Bind b) d) t1) H8))) u (sym_eq T u (lift h d 
t0) H7))) k H6)) H5)) H4)))]) in (H3 (refl_equal T (THead k (lift h d t0) 
(lift h (s k d) t1)))))))))))))) x)))).

theorem lift_gen_flat:
 \forall (f: F).(\forall (u: T).(\forall (t: T).(\forall (x: T).(\forall (h: 
nat).(\forall (d: nat).((eq T (THead (Flat f) u t) (lift h d x)) \to (ex3_2 T 
T (\lambda (y: T).(\lambda (z: T).(eq T x (THead (Flat f) y z)))) (\lambda 
(y: T).(\lambda (_: T).(eq T u (lift h d y)))) (\lambda (_: T).(\lambda (z: 
T).(eq T t (lift h d z)))))))))))
\def
 \lambda (f: F).(\lambda (u: T).(\lambda (t: T).(\lambda (x: T).(T_ind 
(\lambda (t0: T).(\forall (h: nat).(\forall (d: nat).((eq T (THead (Flat f) u 
t) (lift h d t0)) \to (ex3_2 T T (\lambda (y: T).(\lambda (z: T).(eq T t0 
(THead (Flat f) y z)))) (\lambda (y: T).(\lambda (_: T).(eq T u (lift h d 
y)))) (\lambda (_: T).(\lambda (z: T).(eq T t (lift h d z))))))))) (\lambda 
(n: nat).(\lambda (h: nat).(\lambda (d: nat).(\lambda (H: (eq T (THead (Flat 
f) u t) (lift h d (TSort n)))).(let H0 \def (match H in eq return (\lambda 
(t0: T).(\lambda (_: (eq ? ? t0)).((eq T t0 (lift h d (TSort n))) \to (ex3_2 
T T (\lambda (y: T).(\lambda (z: T).(eq T (TSort n) (THead (Flat f) y z)))) 
(\lambda (y: T).(\lambda (_: T).(eq T u (lift h d y)))) (\lambda (_: 
T).(\lambda (z: T).(eq T t (lift h d z)))))))) with [refl_equal \Rightarrow 
(\lambda (H0: (eq T (THead (Flat f) u t) (lift h d (TSort n)))).(let H1 \def 
(eq_ind T (THead (Flat f) u t) (\lambda (e: T).(match e in T return (\lambda 
(_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False 
| (THead _ _ _) \Rightarrow True])) I (lift h d (TSort n)) H0) in (False_ind 
(ex3_2 T T (\lambda (y: T).(\lambda (z: T).(eq T (TSort n) (THead (Flat f) y 
z)))) (\lambda (y: T).(\lambda (_: T).(eq T u (lift h d y)))) (\lambda (_: 
T).(\lambda (z: T).(eq T t (lift h d z))))) H1)))]) in (H0 (refl_equal T 
(lift h d (TSort n))))))))) (\lambda (n: nat).(\lambda (h: nat).(\lambda (d: 
nat).(\lambda (H: (eq T (THead (Flat f) u t) (lift h d (TLRef n)))).(lt_le_e 
n d (ex3_2 T T (\lambda (y: T).(\lambda (z: T).(eq T (TLRef n) (THead (Flat 
f) y z)))) (\lambda (y: T).(\lambda (_: T).(eq T u (lift h d y)))) (\lambda 
(_: T).(\lambda (z: T).(eq T t (lift h d z))))) (\lambda (H0: (lt n d)).(let 
H1 \def (eq_ind T (lift h d (TLRef n)) (\lambda (t0: T).(eq T (THead (Flat f) 
u t) t0)) H (TLRef n) (lift_lref_lt n h d H0)) in (let H2 \def (match H1 in 
eq return (\lambda (t0: T).(\lambda (_: (eq ? ? t0)).((eq T t0 (TLRef n)) \to 
(ex3_2 T T (\lambda (y: T).(\lambda (z: T).(eq T (TLRef n) (THead (Flat f) y 
z)))) (\lambda (y: T).(\lambda (_: T).(eq T u (lift h d y)))) (\lambda (_: 
T).(\lambda (z: T).(eq T t (lift h d z)))))))) with [refl_equal \Rightarrow 
(\lambda (H2: (eq T (THead (Flat f) u t) (TLRef n))).(let H3 \def (eq_ind T 
(THead (Flat f) u t) (\lambda (e: T).(match e in T return (\lambda (_: 
T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | 
(THead _ _ _) \Rightarrow True])) I (TLRef n) H2) in (False_ind (ex3_2 T T 
(\lambda (y: T).(\lambda (z: T).(eq T (TLRef n) (THead (Flat f) y z)))) 
(\lambda (y: T).(\lambda (_: T).(eq T u (lift h d y)))) (\lambda (_: 
T).(\lambda (z: T).(eq T t (lift h d z))))) H3)))]) in (H2 (refl_equal T 
(TLRef n)))))) (\lambda (H0: (le d n)).(let H1 \def (eq_ind T (lift h d 
(TLRef n)) (\lambda (t0: T).(eq T (THead (Flat f) u t) t0)) H (TLRef (plus n 
h)) (lift_lref_ge n h d H0)) in (let H2 \def (match H1 in eq return (\lambda 
(t0: T).(\lambda (_: (eq ? ? t0)).((eq T t0 (TLRef (plus n h))) \to (ex3_2 T 
T (\lambda (y: T).(\lambda (z: T).(eq T (TLRef n) (THead (Flat f) y z)))) 
(\lambda (y: T).(\lambda (_: T).(eq T u (lift h d y)))) (\lambda (_: 
T).(\lambda (z: T).(eq T t (lift h d z)))))))) with [refl_equal \Rightarrow 
(\lambda (H2: (eq T (THead (Flat f) u t) (TLRef (plus n h)))).(let H3 \def 
(eq_ind T (THead (Flat f) u t) (\lambda (e: T).(match e in T return (\lambda 
(_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False 
| (THead _ _ _) \Rightarrow True])) I (TLRef (plus n h)) H2) in (False_ind 
(ex3_2 T T (\lambda (y: T).(\lambda (z: T).(eq T (TLRef n) (THead (Flat f) y 
z)))) (\lambda (y: T).(\lambda (_: T).(eq T u (lift h d y)))) (\lambda (_: 
T).(\lambda (z: T).(eq T t (lift h d z))))) H3)))]) in (H2 (refl_equal T 
(TLRef (plus n h)))))))))))) (\lambda (k: K).(\lambda (t0: T).(\lambda (_: 
((\forall (h: nat).(\forall (d: nat).((eq T (THead (Flat f) u t) (lift h d 
t0)) \to (ex3_2 T T (\lambda (y: T).(\lambda (z: T).(eq T t0 (THead (Flat f) 
y z)))) (\lambda (y: T).(\lambda (_: T).(eq T u (lift h d y)))) (\lambda (_: 
T).(\lambda (z: T).(eq T t (lift h d z)))))))))).(\lambda (t1: T).(\lambda 
(_: ((\forall (h: nat).(\forall (d: nat).((eq T (THead (Flat f) u t) (lift h 
d t1)) \to (ex3_2 T T (\lambda (y: T).(\lambda (z: T).(eq T t1 (THead (Flat 
f) y z)))) (\lambda (y: T).(\lambda (_: T).(eq T u (lift h d y)))) (\lambda 
(_: T).(\lambda (z: T).(eq T t (lift h d z)))))))))).(\lambda (h: 
nat).(\lambda (d: nat).(\lambda (H1: (eq T (THead (Flat f) u t) (lift h d 
(THead k t0 t1)))).(let H2 \def (eq_ind T (lift h d (THead k t0 t1)) (\lambda 
(t2: T).(eq T (THead (Flat f) u t) t2)) H1 (THead k (lift h d t0) (lift h (s 
k d) t1)) (lift_head k t0 t1 h d)) in (let H3 \def (match H2 in eq return 
(\lambda (t2: T).(\lambda (_: (eq ? ? t2)).((eq T t2 (THead k (lift h d t0) 
(lift h (s k d) t1))) \to (ex3_2 T T (\lambda (y: T).(\lambda (z: T).(eq T 
(THead k t0 t1) (THead (Flat f) y z)))) (\lambda (y: T).(\lambda (_: T).(eq T 
u (lift h d y)))) (\lambda (_: T).(\lambda (z: T).(eq T t (lift h d z)))))))) 
with [refl_equal \Rightarrow (\lambda (H3: (eq T (THead (Flat f) u t) (THead 
k (lift h d t0) (lift h (s k d) t1)))).(let H4 \def (f_equal T T (\lambda (e: 
T).(match e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow t | 
(TLRef _) \Rightarrow t | (THead _ _ t2) \Rightarrow t2])) (THead (Flat f) u 
t) (THead k (lift h d t0) (lift h (s k d) t1)) H3) in ((let H5 \def (f_equal 
T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) with [(TSort _) 
\Rightarrow u | (TLRef _) \Rightarrow u | (THead _ t2 _) \Rightarrow t2])) 
(THead (Flat f) u t) (THead k (lift h d t0) (lift h (s k d) t1)) H3) in ((let 
H6 \def (f_equal T K (\lambda (e: T).(match e in T return (\lambda (_: T).K) 
with [(TSort _) \Rightarrow (Flat f) | (TLRef _) \Rightarrow (Flat f) | 
(THead k0 _ _) \Rightarrow k0])) (THead (Flat f) u t) (THead k (lift h d t0) 
(lift h (s k d) t1)) H3) in (eq_ind K (Flat f) (\lambda (k0: K).((eq T u 
(lift h d t0)) \to ((eq T t (lift h (s k0 d) t1)) \to (ex3_2 T T (\lambda (y: 
T).(\lambda (z: T).(eq T (THead k0 t0 t1) (THead (Flat f) y z)))) (\lambda 
(y: T).(\lambda (_: T).(eq T u (lift h d y)))) (\lambda (_: T).(\lambda (z: 
T).(eq T t (lift h d z)))))))) (\lambda (H7: (eq T u (lift h d t0))).(eq_ind 
T (lift h d t0) (\lambda (t2: T).((eq T t (lift h (s (Flat f) d) t1)) \to 
(ex3_2 T T (\lambda (y: T).(\lambda (z: T).(eq T (THead (Flat f) t0 t1) 
(THead (Flat f) y z)))) (\lambda (y: T).(\lambda (_: T).(eq T t2 (lift h d 
y)))) (\lambda (_: T).(\lambda (z: T).(eq T t (lift h d z))))))) (\lambda 
(H8: (eq T t (lift h (s (Flat f) d) t1))).(eq_ind T (lift h (s (Flat f) d) 
t1) (\lambda (t2: T).(ex3_2 T T (\lambda (y: T).(\lambda (z: T).(eq T (THead 
(Flat f) t0 t1) (THead (Flat f) y z)))) (\lambda (y: T).(\lambda (_: T).(eq T 
(lift h d t0) (lift h d y)))) (\lambda (_: T).(\lambda (z: T).(eq T t2 (lift 
h d z)))))) (ex3_2_intro T T (\lambda (y: T).(\lambda (z: T).(eq T (THead 
(Flat f) t0 t1) (THead (Flat f) y z)))) (\lambda (y: T).(\lambda (_: T).(eq T 
(lift h d t0) (lift h d y)))) (\lambda (_: T).(\lambda (z: T).(eq T (lift h 
(s (Flat f) d) t1) (lift h d z)))) t0 t1 (refl_equal T (THead (Flat f) t0 
t1)) (refl_equal T (lift h d t0)) (refl_equal T (lift h d t1))) t (sym_eq T t 
(lift h (s (Flat f) d) t1) H8))) u (sym_eq T u (lift h d t0) H7))) k H6)) 
H5)) H4)))]) in (H3 (refl_equal T (THead k (lift h d t0) (lift h (s k d) 
t1)))))))))))))) x)))).

