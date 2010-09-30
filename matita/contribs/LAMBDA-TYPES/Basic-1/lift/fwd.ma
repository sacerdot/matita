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

include "Basic-1/lift/defs.ma".

theorem lift_sort:
 \forall (n: nat).(\forall (h: nat).(\forall (d: nat).(eq T (lift h d (TSort 
n)) (TSort n))))
\def
 \lambda (n: nat).(\lambda (_: nat).(\lambda (_: nat).(refl_equal T (TSort 
n)))).
(* COMMENTS
Initial nodes: 13
END *)

theorem lift_lref_lt:
 \forall (n: nat).(\forall (h: nat).(\forall (d: nat).((lt n d) \to (eq T 
(lift h d (TLRef n)) (TLRef n)))))
\def
 \lambda (n: nat).(\lambda (h: nat).(\lambda (d: nat).(\lambda (H: (lt n 
d)).(eq_ind bool true (\lambda (b: bool).(eq T (TLRef (match b with [true 
\Rightarrow n | false \Rightarrow (plus n h)])) (TLRef n))) (refl_equal T 
(TLRef n)) (blt n d) (sym_eq bool (blt n d) true (lt_blt d n H)))))).
(* COMMENTS
Initial nodes: 72
END *)

theorem lift_lref_ge:
 \forall (n: nat).(\forall (h: nat).(\forall (d: nat).((le d n) \to (eq T 
(lift h d (TLRef n)) (TLRef (plus n h))))))
\def
 \lambda (n: nat).(\lambda (h: nat).(\lambda (d: nat).(\lambda (H: (le d 
n)).(eq_ind bool false (\lambda (b: bool).(eq T (TLRef (match b with [true 
\Rightarrow n | false \Rightarrow (plus n h)])) (TLRef (plus n h)))) 
(refl_equal T (TLRef (plus n h))) (blt n d) (sym_eq bool (blt n d) false 
(le_bge d n H)))))).
(* COMMENTS
Initial nodes: 80
END *)

theorem lift_head:
 \forall (k: K).(\forall (u: T).(\forall (t: T).(\forall (h: nat).(\forall 
(d: nat).(eq T (lift h d (THead k u t)) (THead k (lift h d u) (lift h (s k d) 
t)))))))
\def
 \lambda (k: K).(\lambda (u: T).(\lambda (t: T).(\lambda (h: nat).(\lambda 
(d: nat).(refl_equal T (THead k (lift h d u) (lift h (s k d) t))))))).
(* COMMENTS
Initial nodes: 37
END *)

theorem lift_bind:
 \forall (b: B).(\forall (u: T).(\forall (t: T).(\forall (h: nat).(\forall 
(d: nat).(eq T (lift h d (THead (Bind b) u t)) (THead (Bind b) (lift h d u) 
(lift h (S d) t)))))))
\def
 \lambda (b: B).(\lambda (u: T).(\lambda (t: T).(\lambda (h: nat).(\lambda 
(d: nat).(refl_equal T (THead (Bind b) (lift h d u) (lift h (S d) t))))))).
(* COMMENTS
Initial nodes: 37
END *)

theorem lift_flat:
 \forall (f: F).(\forall (u: T).(\forall (t: T).(\forall (h: nat).(\forall 
(d: nat).(eq T (lift h d (THead (Flat f) u t)) (THead (Flat f) (lift h d u) 
(lift h d t)))))))
\def
 \lambda (f: F).(\lambda (u: T).(\lambda (t: T).(\lambda (h: nat).(\lambda 
(d: nat).(refl_equal T (THead (Flat f) (lift h d u) (lift h d t))))))).
(* COMMENTS
Initial nodes: 35
END *)

theorem lift_gen_sort:
 \forall (h: nat).(\forall (d: nat).(\forall (n: nat).(\forall (t: T).((eq T 
(TSort n) (lift h d t)) \to (eq T t (TSort n))))))
\def
 \lambda (h: nat).(\lambda (d: nat).(\lambda (n: nat).(\lambda (t: T).(T_ind 
(\lambda (t0: T).((eq T (TSort n) (lift h d t0)) \to (eq T t0 (TSort n)))) 
(\lambda (n0: nat).(\lambda (H: (eq T (TSort n) (lift h d (TSort 
n0)))).(sym_eq T (TSort n) (TSort n0) H))) (\lambda (n0: nat).(\lambda (H: 
(eq T (TSort n) (lift h d (TLRef n0)))).(lt_le_e n0 d (eq T (TLRef n0) (TSort 
n)) (\lambda (_: (lt n0 d)).(let H1 \def (eq_ind T (lift h d (TLRef n0)) 
(\lambda (t0: T).(eq T (TSort n) t0)) H (TLRef n0) (lift_lref_lt n0 h d (let 
H1 \def (eq_ind T (TSort n) (\lambda (ee: T).(match ee in T return (\lambda 
(_: T).Prop) with [(TSort _) \Rightarrow True | (TLRef _) \Rightarrow False | 
(THead _ _ _) \Rightarrow False])) I (lift h d (TLRef n0)) H) in (False_ind 
(lt n0 d) H1)))) in (let H2 \def (eq_ind T (TSort n) (\lambda (ee: T).(match 
ee in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow True | 
(TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow False])) I (TLRef n0) 
H1) in (False_ind (eq T (TLRef n0) (TSort n)) H2)))) (\lambda (_: (le d 
n0)).(let H1 \def (eq_ind T (lift h d (TLRef n0)) (\lambda (t0: T).(eq T 
(TSort n) t0)) H (TLRef (plus n0 h)) (lift_lref_ge n0 h d (let H1 \def 
(eq_ind T (TSort n) (\lambda (ee: T).(match ee in T return (\lambda (_: 
T).Prop) with [(TSort _) \Rightarrow True | (TLRef _) \Rightarrow False | 
(THead _ _ _) \Rightarrow False])) I (lift h d (TLRef n0)) H) in (False_ind 
(le d n0) H1)))) in (let H2 \def (eq_ind T (TSort n) (\lambda (ee: T).(match 
ee in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow True | 
(TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow False])) I (TLRef 
(plus n0 h)) H1) in (False_ind (eq T (TLRef n0) (TSort n)) H2))))))) (\lambda 
(k: K).(\lambda (t0: T).(\lambda (_: (((eq T (TSort n) (lift h d t0)) \to (eq 
T t0 (TSort n))))).(\lambda (t1: T).(\lambda (_: (((eq T (TSort n) (lift h d 
t1)) \to (eq T t1 (TSort n))))).(\lambda (H1: (eq T (TSort n) (lift h d 
(THead k t0 t1)))).(let H2 \def (eq_ind T (lift h d (THead k t0 t1)) (\lambda 
(t2: T).(eq T (TSort n) t2)) H1 (THead k (lift h d t0) (lift h (s k d) t1)) 
(lift_head k t0 t1 h d)) in (let H3 \def (eq_ind T (TSort n) (\lambda (ee: 
T).(match ee in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow 
True | (TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow False])) I 
(THead k (lift h d t0) (lift h (s k d) t1)) H2) in (False_ind (eq T (THead k 
t0 t1) (TSort n)) H3))))))))) t)))).
(* COMMENTS
Initial nodes: 613
END *)

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
(plus n h)) (eq T (TLRef n) (TLRef n)) (le_plus_plus d n h h H0 (le_n h)) 
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
(* COMMENTS
Initial nodes: 1221
END *)

theorem lift_gen_lref_lt:
 \forall (h: nat).(\forall (d: nat).(\forall (n: nat).((lt n d) \to (\forall 
(t: T).((eq T (TLRef n) (lift h d t)) \to (eq T t (TLRef n)))))))
\def
 \lambda (h: nat).(\lambda (d: nat).(\lambda (n: nat).(\lambda (H: (lt n 
d)).(\lambda (t: T).(\lambda (H0: (eq T (TLRef n) (lift h d t))).(let H_x 
\def (lift_gen_lref t d h n H0) in (let H1 \def H_x in (or_ind (land (lt n d) 
(eq T t (TLRef n))) (land (le (plus d h) n) (eq T t (TLRef (minus n h)))) (eq 
T t (TLRef n)) (\lambda (H2: (land (lt n d) (eq T t (TLRef n)))).(land_ind 
(lt n d) (eq T t (TLRef n)) (eq T t (TLRef n)) (\lambda (_: (lt n 
d)).(\lambda (H4: (eq T t (TLRef n))).(eq_ind_r T (TLRef n) (\lambda (t0: 
T).(eq T t0 (TLRef n))) (refl_equal T (TLRef n)) t H4))) H2)) (\lambda (H2: 
(land (le (plus d h) n) (eq T t (TLRef (minus n h))))).(land_ind (le (plus d 
h) n) (eq T t (TLRef (minus n h))) (eq T t (TLRef n)) (\lambda (H3: (le (plus 
d h) n)).(\lambda (H4: (eq T t (TLRef (minus n h)))).(eq_ind_r T (TLRef 
(minus n h)) (\lambda (t0: T).(eq T t0 (TLRef n))) (le_false (plus d h) n (eq 
T (TLRef (minus n h)) (TLRef n)) H3 (lt_le_S n (plus d h) (le_plus_trans (S 
n) d h H))) t H4))) H2)) H1)))))))).
(* COMMENTS
Initial nodes: 363
END *)

theorem lift_gen_lref_false:
 \forall (h: nat).(\forall (d: nat).(\forall (n: nat).((le d n) \to ((lt n 
(plus d h)) \to (\forall (t: T).((eq T (TLRef n) (lift h d t)) \to (\forall 
(P: Prop).P)))))))
\def
 \lambda (h: nat).(\lambda (d: nat).(\lambda (n: nat).(\lambda (H: (le d 
n)).(\lambda (H0: (lt n (plus d h))).(\lambda (t: T).(\lambda (H1: (eq T 
(TLRef n) (lift h d t))).(\lambda (P: Prop).(let H_x \def (lift_gen_lref t d 
h n H1) in (let H2 \def H_x in (or_ind (land (lt n d) (eq T t (TLRef n))) 
(land (le (plus d h) n) (eq T t (TLRef (minus n h)))) P (\lambda (H3: (land 
(lt n d) (eq T t (TLRef n)))).(land_ind (lt n d) (eq T t (TLRef n)) P 
(\lambda (H4: (lt n d)).(\lambda (_: (eq T t (TLRef n))).(le_false d n P H 
H4))) H3)) (\lambda (H3: (land (le (plus d h) n) (eq T t (TLRef (minus n 
h))))).(land_ind (le (plus d h) n) (eq T t (TLRef (minus n h))) P (\lambda 
(H4: (le (plus d h) n)).(\lambda (_: (eq T t (TLRef (minus n h)))).(le_false 
(plus d h) n P H4 H0))) H3)) H2)))))))))).
(* COMMENTS
Initial nodes: 269
END *)

theorem lift_gen_lref_ge:
 \forall (h: nat).(\forall (d: nat).(\forall (n: nat).((le d n) \to (\forall 
(t: T).((eq T (TLRef (plus n h)) (lift h d t)) \to (eq T t (TLRef n)))))))
\def
 \lambda (h: nat).(\lambda (d: nat).(\lambda (n: nat).(\lambda (H: (le d 
n)).(\lambda (t: T).(\lambda (H0: (eq T (TLRef (plus n h)) (lift h d 
t))).(let H_x \def (lift_gen_lref t d h (plus n h) H0) in (let H1 \def H_x in 
(or_ind (land (lt (plus n h) d) (eq T t (TLRef (plus n h)))) (land (le (plus 
d h) (plus n h)) (eq T t (TLRef (minus (plus n h) h)))) (eq T t (TLRef n)) 
(\lambda (H2: (land (lt (plus n h) d) (eq T t (TLRef (plus n h))))).(land_ind 
(lt (plus n h) d) (eq T t (TLRef (plus n h))) (eq T t (TLRef n)) (\lambda 
(H3: (lt (plus n h) d)).(\lambda (H4: (eq T t (TLRef (plus n h)))).(eq_ind_r 
T (TLRef (plus n h)) (\lambda (t0: T).(eq T t0 (TLRef n))) (le_false d n (eq 
T (TLRef (plus n h)) (TLRef n)) H (lt_le_S n d (simpl_lt_plus_r h n d 
(lt_le_trans (plus n h) d (plus d h) H3 (le_plus_l d h))))) t H4))) H2)) 
(\lambda (H2: (land (le (plus d h) (plus n h)) (eq T t (TLRef (minus (plus n 
h) h))))).(land_ind (le (plus d h) (plus n h)) (eq T t (TLRef (minus (plus n 
h) h))) (eq T t (TLRef n)) (\lambda (_: (le (plus d h) (plus n h))).(\lambda 
(H4: (eq T t (TLRef (minus (plus n h) h)))).(eq_ind_r T (TLRef (minus (plus n 
h) h)) (\lambda (t0: T).(eq T t0 (TLRef n))) (f_equal nat T TLRef (minus 
(plus n h) h) n (minus_plus_r n h)) t H4))) H2)) H1)))))))).
(* COMMENTS
Initial nodes: 473
END *)

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
(lift h d (TSort n)))).(let H0 \def (eq_ind T (lift h d (TSort n)) (\lambda 
(t0: T).(eq T (THead k u t) t0)) H (TSort n) (lift_sort n h d)) in (let H1 
\def (eq_ind T (THead k u t) (\lambda (ee: T).(match ee in T return (\lambda 
(_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False 
| (THead _ _ _) \Rightarrow True])) I (TSort n) H0) in (False_ind (ex3_2 T T 
(\lambda (y: T).(\lambda (z: T).(eq T (TSort n) (THead k y z)))) (\lambda (y: 
T).(\lambda (_: T).(eq T u (lift h d y)))) (\lambda (_: T).(\lambda (z: 
T).(eq T t (lift h (s k d) z))))) H1))))))) (\lambda (n: nat).(\lambda (h: 
nat).(\lambda (d: nat).(\lambda (H: (eq T (THead k u t) (lift h d (TLRef 
n)))).(lt_le_e n d (ex3_2 T T (\lambda (y: T).(\lambda (z: T).(eq T (TLRef n) 
(THead k y z)))) (\lambda (y: T).(\lambda (_: T).(eq T u (lift h d y)))) 
(\lambda (_: T).(\lambda (z: T).(eq T t (lift h (s k d) z))))) (\lambda (H0: 
(lt n d)).(let H1 \def (eq_ind T (lift h d (TLRef n)) (\lambda (t0: T).(eq T 
(THead k u t) t0)) H (TLRef n) (lift_lref_lt n h d H0)) in (let H2 \def 
(eq_ind T (THead k u t) (\lambda (ee: T).(match ee in T return (\lambda (_: 
T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | 
(THead _ _ _) \Rightarrow True])) I (TLRef n) H1) in (False_ind (ex3_2 T T 
(\lambda (y: T).(\lambda (z: T).(eq T (TLRef n) (THead k y z)))) (\lambda (y: 
T).(\lambda (_: T).(eq T u (lift h d y)))) (\lambda (_: T).(\lambda (z: 
T).(eq T t (lift h (s k d) z))))) H2)))) (\lambda (H0: (le d n)).(let H1 \def 
(eq_ind T (lift h d (TLRef n)) (\lambda (t0: T).(eq T (THead k u t) t0)) H 
(TLRef (plus n h)) (lift_lref_ge n h d H0)) in (let H2 \def (eq_ind T (THead 
k u t) (\lambda (ee: T).(match ee in T return (\lambda (_: T).Prop) with 
[(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | (THead _ _ _) 
\Rightarrow True])) I (TLRef (plus n h)) H1) in (False_ind (ex3_2 T T 
(\lambda (y: T).(\lambda (z: T).(eq T (TLRef n) (THead k y z)))) (\lambda (y: 
T).(\lambda (_: T).(eq T u (lift h d y)))) (\lambda (_: T).(\lambda (z: 
T).(eq T t (lift h (s k d) z))))) H2))))))))) (\lambda (k0: K).(\lambda (t0: 
T).(\lambda (H: ((\forall (h: nat).(\forall (d: nat).((eq T (THead k u t) 
(lift h d t0)) \to (ex3_2 T T (\lambda (y: T).(\lambda (z: T).(eq T t0 (THead 
k y z)))) (\lambda (y: T).(\lambda (_: T).(eq T u (lift h d y)))) (\lambda 
(_: T).(\lambda (z: T).(eq T t (lift h (s k d) z)))))))))).(\lambda (t1: 
T).(\lambda (H0: ((\forall (h: nat).(\forall (d: nat).((eq T (THead k u t) 
(lift h d t1)) \to (ex3_2 T T (\lambda (y: T).(\lambda (z: T).(eq T t1 (THead 
k y z)))) (\lambda (y: T).(\lambda (_: T).(eq T u (lift h d y)))) (\lambda 
(_: T).(\lambda (z: T).(eq T t (lift h (s k d) z)))))))))).(\lambda (h: 
nat).(\lambda (d: nat).(\lambda (H1: (eq T (THead k u t) (lift h d (THead k0 
t0 t1)))).(let H2 \def (eq_ind T (lift h d (THead k0 t0 t1)) (\lambda (t2: 
T).(eq T (THead k u t) t2)) H1 (THead k0 (lift h d t0) (lift h (s k0 d) t1)) 
(lift_head k0 t0 t1 h d)) in (let H3 \def (f_equal T K (\lambda (e: T).(match 
e in T return (\lambda (_: T).K) with [(TSort _) \Rightarrow k | (TLRef _) 
\Rightarrow k | (THead k1 _ _) \Rightarrow k1])) (THead k u t) (THead k0 
(lift h d t0) (lift h (s k0 d) t1)) H2) in ((let H4 \def (f_equal T T 
(\lambda (e: T).(match e in T return (\lambda (_: T).T) with [(TSort _) 
\Rightarrow u | (TLRef _) \Rightarrow u | (THead _ t2 _) \Rightarrow t2])) 
(THead k u t) (THead k0 (lift h d t0) (lift h (s k0 d) t1)) H2) in ((let H5 
\def (f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) 
with [(TSort _) \Rightarrow t | (TLRef _) \Rightarrow t | (THead _ _ t2) 
\Rightarrow t2])) (THead k u t) (THead k0 (lift h d t0) (lift h (s k0 d) t1)) 
H2) in (\lambda (H6: (eq T u (lift h d t0))).(\lambda (H7: (eq K k k0)).(let 
H8 \def (eq_ind_r K k0 (\lambda (k1: K).(eq T t (lift h (s k1 d) t1))) H5 k 
H7) in (eq_ind K k (\lambda (k1: K).(ex3_2 T T (\lambda (y: T).(\lambda (z: 
T).(eq T (THead k1 t0 t1) (THead k y z)))) (\lambda (y: T).(\lambda (_: 
T).(eq T u (lift h d y)))) (\lambda (_: T).(\lambda (z: T).(eq T t (lift h (s 
k d) z)))))) (let H9 \def (eq_ind T t (\lambda (t2: T).(\forall (h0: 
nat).(\forall (d0: nat).((eq T (THead k u t2) (lift h0 d0 t1)) \to (ex3_2 T T 
(\lambda (y: T).(\lambda (z: T).(eq T t1 (THead k y z)))) (\lambda (y: 
T).(\lambda (_: T).(eq T u (lift h0 d0 y)))) (\lambda (_: T).(\lambda (z: 
T).(eq T t2 (lift h0 (s k d0) z))))))))) H0 (lift h (s k d) t1) H8) in (let 
H10 \def (eq_ind T t (\lambda (t2: T).(\forall (h0: nat).(\forall (d0: 
nat).((eq T (THead k u t2) (lift h0 d0 t0)) \to (ex3_2 T T (\lambda (y: 
T).(\lambda (z: T).(eq T t0 (THead k y z)))) (\lambda (y: T).(\lambda (_: 
T).(eq T u (lift h0 d0 y)))) (\lambda (_: T).(\lambda (z: T).(eq T t2 (lift 
h0 (s k d0) z))))))))) H (lift h (s k d) t1) H8) in (eq_ind_r T (lift h (s k 
d) t1) (\lambda (t2: T).(ex3_2 T T (\lambda (y: T).(\lambda (z: T).(eq T 
(THead k t0 t1) (THead k y z)))) (\lambda (y: T).(\lambda (_: T).(eq T u 
(lift h d y)))) (\lambda (_: T).(\lambda (z: T).(eq T t2 (lift h (s k d) 
z)))))) (let H11 \def (eq_ind T u (\lambda (t2: T).(\forall (h0: 
nat).(\forall (d0: nat).((eq T (THead k t2 (lift h (s k d) t1)) (lift h0 d0 
t0)) \to (ex3_2 T T (\lambda (y: T).(\lambda (z: T).(eq T t0 (THead k y z)))) 
(\lambda (y: T).(\lambda (_: T).(eq T t2 (lift h0 d0 y)))) (\lambda (_: 
T).(\lambda (z: T).(eq T (lift h (s k d) t1) (lift h0 (s k d0) z))))))))) H10 
(lift h d t0) H6) in (let H12 \def (eq_ind T u (\lambda (t2: T).(\forall (h0: 
nat).(\forall (d0: nat).((eq T (THead k t2 (lift h (s k d) t1)) (lift h0 d0 
t1)) \to (ex3_2 T T (\lambda (y: T).(\lambda (z: T).(eq T t1 (THead k y z)))) 
(\lambda (y: T).(\lambda (_: T).(eq T t2 (lift h0 d0 y)))) (\lambda (_: 
T).(\lambda (z: T).(eq T (lift h (s k d) t1) (lift h0 (s k d0) z))))))))) H9 
(lift h d t0) H6) in (eq_ind_r T (lift h d t0) (\lambda (t2: T).(ex3_2 T T 
(\lambda (y: T).(\lambda (z: T).(eq T (THead k t0 t1) (THead k y z)))) 
(\lambda (y: T).(\lambda (_: T).(eq T t2 (lift h d y)))) (\lambda (_: 
T).(\lambda (z: T).(eq T (lift h (s k d) t1) (lift h (s k d) z)))))) 
(ex3_2_intro T T (\lambda (y: T).(\lambda (z: T).(eq T (THead k t0 t1) (THead 
k y z)))) (\lambda (y: T).(\lambda (_: T).(eq T (lift h d t0) (lift h d y)))) 
(\lambda (_: T).(\lambda (z: T).(eq T (lift h (s k d) t1) (lift h (s k d) 
z)))) t0 t1 (refl_equal T (THead k t0 t1)) (refl_equal T (lift h d t0)) 
(refl_equal T (lift h (s k d) t1))) u H6))) t H8))) k0 H7))))) H4)) 
H3))))))))))) x)))).
(* COMMENTS
Initial nodes: 2083
END *)

theorem lift_gen_bind:
 \forall (b: B).(\forall (u: T).(\forall (t: T).(\forall (x: T).(\forall (h: 
nat).(\forall (d: nat).((eq T (THead (Bind b) u t) (lift h d x)) \to (ex3_2 T 
T (\lambda (y: T).(\lambda (z: T).(eq T x (THead (Bind b) y z)))) (\lambda 
(y: T).(\lambda (_: T).(eq T u (lift h d y)))) (\lambda (_: T).(\lambda (z: 
T).(eq T t (lift h (S d) z)))))))))))
\def
 \lambda (b: B).(\lambda (u: T).(\lambda (t: T).(\lambda (x: T).(\lambda (h: 
nat).(\lambda (d: nat).(\lambda (H: (eq T (THead (Bind b) u t) (lift h d 
x))).(let H_x \def (lift_gen_head (Bind b) u t x h d H) in (let H0 \def H_x 
in (ex3_2_ind T T (\lambda (y: T).(\lambda (z: T).(eq T x (THead (Bind b) y 
z)))) (\lambda (y: T).(\lambda (_: T).(eq T u (lift h d y)))) (\lambda (_: 
T).(\lambda (z: T).(eq T t (lift h (S d) z)))) (ex3_2 T T (\lambda (y: 
T).(\lambda (z: T).(eq T x (THead (Bind b) y z)))) (\lambda (y: T).(\lambda 
(_: T).(eq T u (lift h d y)))) (\lambda (_: T).(\lambda (z: T).(eq T t (lift 
h (S d) z))))) (\lambda (x0: T).(\lambda (x1: T).(\lambda (H1: (eq T x (THead 
(Bind b) x0 x1))).(\lambda (H2: (eq T u (lift h d x0))).(\lambda (H3: (eq T t 
(lift h (S d) x1))).(eq_ind_r T (THead (Bind b) x0 x1) (\lambda (t0: 
T).(ex3_2 T T (\lambda (y: T).(\lambda (z: T).(eq T t0 (THead (Bind b) y 
z)))) (\lambda (y: T).(\lambda (_: T).(eq T u (lift h d y)))) (\lambda (_: 
T).(\lambda (z: T).(eq T t (lift h (S d) z)))))) (eq_ind_r T (lift h (S d) 
x1) (\lambda (t0: T).(ex3_2 T T (\lambda (y: T).(\lambda (z: T).(eq T (THead 
(Bind b) x0 x1) (THead (Bind b) y z)))) (\lambda (y: T).(\lambda (_: T).(eq T 
u (lift h d y)))) (\lambda (_: T).(\lambda (z: T).(eq T t0 (lift h (S d) 
z)))))) (eq_ind_r T (lift h d x0) (\lambda (t0: T).(ex3_2 T T (\lambda (y: 
T).(\lambda (z: T).(eq T (THead (Bind b) x0 x1) (THead (Bind b) y z)))) 
(\lambda (y: T).(\lambda (_: T).(eq T t0 (lift h d y)))) (\lambda (_: 
T).(\lambda (z: T).(eq T (lift h (S d) x1) (lift h (S d) z)))))) (ex3_2_intro 
T T (\lambda (y: T).(\lambda (z: T).(eq T (THead (Bind b) x0 x1) (THead (Bind 
b) y z)))) (\lambda (y: T).(\lambda (_: T).(eq T (lift h d x0) (lift h d 
y)))) (\lambda (_: T).(\lambda (z: T).(eq T (lift h (S d) x1) (lift h (S d) 
z)))) x0 x1 (refl_equal T (THead (Bind b) x0 x1)) (refl_equal T (lift h d 
x0)) (refl_equal T (lift h (S d) x1))) u H2) t H3) x H1)))))) H0))))))))).
(* COMMENTS
Initial nodes: 637
END *)

theorem lift_gen_flat:
 \forall (f: F).(\forall (u: T).(\forall (t: T).(\forall (x: T).(\forall (h: 
nat).(\forall (d: nat).((eq T (THead (Flat f) u t) (lift h d x)) \to (ex3_2 T 
T (\lambda (y: T).(\lambda (z: T).(eq T x (THead (Flat f) y z)))) (\lambda 
(y: T).(\lambda (_: T).(eq T u (lift h d y)))) (\lambda (_: T).(\lambda (z: 
T).(eq T t (lift h d z)))))))))))
\def
 \lambda (f: F).(\lambda (u: T).(\lambda (t: T).(\lambda (x: T).(\lambda (h: 
nat).(\lambda (d: nat).(\lambda (H: (eq T (THead (Flat f) u t) (lift h d 
x))).(let H_x \def (lift_gen_head (Flat f) u t x h d H) in (let H0 \def H_x 
in (ex3_2_ind T T (\lambda (y: T).(\lambda (z: T).(eq T x (THead (Flat f) y 
z)))) (\lambda (y: T).(\lambda (_: T).(eq T u (lift h d y)))) (\lambda (_: 
T).(\lambda (z: T).(eq T t (lift h d z)))) (ex3_2 T T (\lambda (y: 
T).(\lambda (z: T).(eq T x (THead (Flat f) y z)))) (\lambda (y: T).(\lambda 
(_: T).(eq T u (lift h d y)))) (\lambda (_: T).(\lambda (z: T).(eq T t (lift 
h d z))))) (\lambda (x0: T).(\lambda (x1: T).(\lambda (H1: (eq T x (THead 
(Flat f) x0 x1))).(\lambda (H2: (eq T u (lift h d x0))).(\lambda (H3: (eq T t 
(lift h d x1))).(eq_ind_r T (THead (Flat f) x0 x1) (\lambda (t0: T).(ex3_2 T 
T (\lambda (y: T).(\lambda (z: T).(eq T t0 (THead (Flat f) y z)))) (\lambda 
(y: T).(\lambda (_: T).(eq T u (lift h d y)))) (\lambda (_: T).(\lambda (z: 
T).(eq T t (lift h d z)))))) (eq_ind_r T (lift h d x1) (\lambda (t0: 
T).(ex3_2 T T (\lambda (y: T).(\lambda (z: T).(eq T (THead (Flat f) x0 x1) 
(THead (Flat f) y z)))) (\lambda (y: T).(\lambda (_: T).(eq T u (lift h d 
y)))) (\lambda (_: T).(\lambda (z: T).(eq T t0 (lift h d z)))))) (eq_ind_r T 
(lift h d x0) (\lambda (t0: T).(ex3_2 T T (\lambda (y: T).(\lambda (z: T).(eq 
T (THead (Flat f) x0 x1) (THead (Flat f) y z)))) (\lambda (y: T).(\lambda (_: 
T).(eq T t0 (lift h d y)))) (\lambda (_: T).(\lambda (z: T).(eq T (lift h d 
x1) (lift h d z)))))) (ex3_2_intro T T (\lambda (y: T).(\lambda (z: T).(eq T 
(THead (Flat f) x0 x1) (THead (Flat f) y z)))) (\lambda (y: T).(\lambda (_: 
T).(eq T (lift h d x0) (lift h d y)))) (\lambda (_: T).(\lambda (z: T).(eq T 
(lift h d x1) (lift h d z)))) x0 x1 (refl_equal T (THead (Flat f) x0 x1)) 
(refl_equal T (lift h d x0)) (refl_equal T (lift h d x1))) u H2) t H3) x 
H1)))))) H0))))))))).
(* COMMENTS
Initial nodes: 615
END *)

