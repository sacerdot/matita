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

include "basic_1/lift/props.ma".

lemma lift_gen_sort:
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
H1 \def (eq_ind T (TSort n) (\lambda (ee: T).(match ee with [(TSort _) 
\Rightarrow True | (TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow 
False])) I (lift h d (TLRef n0)) H) in (False_ind (lt n0 d) H1)))) in (let H2 
\def (eq_ind T (TSort n) (\lambda (ee: T).(match ee with [(TSort _) 
\Rightarrow True | (TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow 
False])) I (TLRef n0) H1) in (False_ind (eq T (TLRef n0) (TSort n)) H2)))) 
(\lambda (_: (le d n0)).(let H1 \def (eq_ind T (lift h d (TLRef n0)) (\lambda 
(t0: T).(eq T (TSort n) t0)) H (TLRef (plus n0 h)) (lift_lref_ge n0 h d (let 
H1 \def (eq_ind T (TSort n) (\lambda (ee: T).(match ee with [(TSort _) 
\Rightarrow True | (TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow 
False])) I (lift h d (TLRef n0)) H) in (False_ind (le d n0) H1)))) in (let H2 
\def (eq_ind T (TSort n) (\lambda (ee: T).(match ee with [(TSort _) 
\Rightarrow True | (TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow 
False])) I (TLRef (plus n0 h)) H1) in (False_ind (eq T (TLRef n0) (TSort n)) 
H2))))))) (\lambda (k: K).(\lambda (t0: T).(\lambda (_: (((eq T (TSort n) 
(lift h d t0)) \to (eq T t0 (TSort n))))).(\lambda (t1: T).(\lambda (_: (((eq 
T (TSort n) (lift h d t1)) \to (eq T t1 (TSort n))))).(\lambda (H1: (eq T 
(TSort n) (lift h d (THead k t0 t1)))).(let H2 \def (eq_ind T (lift h d 
(THead k t0 t1)) (\lambda (t2: T).(eq T (TSort n) t2)) H1 (THead k (lift h d 
t0) (lift h (s k d) t1)) (lift_head k t0 t1 h d)) in (let H3 \def (eq_ind T 
(TSort n) (\lambda (ee: T).(match ee with [(TSort _) \Rightarrow True | 
(TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow False])) I (THead k 
(lift h d t0) (lift h (s k d) t1)) H2) in (False_ind (eq T (THead k t0 t1) 
(TSort n)) H3))))))))) t)))).

lemma lift_gen_lref:
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
T).(match ee with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow True | 
(THead _ _ _) \Rightarrow False])) I (TSort n) H0) in (False_ind (or (land 
(lt i d) (eq T (TSort n) (TLRef i))) (land (le (plus d h) i) (eq T (TSort n) 
(TLRef (minus i h))))) H1)))))))) (\lambda (n: nat).(\lambda (d: 
nat).(\lambda (h: nat).(\lambda (i: nat).(\lambda (H: (eq T (TLRef i) (lift h 
d (TLRef n)))).(lt_le_e n d (or (land (lt i d) (eq T (TLRef n) (TLRef i))) 
(land (le (plus d h) i) (eq T (TLRef n) (TLRef (minus i h))))) (\lambda (H0: 
(lt n d)).(let H1 \def (eq_ind T (lift h d (TLRef n)) (\lambda (t0: T).(eq T 
(TLRef i) t0)) H (TLRef n) (lift_lref_lt n h d H0)) in (let H2 \def (f_equal 
T nat (\lambda (e: T).(match e with [(TSort _) \Rightarrow i | (TLRef n0) 
\Rightarrow n0 | (THead _ _ _) \Rightarrow i])) (TLRef i) (TLRef n) H1) in 
(eq_ind_r nat n (\lambda (n0: nat).(or (land (lt n0 d) (eq T (TLRef n) (TLRef 
n0))) (land (le (plus d h) n0) (eq T (TLRef n) (TLRef (minus n0 h)))))) 
(or_introl (land (lt n d) (eq T (TLRef n) (TLRef n))) (land (le (plus d h) n) 
(eq T (TLRef n) (TLRef (minus n h)))) (conj (lt n d) (eq T (TLRef n) (TLRef 
n)) H0 (refl_equal T (TLRef n)))) i H2)))) (\lambda (H0: (le d n)).(let H1 
\def (eq_ind T (lift h d (TLRef n)) (\lambda (t0: T).(eq T (TLRef i) t0)) H 
(TLRef (plus n h)) (lift_lref_ge n h d H0)) in (let H2 \def (f_equal T nat 
(\lambda (e: T).(match e with [(TSort _) \Rightarrow i | (TLRef n0) 
\Rightarrow n0 | (THead _ _ _) \Rightarrow i])) (TLRef i) (TLRef (plus n h)) 
H1) in (eq_ind_r nat (plus n h) (\lambda (n0: nat).(or (land (lt n0 d) (eq T 
(TLRef n) (TLRef n0))) (land (le (plus d h) n0) (eq T (TLRef n) (TLRef (minus 
n0 h)))))) (eq_ind_r nat n (\lambda (n0: nat).(or (land (lt (plus n h) d) (eq 
T (TLRef n) (TLRef (plus n h)))) (land (le (plus d h) (plus n h)) (eq T 
(TLRef n) (TLRef n0))))) (or_intror (land (lt (plus n h) d) (eq T (TLRef n) 
(TLRef (plus n h)))) (land (le (plus d h) (plus n h)) (eq T (TLRef n) (TLRef 
n))) (conj (le (plus d h) (plus n h)) (eq T (TLRef n) (TLRef n)) 
(le_plus_plus d n h h H0 (le_n h)) (refl_equal T (TLRef n)))) (minus (plus n 
h) h) (minus_plus_r n h)) i H2)))))))))) (\lambda (k: K).(\lambda (t0: 
T).(\lambda (_: ((\forall (d: nat).(\forall (h: nat).(\forall (i: nat).((eq T 
(TLRef i) (lift h d t0)) \to (or (land (lt i d) (eq T t0 (TLRef i))) (land 
(le (plus d h) i) (eq T t0 (TLRef (minus i h))))))))))).(\lambda (t1: 
T).(\lambda (_: ((\forall (d: nat).(\forall (h: nat).(\forall (i: nat).((eq T 
(TLRef i) (lift h d t1)) \to (or (land (lt i d) (eq T t1 (TLRef i))) (land 
(le (plus d h) i) (eq T t1 (TLRef (minus i h))))))))))).(\lambda (d: 
nat).(\lambda (h: nat).(\lambda (i: nat).(\lambda (H1: (eq T (TLRef i) (lift 
h d (THead k t0 t1)))).(let H2 \def (eq_ind T (lift h d (THead k t0 t1)) 
(\lambda (t2: T).(eq T (TLRef i) t2)) H1 (THead k (lift h d t0) (lift h (s k 
d) t1)) (lift_head k t0 t1 h d)) in (let H3 \def (eq_ind T (TLRef i) (\lambda 
(ee: T).(match ee with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow 
True | (THead _ _ _) \Rightarrow False])) I (THead k (lift h d t0) (lift h (s 
k d) t1)) H2) in (False_ind (or (land (lt i d) (eq T (THead k t0 t1) (TLRef 
i))) (land (le (plus d h) i) (eq T (THead k t0 t1) (TLRef (minus i h))))) 
H3)))))))))))) t).

lemma lift_gen_lref_lt:
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

lemma lift_gen_lref_false:
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

lemma lift_gen_lref_ge:
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

lemma lift_gen_head:
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
\def (eq_ind T (THead k u t) (\lambda (ee: T).(match ee with [(TSort _) 
\Rightarrow False | (TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow 
True])) I (TSort n) H0) in (False_ind (ex3_2 T T (\lambda (y: T).(\lambda (z: 
T).(eq T (TSort n) (THead k y z)))) (\lambda (y: T).(\lambda (_: T).(eq T u 
(lift h d y)))) (\lambda (_: T).(\lambda (z: T).(eq T t (lift h (s k d) 
z))))) H1))))))) (\lambda (n: nat).(\lambda (h: nat).(\lambda (d: 
nat).(\lambda (H: (eq T (THead k u t) (lift h d (TLRef n)))).(lt_le_e n d 
(ex3_2 T T (\lambda (y: T).(\lambda (z: T).(eq T (TLRef n) (THead k y z)))) 
(\lambda (y: T).(\lambda (_: T).(eq T u (lift h d y)))) (\lambda (_: 
T).(\lambda (z: T).(eq T t (lift h (s k d) z))))) (\lambda (H0: (lt n 
d)).(let H1 \def (eq_ind T (lift h d (TLRef n)) (\lambda (t0: T).(eq T (THead 
k u t) t0)) H (TLRef n) (lift_lref_lt n h d H0)) in (let H2 \def (eq_ind T 
(THead k u t) (\lambda (ee: T).(match ee with [(TSort _) \Rightarrow False | 
(TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow True])) I (TLRef n) 
H1) in (False_ind (ex3_2 T T (\lambda (y: T).(\lambda (z: T).(eq T (TLRef n) 
(THead k y z)))) (\lambda (y: T).(\lambda (_: T).(eq T u (lift h d y)))) 
(\lambda (_: T).(\lambda (z: T).(eq T t (lift h (s k d) z))))) H2)))) 
(\lambda (H0: (le d n)).(let H1 \def (eq_ind T (lift h d (TLRef n)) (\lambda 
(t0: T).(eq T (THead k u t) t0)) H (TLRef (plus n h)) (lift_lref_ge n h d 
H0)) in (let H2 \def (eq_ind T (THead k u t) (\lambda (ee: T).(match ee with 
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
e with [(TSort _) \Rightarrow k | (TLRef _) \Rightarrow k | (THead k1 _ _) 
\Rightarrow k1])) (THead k u t) (THead k0 (lift h d t0) (lift h (s k0 d) t1)) 
H2) in ((let H4 \def (f_equal T T (\lambda (e: T).(match e with [(TSort _) 
\Rightarrow u | (TLRef _) \Rightarrow u | (THead _ t2 _) \Rightarrow t2])) 
(THead k u t) (THead k0 (lift h d t0) (lift h (s k0 d) t1)) H2) in ((let H5 
\def (f_equal T T (\lambda (e: T).(match e with [(TSort _) \Rightarrow t | 
(TLRef _) \Rightarrow t | (THead _ _ t2) \Rightarrow t2])) (THead k u t) 
(THead k0 (lift h d t0) (lift h (s k0 d) t1)) H2) in (\lambda (H6: (eq T u 
(lift h d t0))).(\lambda (H7: (eq K k k0)).(let H8 \def (eq_ind_r K k0 
(\lambda (k1: K).(eq T t (lift h (s k1 d) t1))) H5 k H7) in (eq_ind K k 
(\lambda (k1: K).(ex3_2 T T (\lambda (y: T).(\lambda (z: T).(eq T (THead k1 
t0 t1) (THead k y z)))) (\lambda (y: T).(\lambda (_: T).(eq T u (lift h d 
y)))) (\lambda (_: T).(\lambda (z: T).(eq T t (lift h (s k d) z)))))) (let H9 
\def (eq_ind T t (\lambda (t2: T).(\forall (h0: nat).(\forall (d0: nat).((eq 
T (THead k u t2) (lift h0 d0 t1)) \to (ex3_2 T T (\lambda (y: T).(\lambda (z: 
T).(eq T t1 (THead k y z)))) (\lambda (y: T).(\lambda (_: T).(eq T u (lift h0 
d0 y)))) (\lambda (_: T).(\lambda (z: T).(eq T t2 (lift h0 (s k d0) 
z))))))))) H0 (lift h (s k d) t1) H8) in (let H10 \def (eq_ind T t (\lambda 
(t2: T).(\forall (h0: nat).(\forall (d0: nat).((eq T (THead k u t2) (lift h0 
d0 t0)) \to (ex3_2 T T (\lambda (y: T).(\lambda (z: T).(eq T t0 (THead k y 
z)))) (\lambda (y: T).(\lambda (_: T).(eq T u (lift h0 d0 y)))) (\lambda (_: 
T).(\lambda (z: T).(eq T t2 (lift h0 (s k d0) z))))))))) H (lift h (s k d) 
t1) H8) in (eq_ind_r T (lift h (s k d) t1) (\lambda (t2: T).(ex3_2 T T 
(\lambda (y: T).(\lambda (z: T).(eq T (THead k t0 t1) (THead k y z)))) 
(\lambda (y: T).(\lambda (_: T).(eq T u (lift h d y)))) (\lambda (_: 
T).(\lambda (z: T).(eq T t2 (lift h (s k d) z)))))) (let H11 \def (eq_ind T u 
(\lambda (t2: T).(\forall (h0: nat).(\forall (d0: nat).((eq T (THead k t2 
(lift h (s k d) t1)) (lift h0 d0 t0)) \to (ex3_2 T T (\lambda (y: T).(\lambda 
(z: T).(eq T t0 (THead k y z)))) (\lambda (y: T).(\lambda (_: T).(eq T t2 
(lift h0 d0 y)))) (\lambda (_: T).(\lambda (z: T).(eq T (lift h (s k d) t1) 
(lift h0 (s k d0) z))))))))) H10 (lift h d t0) H6) in (let H12 \def (eq_ind T 
u (\lambda (t2: T).(\forall (h0: nat).(\forall (d0: nat).((eq T (THead k t2 
(lift h (s k d) t1)) (lift h0 d0 t1)) \to (ex3_2 T T (\lambda (y: T).(\lambda 
(z: T).(eq T t1 (THead k y z)))) (\lambda (y: T).(\lambda (_: T).(eq T t2 
(lift h0 d0 y)))) (\lambda (_: T).(\lambda (z: T).(eq T (lift h (s k d) t1) 
(lift h0 (s k d0) z))))))))) H9 (lift h d t0) H6) in (eq_ind_r T (lift h d 
t0) (\lambda (t2: T).(ex3_2 T T (\lambda (y: T).(\lambda (z: T).(eq T (THead 
k t0 t1) (THead k y z)))) (\lambda (y: T).(\lambda (_: T).(eq T t2 (lift h d 
y)))) (\lambda (_: T).(\lambda (z: T).(eq T (lift h (s k d) t1) (lift h (s k 
d) z)))))) (ex3_2_intro T T (\lambda (y: T).(\lambda (z: T).(eq T (THead k t0 
t1) (THead k y z)))) (\lambda (y: T).(\lambda (_: T).(eq T (lift h d t0) 
(lift h d y)))) (\lambda (_: T).(\lambda (z: T).(eq T (lift h (s k d) t1) 
(lift h (s k d) z)))) t0 t1 (refl_equal T (THead k t0 t1)) (refl_equal T 
(lift h d t0)) (refl_equal T (lift h (s k d) t1))) u H6))) t H8))) k0 H7))))) 
H4)) H3))))))))))) x)))).

lemma lift_gen_bind:
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

lemma lift_gen_flat:
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

lemma lift_inj:
 \forall (x: T).(\forall (t: T).(\forall (h: nat).(\forall (d: nat).((eq T 
(lift h d x) (lift h d t)) \to (eq T x t)))))
\def
 \lambda (x: T).(T_ind (\lambda (t: T).(\forall (t0: T).(\forall (h: 
nat).(\forall (d: nat).((eq T (lift h d t) (lift h d t0)) \to (eq T t 
t0)))))) (\lambda (n: nat).(\lambda (t: T).(\lambda (h: nat).(\lambda (d: 
nat).(\lambda (H: (eq T (lift h d (TSort n)) (lift h d t))).(let H0 \def 
(eq_ind T (lift h d (TSort n)) (\lambda (t0: T).(eq T t0 (lift h d t))) H 
(TSort n) (lift_sort n h d)) in (sym_eq T t (TSort n) (lift_gen_sort h d n t 
H0)))))))) (\lambda (n: nat).(\lambda (t: T).(\lambda (h: nat).(\lambda (d: 
nat).(\lambda (H: (eq T (lift h d (TLRef n)) (lift h d t))).(lt_le_e n d (eq 
T (TLRef n) t) (\lambda (H0: (lt n d)).(let H1 \def (eq_ind T (lift h d 
(TLRef n)) (\lambda (t0: T).(eq T t0 (lift h d t))) H (TLRef n) (lift_lref_lt 
n h d H0)) in (sym_eq T t (TLRef n) (lift_gen_lref_lt h d n (lt_le_trans n d 
d H0 (le_n d)) t H1)))) (\lambda (H0: (le d n)).(let H1 \def (eq_ind T (lift 
h d (TLRef n)) (\lambda (t0: T).(eq T t0 (lift h d t))) H (TLRef (plus n h)) 
(lift_lref_ge n h d H0)) in (sym_eq T t (TLRef n) (lift_gen_lref_ge h d n H0 
t H1)))))))))) (\lambda (k: K).(K_ind (\lambda (k0: K).(\forall (t: 
T).(((\forall (t0: T).(\forall (h: nat).(\forall (d: nat).((eq T (lift h d t) 
(lift h d t0)) \to (eq T t t0)))))) \to (\forall (t0: T).(((\forall (t1: 
T).(\forall (h: nat).(\forall (d: nat).((eq T (lift h d t0) (lift h d t1)) 
\to (eq T t0 t1)))))) \to (\forall (t1: T).(\forall (h: nat).(\forall (d: 
nat).((eq T (lift h d (THead k0 t t0)) (lift h d t1)) \to (eq T (THead k0 t 
t0) t1)))))))))) (\lambda (b: B).(\lambda (t: T).(\lambda (H: ((\forall (t0: 
T).(\forall (h: nat).(\forall (d: nat).((eq T (lift h d t) (lift h d t0)) \to 
(eq T t t0))))))).(\lambda (t0: T).(\lambda (H0: ((\forall (t1: T).(\forall 
(h: nat).(\forall (d: nat).((eq T (lift h d t0) (lift h d t1)) \to (eq T t0 
t1))))))).(\lambda (t1: T).(\lambda (h: nat).(\lambda (d: nat).(\lambda (H1: 
(eq T (lift h d (THead (Bind b) t t0)) (lift h d t1))).(let H2 \def (eq_ind T 
(lift h d (THead (Bind b) t t0)) (\lambda (t2: T).(eq T t2 (lift h d t1))) H1 
(THead (Bind b) (lift h d t) (lift h (S d) t0)) (lift_bind b t t0 h d)) in 
(ex3_2_ind T T (\lambda (y: T).(\lambda (z: T).(eq T t1 (THead (Bind b) y 
z)))) (\lambda (y: T).(\lambda (_: T).(eq T (lift h d t) (lift h d y)))) 
(\lambda (_: T).(\lambda (z: T).(eq T (lift h (S d) t0) (lift h (S d) z)))) 
(eq T (THead (Bind b) t t0) t1) (\lambda (x0: T).(\lambda (x1: T).(\lambda 
(H3: (eq T t1 (THead (Bind b) x0 x1))).(\lambda (H4: (eq T (lift h d t) (lift 
h d x0))).(\lambda (H5: (eq T (lift h (S d) t0) (lift h (S d) x1))).(eq_ind_r 
T (THead (Bind b) x0 x1) (\lambda (t2: T).(eq T (THead (Bind b) t t0) t2)) 
(sym_eq T (THead (Bind b) x0 x1) (THead (Bind b) t t0) (sym_eq T (THead (Bind 
b) t t0) (THead (Bind b) x0 x1) (f_equal3 K T T T THead (Bind b) (Bind b) t 
x0 t0 x1 (refl_equal K (Bind b)) (H x0 h d H4) (H0 x1 h (S d) H5)))) t1 
H3)))))) (lift_gen_bind b (lift h d t) (lift h (S d) t0) t1 h d 
H2)))))))))))) (\lambda (f: F).(\lambda (t: T).(\lambda (H: ((\forall (t0: 
T).(\forall (h: nat).(\forall (d: nat).((eq T (lift h d t) (lift h d t0)) \to 
(eq T t t0))))))).(\lambda (t0: T).(\lambda (H0: ((\forall (t1: T).(\forall 
(h: nat).(\forall (d: nat).((eq T (lift h d t0) (lift h d t1)) \to (eq T t0 
t1))))))).(\lambda (t1: T).(\lambda (h: nat).(\lambda (d: nat).(\lambda (H1: 
(eq T (lift h d (THead (Flat f) t t0)) (lift h d t1))).(let H2 \def (eq_ind T 
(lift h d (THead (Flat f) t t0)) (\lambda (t2: T).(eq T t2 (lift h d t1))) H1 
(THead (Flat f) (lift h d t) (lift h d t0)) (lift_flat f t t0 h d)) in 
(ex3_2_ind T T (\lambda (y: T).(\lambda (z: T).(eq T t1 (THead (Flat f) y 
z)))) (\lambda (y: T).(\lambda (_: T).(eq T (lift h d t) (lift h d y)))) 
(\lambda (_: T).(\lambda (z: T).(eq T (lift h d t0) (lift h d z)))) (eq T 
(THead (Flat f) t t0) t1) (\lambda (x0: T).(\lambda (x1: T).(\lambda (H3: (eq 
T t1 (THead (Flat f) x0 x1))).(\lambda (H4: (eq T (lift h d t) (lift h d 
x0))).(\lambda (H5: (eq T (lift h d t0) (lift h d x1))).(eq_ind_r T (THead 
(Flat f) x0 x1) (\lambda (t2: T).(eq T (THead (Flat f) t t0) t2)) (sym_eq T 
(THead (Flat f) x0 x1) (THead (Flat f) t t0) (sym_eq T (THead (Flat f) t t0) 
(THead (Flat f) x0 x1) (f_equal3 K T T T THead (Flat f) (Flat f) t x0 t0 x1 
(refl_equal K (Flat f)) (H x0 h d H4) (H0 x1 h d H5)))) t1 H3)))))) 
(lift_gen_flat f (lift h d t) (lift h d t0) t1 h d H2)))))))))))) k)) x).

lemma lift_gen_lift:
 \forall (t1: T).(\forall (x: T).(\forall (h1: nat).(\forall (h2: 
nat).(\forall (d1: nat).(\forall (d2: nat).((le d1 d2) \to ((eq T (lift h1 d1 
t1) (lift h2 (plus d2 h1) x)) \to (ex2 T (\lambda (t2: T).(eq T x (lift h1 d1 
t2))) (\lambda (t2: T).(eq T t1 (lift h2 d2 t2)))))))))))
\def
 \lambda (t1: T).(T_ind (\lambda (t: T).(\forall (x: T).(\forall (h1: 
nat).(\forall (h2: nat).(\forall (d1: nat).(\forall (d2: nat).((le d1 d2) \to 
((eq T (lift h1 d1 t) (lift h2 (plus d2 h1) x)) \to (ex2 T (\lambda (t2: 
T).(eq T x (lift h1 d1 t2))) (\lambda (t2: T).(eq T t (lift h2 d2 
t2)))))))))))) (\lambda (n: nat).(\lambda (x: T).(\lambda (h1: nat).(\lambda 
(h2: nat).(\lambda (d1: nat).(\lambda (d2: nat).(\lambda (_: (le d1 
d2)).(\lambda (H0: (eq T (lift h1 d1 (TSort n)) (lift h2 (plus d2 h1) 
x))).(let H1 \def (eq_ind T (lift h1 d1 (TSort n)) (\lambda (t: T).(eq T t 
(lift h2 (plus d2 h1) x))) H0 (TSort n) (lift_sort n h1 d1)) in (eq_ind_r T 
(TSort n) (\lambda (t: T).(ex2 T (\lambda (t2: T).(eq T t (lift h1 d1 t2))) 
(\lambda (t2: T).(eq T (TSort n) (lift h2 d2 t2))))) (ex_intro2 T (\lambda 
(t2: T).(eq T (TSort n) (lift h1 d1 t2))) (\lambda (t2: T).(eq T (TSort n) 
(lift h2 d2 t2))) (TSort n) (eq_ind_r T (TSort n) (\lambda (t: T).(eq T 
(TSort n) t)) (refl_equal T (TSort n)) (lift h1 d1 (TSort n)) (lift_sort n h1 
d1)) (eq_ind_r T (TSort n) (\lambda (t: T).(eq T (TSort n) t)) (refl_equal T 
(TSort n)) (lift h2 d2 (TSort n)) (lift_sort n h2 d2))) x (lift_gen_sort h2 
(plus d2 h1) n x H1))))))))))) (\lambda (n: nat).(\lambda (x: T).(\lambda 
(h1: nat).(\lambda (h2: nat).(\lambda (d1: nat).(\lambda (d2: nat).(\lambda 
(H: (le d1 d2)).(\lambda (H0: (eq T (lift h1 d1 (TLRef n)) (lift h2 (plus d2 
h1) x))).(lt_le_e n d1 (ex2 T (\lambda (t2: T).(eq T x (lift h1 d1 t2))) 
(\lambda (t2: T).(eq T (TLRef n) (lift h2 d2 t2)))) (\lambda (H1: (lt n 
d1)).(let H2 \def (eq_ind T (lift h1 d1 (TLRef n)) (\lambda (t: T).(eq T t 
(lift h2 (plus d2 h1) x))) H0 (TLRef n) (lift_lref_lt n h1 d1 H1)) in 
(eq_ind_r T (TLRef n) (\lambda (t: T).(ex2 T (\lambda (t2: T).(eq T t (lift 
h1 d1 t2))) (\lambda (t2: T).(eq T (TLRef n) (lift h2 d2 t2))))) (ex_intro2 T 
(\lambda (t2: T).(eq T (TLRef n) (lift h1 d1 t2))) (\lambda (t2: T).(eq T 
(TLRef n) (lift h2 d2 t2))) (TLRef n) (eq_ind_r T (TLRef n) (\lambda (t: 
T).(eq T (TLRef n) t)) (refl_equal T (TLRef n)) (lift h1 d1 (TLRef n)) 
(lift_lref_lt n h1 d1 H1)) (eq_ind_r T (TLRef n) (\lambda (t: T).(eq T (TLRef 
n) t)) (refl_equal T (TLRef n)) (lift h2 d2 (TLRef n)) (lift_lref_lt n h2 d2 
(lt_le_trans n d1 d2 H1 H)))) x (lift_gen_lref_lt h2 (plus d2 h1) n 
(lt_le_trans n d1 (plus d2 h1) H1 (le_plus_trans d1 d2 h1 H)) x H2)))) 
(\lambda (H1: (le d1 n)).(let H2 \def (eq_ind T (lift h1 d1 (TLRef n)) 
(\lambda (t: T).(eq T t (lift h2 (plus d2 h1) x))) H0 (TLRef (plus n h1)) 
(lift_lref_ge n h1 d1 H1)) in (lt_le_e n d2 (ex2 T (\lambda (t2: T).(eq T x 
(lift h1 d1 t2))) (\lambda (t2: T).(eq T (TLRef n) (lift h2 d2 t2)))) 
(\lambda (H3: (lt n d2)).(eq_ind_r T (TLRef (plus n h1)) (\lambda (t: T).(ex2 
T (\lambda (t2: T).(eq T t (lift h1 d1 t2))) (\lambda (t2: T).(eq T (TLRef n) 
(lift h2 d2 t2))))) (ex_intro2 T (\lambda (t2: T).(eq T (TLRef (plus n h1)) 
(lift h1 d1 t2))) (\lambda (t2: T).(eq T (TLRef n) (lift h2 d2 t2))) (TLRef 
n) (eq_ind_r T (TLRef (plus n h1)) (\lambda (t: T).(eq T (TLRef (plus n h1)) 
t)) (refl_equal T (TLRef (plus n h1))) (lift h1 d1 (TLRef n)) (lift_lref_ge n 
h1 d1 H1)) (eq_ind_r T (TLRef n) (\lambda (t: T).(eq T (TLRef n) t)) 
(refl_equal T (TLRef n)) (lift h2 d2 (TLRef n)) (lift_lref_lt n h2 d2 H3))) x 
(lift_gen_lref_lt h2 (plus d2 h1) (plus n h1) (lt_reg_r n d2 h1 H3) x H2))) 
(\lambda (H3: (le d2 n)).(lt_le_e n (plus d2 h2) (ex2 T (\lambda (t2: T).(eq 
T x (lift h1 d1 t2))) (\lambda (t2: T).(eq T (TLRef n) (lift h2 d2 t2)))) 
(\lambda (H4: (lt n (plus d2 h2))).(lift_gen_lref_false h2 (plus d2 h1) (plus 
n h1) (le_plus_plus d2 n h1 h1 H3 (le_n h1)) (eq_ind_r nat (plus (plus d2 h2) 
h1) (\lambda (n0: nat).(lt (plus n h1) n0)) (lt_reg_r n (plus d2 h2) h1 H4) 
(plus (plus d2 h1) h2) (plus_permute_2_in_3 d2 h1 h2)) x H2 (ex2 T (\lambda 
(t2: T).(eq T x (lift h1 d1 t2))) (\lambda (t2: T).(eq T (TLRef n) (lift h2 
d2 t2)))))) (\lambda (H4: (le (plus d2 h2) n)).(let H5 \def (eq_ind nat (plus 
n h1) (\lambda (n0: nat).(eq T (TLRef n0) (lift h2 (plus d2 h1) x))) H2 (plus 
(minus (plus n h1) h2) h2) (le_plus_minus_sym h2 (plus n h1) (le_plus_trans 
h2 n h1 (le_trans h2 (plus d2 h2) n (le_plus_r d2 h2) H4)))) in (eq_ind_r T 
(TLRef (minus (plus n h1) h2)) (\lambda (t: T).(ex2 T (\lambda (t2: T).(eq T 
t (lift h1 d1 t2))) (\lambda (t2: T).(eq T (TLRef n) (lift h2 d2 t2))))) 
(ex_intro2 T (\lambda (t2: T).(eq T (TLRef (minus (plus n h1) h2)) (lift h1 
d1 t2))) (\lambda (t2: T).(eq T (TLRef n) (lift h2 d2 t2))) (TLRef (minus n 
h2)) (eq_ind_r nat (plus (minus n h2) h1) (\lambda (n0: nat).(eq T (TLRef n0) 
(lift h1 d1 (TLRef (minus n h2))))) (eq_ind_r T (TLRef (plus (minus n h2) 
h1)) (\lambda (t: T).(eq T (TLRef (plus (minus n h2) h1)) t)) (refl_equal T 
(TLRef (plus (minus n h2) h1))) (lift h1 d1 (TLRef (minus n h2))) 
(lift_lref_ge (minus n h2) h1 d1 (le_trans d1 d2 (minus n h2) H (le_minus d2 
n h2 H4)))) (minus (plus n h1) h2) (le_minus_plus h2 n (le_trans h2 (plus d2 
h2) n (le_plus_r d2 h2) H4) h1)) (eq_ind_r nat (plus (minus n h2) h2) 
(\lambda (n0: nat).(eq T (TLRef n0) (lift h2 d2 (TLRef (minus n0 h2))))) 
(eq_ind_r T (TLRef (plus (minus (plus (minus n h2) h2) h2) h2)) (\lambda (t: 
T).(eq T (TLRef (plus (minus n h2) h2)) t)) (sym_eq T (TLRef (plus (minus 
(plus (minus n h2) h2) h2) h2)) (TLRef (plus (minus n h2) h2)) (f_equal nat T 
TLRef (plus (minus (plus (minus n h2) h2) h2) h2) (plus (minus n h2) h2) 
(f_equal2 nat nat nat plus (minus (plus (minus n h2) h2) h2) (minus n h2) h2 
h2 (minus_plus_r (minus n h2) h2) (refl_equal nat h2)))) (lift h2 d2 (TLRef 
(minus (plus (minus n h2) h2) h2))) (lift_lref_ge (minus (plus (minus n h2) 
h2) h2) h2 d2 (le_minus d2 (plus (minus n h2) h2) h2 (le_plus_plus d2 (minus 
n h2) h2 h2 (le_minus d2 n h2 H4) (le_n h2))))) n (le_plus_minus_sym h2 n 
(le_trans h2 (plus d2 h2) n (le_plus_r d2 h2) H4)))) x (lift_gen_lref_ge h2 
(plus d2 h1) (minus (plus n h1) h2) (arith0 h2 d2 n H4 h1) x 
H5)))))))))))))))))) (\lambda (k: K).(\lambda (t: T).(\lambda (H: ((\forall 
(x: T).(\forall (h1: nat).(\forall (h2: nat).(\forall (d1: nat).(\forall (d2: 
nat).((le d1 d2) \to ((eq T (lift h1 d1 t) (lift h2 (plus d2 h1) x)) \to (ex2 
T (\lambda (t2: T).(eq T x (lift h1 d1 t2))) (\lambda (t2: T).(eq T t (lift 
h2 d2 t2))))))))))))).(\lambda (t0: T).(\lambda (H0: ((\forall (x: 
T).(\forall (h1: nat).(\forall (h2: nat).(\forall (d1: nat).(\forall (d2: 
nat).((le d1 d2) \to ((eq T (lift h1 d1 t0) (lift h2 (plus d2 h1) x)) \to 
(ex2 T (\lambda (t2: T).(eq T x (lift h1 d1 t2))) (\lambda (t2: T).(eq T t0 
(lift h2 d2 t2))))))))))))).(\lambda (x: T).(\lambda (h1: nat).(\lambda (h2: 
nat).(\lambda (d1: nat).(\lambda (d2: nat).(\lambda (H1: (le d1 d2)).(\lambda 
(H2: (eq T (lift h1 d1 (THead k t t0)) (lift h2 (plus d2 h1) x))).(K_ind 
(\lambda (k0: K).((eq T (lift h1 d1 (THead k0 t t0)) (lift h2 (plus d2 h1) 
x)) \to (ex2 T (\lambda (t2: T).(eq T x (lift h1 d1 t2))) (\lambda (t2: 
T).(eq T (THead k0 t t0) (lift h2 d2 t2)))))) (\lambda (b: B).(\lambda (H3: 
(eq T (lift h1 d1 (THead (Bind b) t t0)) (lift h2 (plus d2 h1) x))).(let H4 
\def (eq_ind T (lift h1 d1 (THead (Bind b) t t0)) (\lambda (t2: T).(eq T t2 
(lift h2 (plus d2 h1) x))) H3 (THead (Bind b) (lift h1 d1 t) (lift h1 (S d1) 
t0)) (lift_bind b t t0 h1 d1)) in (ex3_2_ind T T (\lambda (y: T).(\lambda (z: 
T).(eq T x (THead (Bind b) y z)))) (\lambda (y: T).(\lambda (_: T).(eq T 
(lift h1 d1 t) (lift h2 (plus d2 h1) y)))) (\lambda (_: T).(\lambda (z: 
T).(eq T (lift h1 (S d1) t0) (lift h2 (S (plus d2 h1)) z)))) (ex2 T (\lambda 
(t2: T).(eq T x (lift h1 d1 t2))) (\lambda (t2: T).(eq T (THead (Bind b) t 
t0) (lift h2 d2 t2)))) (\lambda (x0: T).(\lambda (x1: T).(\lambda (H5: (eq T 
x (THead (Bind b) x0 x1))).(\lambda (H6: (eq T (lift h1 d1 t) (lift h2 (plus 
d2 h1) x0))).(\lambda (H7: (eq T (lift h1 (S d1) t0) (lift h2 (S (plus d2 
h1)) x1))).(eq_ind_r T (THead (Bind b) x0 x1) (\lambda (t2: T).(ex2 T 
(\lambda (t3: T).(eq T t2 (lift h1 d1 t3))) (\lambda (t3: T).(eq T (THead 
(Bind b) t t0) (lift h2 d2 t3))))) (ex2_ind T (\lambda (t2: T).(eq T x0 (lift 
h1 d1 t2))) (\lambda (t2: T).(eq T t (lift h2 d2 t2))) (ex2 T (\lambda (t2: 
T).(eq T (THead (Bind b) x0 x1) (lift h1 d1 t2))) (\lambda (t2: T).(eq T 
(THead (Bind b) t t0) (lift h2 d2 t2)))) (\lambda (x2: T).(\lambda (H8: (eq T 
x0 (lift h1 d1 x2))).(\lambda (H9: (eq T t (lift h2 d2 x2))).(eq_ind_r T 
(lift h1 d1 x2) (\lambda (t2: T).(ex2 T (\lambda (t3: T).(eq T (THead (Bind 
b) t2 x1) (lift h1 d1 t3))) (\lambda (t3: T).(eq T (THead (Bind b) t t0) 
(lift h2 d2 t3))))) (eq_ind_r T (lift h2 d2 x2) (\lambda (t2: T).(ex2 T 
(\lambda (t3: T).(eq T (THead (Bind b) (lift h1 d1 x2) x1) (lift h1 d1 t3))) 
(\lambda (t3: T).(eq T (THead (Bind b) t2 t0) (lift h2 d2 t3))))) (let H10 
\def (refl_equal nat (plus (S d2) h1)) in (let H11 \def (eq_ind nat (S (plus 
d2 h1)) (\lambda (n: nat).(eq T (lift h1 (S d1) t0) (lift h2 n x1))) H7 (plus 
(S d2) h1) H10) in (ex2_ind T (\lambda (t2: T).(eq T x1 (lift h1 (S d1) t2))) 
(\lambda (t2: T).(eq T t0 (lift h2 (S d2) t2))) (ex2 T (\lambda (t2: T).(eq T 
(THead (Bind b) (lift h1 d1 x2) x1) (lift h1 d1 t2))) (\lambda (t2: T).(eq T 
(THead (Bind b) (lift h2 d2 x2) t0) (lift h2 d2 t2)))) (\lambda (x3: 
T).(\lambda (H12: (eq T x1 (lift h1 (S d1) x3))).(\lambda (H13: (eq T t0 
(lift h2 (S d2) x3))).(eq_ind_r T (lift h1 (S d1) x3) (\lambda (t2: T).(ex2 T 
(\lambda (t3: T).(eq T (THead (Bind b) (lift h1 d1 x2) t2) (lift h1 d1 t3))) 
(\lambda (t3: T).(eq T (THead (Bind b) (lift h2 d2 x2) t0) (lift h2 d2 
t3))))) (eq_ind_r T (lift h2 (S d2) x3) (\lambda (t2: T).(ex2 T (\lambda (t3: 
T).(eq T (THead (Bind b) (lift h1 d1 x2) (lift h1 (S d1) x3)) (lift h1 d1 
t3))) (\lambda (t3: T).(eq T (THead (Bind b) (lift h2 d2 x2) t2) (lift h2 d2 
t3))))) (ex_intro2 T (\lambda (t2: T).(eq T (THead (Bind b) (lift h1 d1 x2) 
(lift h1 (S d1) x3)) (lift h1 d1 t2))) (\lambda (t2: T).(eq T (THead (Bind b) 
(lift h2 d2 x2) (lift h2 (S d2) x3)) (lift h2 d2 t2))) (THead (Bind b) x2 x3) 
(eq_ind_r T (THead (Bind b) (lift h1 d1 x2) (lift h1 (S d1) x3)) (\lambda 
(t2: T).(eq T (THead (Bind b) (lift h1 d1 x2) (lift h1 (S d1) x3)) t2)) 
(refl_equal T (THead (Bind b) (lift h1 d1 x2) (lift h1 (S d1) x3))) (lift h1 
d1 (THead (Bind b) x2 x3)) (lift_bind b x2 x3 h1 d1)) (eq_ind_r T (THead 
(Bind b) (lift h2 d2 x2) (lift h2 (S d2) x3)) (\lambda (t2: T).(eq T (THead 
(Bind b) (lift h2 d2 x2) (lift h2 (S d2) x3)) t2)) (refl_equal T (THead (Bind 
b) (lift h2 d2 x2) (lift h2 (S d2) x3))) (lift h2 d2 (THead (Bind b) x2 x3)) 
(lift_bind b x2 x3 h2 d2))) t0 H13) x1 H12)))) (H0 x1 h1 h2 (S d1) (S d2) 
(le_n_S d1 d2 H1) H11)))) t H9) x0 H8)))) (H x0 h1 h2 d1 d2 H1 H6)) x 
H5)))))) (lift_gen_bind b (lift h1 d1 t) (lift h1 (S d1) t0) x h2 (plus d2 
h1) H4))))) (\lambda (f: F).(\lambda (H3: (eq T (lift h1 d1 (THead (Flat f) t 
t0)) (lift h2 (plus d2 h1) x))).(let H4 \def (eq_ind T (lift h1 d1 (THead 
(Flat f) t t0)) (\lambda (t2: T).(eq T t2 (lift h2 (plus d2 h1) x))) H3 
(THead (Flat f) (lift h1 d1 t) (lift h1 d1 t0)) (lift_flat f t t0 h1 d1)) in 
(ex3_2_ind T T (\lambda (y: T).(\lambda (z: T).(eq T x (THead (Flat f) y 
z)))) (\lambda (y: T).(\lambda (_: T).(eq T (lift h1 d1 t) (lift h2 (plus d2 
h1) y)))) (\lambda (_: T).(\lambda (z: T).(eq T (lift h1 d1 t0) (lift h2 
(plus d2 h1) z)))) (ex2 T (\lambda (t2: T).(eq T x (lift h1 d1 t2))) (\lambda 
(t2: T).(eq T (THead (Flat f) t t0) (lift h2 d2 t2)))) (\lambda (x0: 
T).(\lambda (x1: T).(\lambda (H5: (eq T x (THead (Flat f) x0 x1))).(\lambda 
(H6: (eq T (lift h1 d1 t) (lift h2 (plus d2 h1) x0))).(\lambda (H7: (eq T 
(lift h1 d1 t0) (lift h2 (plus d2 h1) x1))).(eq_ind_r T (THead (Flat f) x0 
x1) (\lambda (t2: T).(ex2 T (\lambda (t3: T).(eq T t2 (lift h1 d1 t3))) 
(\lambda (t3: T).(eq T (THead (Flat f) t t0) (lift h2 d2 t3))))) (ex2_ind T 
(\lambda (t2: T).(eq T x0 (lift h1 d1 t2))) (\lambda (t2: T).(eq T t (lift h2 
d2 t2))) (ex2 T (\lambda (t2: T).(eq T (THead (Flat f) x0 x1) (lift h1 d1 
t2))) (\lambda (t2: T).(eq T (THead (Flat f) t t0) (lift h2 d2 t2)))) 
(\lambda (x2: T).(\lambda (H8: (eq T x0 (lift h1 d1 x2))).(\lambda (H9: (eq T 
t (lift h2 d2 x2))).(eq_ind_r T (lift h1 d1 x2) (\lambda (t2: T).(ex2 T 
(\lambda (t3: T).(eq T (THead (Flat f) t2 x1) (lift h1 d1 t3))) (\lambda (t3: 
T).(eq T (THead (Flat f) t t0) (lift h2 d2 t3))))) (eq_ind_r T (lift h2 d2 
x2) (\lambda (t2: T).(ex2 T (\lambda (t3: T).(eq T (THead (Flat f) (lift h1 
d1 x2) x1) (lift h1 d1 t3))) (\lambda (t3: T).(eq T (THead (Flat f) t2 t0) 
(lift h2 d2 t3))))) (ex2_ind T (\lambda (t2: T).(eq T x1 (lift h1 d1 t2))) 
(\lambda (t2: T).(eq T t0 (lift h2 d2 t2))) (ex2 T (\lambda (t2: T).(eq T 
(THead (Flat f) (lift h1 d1 x2) x1) (lift h1 d1 t2))) (\lambda (t2: T).(eq T 
(THead (Flat f) (lift h2 d2 x2) t0) (lift h2 d2 t2)))) (\lambda (x3: 
T).(\lambda (H10: (eq T x1 (lift h1 d1 x3))).(\lambda (H11: (eq T t0 (lift h2 
d2 x3))).(eq_ind_r T (lift h1 d1 x3) (\lambda (t2: T).(ex2 T (\lambda (t3: 
T).(eq T (THead (Flat f) (lift h1 d1 x2) t2) (lift h1 d1 t3))) (\lambda (t3: 
T).(eq T (THead (Flat f) (lift h2 d2 x2) t0) (lift h2 d2 t3))))) (eq_ind_r T 
(lift h2 d2 x3) (\lambda (t2: T).(ex2 T (\lambda (t3: T).(eq T (THead (Flat 
f) (lift h1 d1 x2) (lift h1 d1 x3)) (lift h1 d1 t3))) (\lambda (t3: T).(eq T 
(THead (Flat f) (lift h2 d2 x2) t2) (lift h2 d2 t3))))) (ex_intro2 T (\lambda 
(t2: T).(eq T (THead (Flat f) (lift h1 d1 x2) (lift h1 d1 x3)) (lift h1 d1 
t2))) (\lambda (t2: T).(eq T (THead (Flat f) (lift h2 d2 x2) (lift h2 d2 x3)) 
(lift h2 d2 t2))) (THead (Flat f) x2 x3) (eq_ind_r T (THead (Flat f) (lift h1 
d1 x2) (lift h1 d1 x3)) (\lambda (t2: T).(eq T (THead (Flat f) (lift h1 d1 
x2) (lift h1 d1 x3)) t2)) (refl_equal T (THead (Flat f) (lift h1 d1 x2) (lift 
h1 d1 x3))) (lift h1 d1 (THead (Flat f) x2 x3)) (lift_flat f x2 x3 h1 d1)) 
(eq_ind_r T (THead (Flat f) (lift h2 d2 x2) (lift h2 d2 x3)) (\lambda (t2: 
T).(eq T (THead (Flat f) (lift h2 d2 x2) (lift h2 d2 x3)) t2)) (refl_equal T 
(THead (Flat f) (lift h2 d2 x2) (lift h2 d2 x3))) (lift h2 d2 (THead (Flat f) 
x2 x3)) (lift_flat f x2 x3 h2 d2))) t0 H11) x1 H10)))) (H0 x1 h1 h2 d1 d2 H1 
H7)) t H9) x0 H8)))) (H x0 h1 h2 d1 d2 H1 H6)) x H5)))))) (lift_gen_flat f 
(lift h1 d1 t) (lift h1 d1 t0) x h2 (plus d2 h1) H4))))) k H2))))))))))))) 
t1).

lemma lifts_inj:
 \forall (xs: TList).(\forall (ts: TList).(\forall (h: nat).(\forall (d: 
nat).((eq TList (lifts h d xs) (lifts h d ts)) \to (eq TList xs ts)))))
\def
 \lambda (xs: TList).(TList_ind (\lambda (t: TList).(\forall (ts: 
TList).(\forall (h: nat).(\forall (d: nat).((eq TList (lifts h d t) (lifts h 
d ts)) \to (eq TList t ts)))))) (\lambda (ts: TList).(TList_ind (\lambda (t: 
TList).(\forall (h: nat).(\forall (d: nat).((eq TList (lifts h d TNil) (lifts 
h d t)) \to (eq TList TNil t))))) (\lambda (_: nat).(\lambda (_: 
nat).(\lambda (_: (eq TList TNil TNil)).(refl_equal TList TNil)))) (\lambda 
(t: T).(\lambda (t0: TList).(\lambda (_: ((\forall (h: nat).(\forall (d: 
nat).((eq TList TNil (lifts h d t0)) \to (eq TList TNil t0)))))).(\lambda (h: 
nat).(\lambda (d: nat).(\lambda (H0: (eq TList TNil (TCons (lift h d t) 
(lifts h d t0)))).(let H1 \def (eq_ind TList TNil (\lambda (ee: TList).(match 
ee with [TNil \Rightarrow True | (TCons _ _) \Rightarrow False])) I (TCons 
(lift h d t) (lifts h d t0)) H0) in (False_ind (eq TList TNil (TCons t t0)) 
H1)))))))) ts)) (\lambda (t: T).(\lambda (t0: TList).(\lambda (H: ((\forall 
(ts: TList).(\forall (h: nat).(\forall (d: nat).((eq TList (lifts h d t0) 
(lifts h d ts)) \to (eq TList t0 ts))))))).(\lambda (ts: TList).(TList_ind 
(\lambda (t1: TList).(\forall (h: nat).(\forall (d: nat).((eq TList (lifts h 
d (TCons t t0)) (lifts h d t1)) \to (eq TList (TCons t t0) t1))))) (\lambda 
(h: nat).(\lambda (d: nat).(\lambda (H0: (eq TList (TCons (lift h d t) (lifts 
h d t0)) TNil)).(let H1 \def (eq_ind TList (TCons (lift h d t) (lifts h d 
t0)) (\lambda (ee: TList).(match ee with [TNil \Rightarrow False | (TCons _ 
_) \Rightarrow True])) I TNil H0) in (False_ind (eq TList (TCons t t0) TNil) 
H1))))) (\lambda (t1: T).(\lambda (t2: TList).(\lambda (_: ((\forall (h: 
nat).(\forall (d: nat).((eq TList (TCons (lift h d t) (lifts h d t0)) (lifts 
h d t2)) \to (eq TList (TCons t t0) t2)))))).(\lambda (h: nat).(\lambda (d: 
nat).(\lambda (H1: (eq TList (TCons (lift h d t) (lifts h d t0)) (TCons (lift 
h d t1) (lifts h d t2)))).(let H2 \def (f_equal TList T (\lambda (e: 
TList).(match e with [TNil \Rightarrow (lref_map (\lambda (x: nat).(plus x 
h)) d t) | (TCons t3 _) \Rightarrow t3])) (TCons (lift h d t) (lifts h d t0)) 
(TCons (lift h d t1) (lifts h d t2)) H1) in ((let H3 \def (f_equal TList 
TList (\lambda (e: TList).(match e with [TNil \Rightarrow (lifts h d t0) | 
(TCons _ t3) \Rightarrow t3])) (TCons (lift h d t) (lifts h d t0)) (TCons 
(lift h d t1) (lifts h d t2)) H1) in (\lambda (H4: (eq T (lift h d t) (lift h 
d t1))).(eq_ind T t (\lambda (t3: T).(eq TList (TCons t t0) (TCons t3 t2))) 
(f_equal2 T TList TList TCons t t t0 t2 (refl_equal T t) (H t2 h d H3)) t1 
(lift_inj t t1 h d H4)))) H2)))))))) ts))))) xs).

