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

include "basic_1/r/defs.ma".

include "basic_1/s/defs.ma".

theorem r_S:
 \forall (k: K).(\forall (i: nat).(eq nat (r k (S i)) (S (r k i))))
\def
 \lambda (k: K).(let TMP_5 \def (\lambda (k0: K).(\forall (i: nat).(let TMP_1 
\def (S i) in (let TMP_2 \def (r k0 TMP_1) in (let TMP_3 \def (r k0 i) in 
(let TMP_4 \def (S TMP_3) in (eq nat TMP_2 TMP_4))))))) in (let TMP_9 \def 
(\lambda (b: B).(\lambda (i: nat).(let TMP_6 \def (Bind b) in (let TMP_7 \def 
(r TMP_6 i) in (let TMP_8 \def (S TMP_7) in (refl_equal nat TMP_8)))))) in 
(let TMP_13 \def (\lambda (f: F).(\lambda (i: nat).(let TMP_10 \def (Flat f) 
in (let TMP_11 \def (r TMP_10 i) in (let TMP_12 \def (S TMP_11) in 
(refl_equal nat TMP_12)))))) in (K_ind TMP_5 TMP_9 TMP_13 k)))).

theorem r_plus:
 \forall (k: K).(\forall (i: nat).(\forall (j: nat).(eq nat (r k (plus i j)) 
(plus (r k i) j))))
\def
 \lambda (k: K).(let TMP_5 \def (\lambda (k0: K).(\forall (i: nat).(\forall 
(j: nat).(let TMP_1 \def (plus i j) in (let TMP_2 \def (r k0 TMP_1) in (let 
TMP_3 \def (r k0 i) in (let TMP_4 \def (plus TMP_3 j) in (eq nat TMP_2 
TMP_4)))))))) in (let TMP_9 \def (\lambda (b: B).(\lambda (i: nat).(\lambda 
(j: nat).(let TMP_6 \def (Bind b) in (let TMP_7 \def (r TMP_6 i) in (let 
TMP_8 \def (plus TMP_7 j) in (refl_equal nat TMP_8))))))) in (let TMP_13 \def 
(\lambda (f: F).(\lambda (i: nat).(\lambda (j: nat).(let TMP_10 \def (Flat f) 
in (let TMP_11 \def (r TMP_10 i) in (let TMP_12 \def (plus TMP_11 j) in 
(refl_equal nat TMP_12))))))) in (K_ind TMP_5 TMP_9 TMP_13 k)))).

theorem r_plus_sym:
 \forall (k: K).(\forall (i: nat).(\forall (j: nat).(eq nat (r k (plus i j)) 
(plus i (r k j)))))
\def
 \lambda (k: K).(let TMP_5 \def (\lambda (k0: K).(\forall (i: nat).(\forall 
(j: nat).(let TMP_1 \def (plus i j) in (let TMP_2 \def (r k0 TMP_1) in (let 
TMP_3 \def (r k0 j) in (let TMP_4 \def (plus i TMP_3) in (eq nat TMP_2 
TMP_4)))))))) in (let TMP_7 \def (\lambda (_: B).(\lambda (i: nat).(\lambda 
(j: nat).(let TMP_6 \def (plus i j) in (refl_equal nat TMP_6))))) in (let 
TMP_8 \def (\lambda (_: F).(\lambda (i: nat).(\lambda (j: nat).(plus_n_Sm i 
j)))) in (K_ind TMP_5 TMP_7 TMP_8 k)))).

theorem r_minus:
 \forall (i: nat).(\forall (n: nat).((lt n i) \to (\forall (k: K).(eq nat 
(minus (r k i) (S n)) (r k (minus i (S n)))))))
\def
 \lambda (i: nat).(\lambda (n: nat).(\lambda (H: (lt n i)).(\lambda (k: 
K).(let TMP_7 \def (\lambda (k0: K).(let TMP_1 \def (r k0 i) in (let TMP_2 
\def (S n) in (let TMP_3 \def (minus TMP_1 TMP_2) in (let TMP_4 \def (S n) in 
(let TMP_5 \def (minus i TMP_4) in (let TMP_6 \def (r k0 TMP_5) in (eq nat 
TMP_3 TMP_6)))))))) in (let TMP_10 \def (\lambda (_: B).(let TMP_8 \def (S n) 
in (let TMP_9 \def (minus i TMP_8) in (refl_equal nat TMP_9)))) in (let 
TMP_11 \def (\lambda (_: F).(minus_x_Sy i n H)) in (K_ind TMP_7 TMP_10 TMP_11 
k))))))).

theorem r_dis:
 \forall (k: K).(\forall (P: Prop).(((((\forall (i: nat).(eq nat (r k i) i))) 
\to P)) \to (((((\forall (i: nat).(eq nat (r k i) (S i)))) \to P)) \to P)))
\def
 \lambda (k: K).(let TMP_1 \def (\lambda (k0: K).(\forall (P: 
Prop).(((((\forall (i: nat).(eq nat (r k0 i) i))) \to P)) \to (((((\forall 
(i: nat).(eq nat (r k0 i) (S i)))) \to P)) \to P)))) in (let TMP_3 \def 
(\lambda (b: B).(\lambda (P: Prop).(\lambda (H: ((((\forall (i: nat).(eq nat 
(r (Bind b) i) i))) \to P))).(\lambda (_: ((((\forall (i: nat).(eq nat (r 
(Bind b) i) (S i)))) \to P))).(let TMP_2 \def (\lambda (i: nat).(refl_equal 
nat i)) in (H TMP_2)))))) in (let TMP_6 \def (\lambda (f: F).(\lambda (P: 
Prop).(\lambda (_: ((((\forall (i: nat).(eq nat (r (Flat f) i) i))) \to 
P))).(\lambda (H0: ((((\forall (i: nat).(eq nat (r (Flat f) i) (S i)))) \to 
P))).(let TMP_5 \def (\lambda (i: nat).(let TMP_4 \def (S i) in (refl_equal 
nat TMP_4))) in (H0 TMP_5)))))) in (K_ind TMP_1 TMP_3 TMP_6 k)))).

theorem s_r:
 \forall (k: K).(\forall (i: nat).(eq nat (s k (r k i)) (S i)))
\def
 \lambda (k: K).(let TMP_4 \def (\lambda (k0: K).(\forall (i: nat).(let TMP_1 
\def (r k0 i) in (let TMP_2 \def (s k0 TMP_1) in (let TMP_3 \def (S i) in (eq 
nat TMP_2 TMP_3)))))) in (let TMP_6 \def (\lambda (_: B).(\lambda (i: 
nat).(let TMP_5 \def (S i) in (refl_equal nat TMP_5)))) in (let TMP_8 \def 
(\lambda (_: F).(\lambda (i: nat).(let TMP_7 \def (S i) in (refl_equal nat 
TMP_7)))) in (K_ind TMP_4 TMP_6 TMP_8 k)))).

theorem r_arith0:
 \forall (k: K).(\forall (i: nat).(eq nat (minus (r k (S i)) (S O)) (r k i)))
\def
 \lambda (k: K).(\lambda (i: nat).(let TMP_1 \def (r k i) in (let TMP_2 \def 
(S TMP_1) in (let TMP_6 \def (\lambda (n: nat).(let TMP_3 \def (S O) in (let 
TMP_4 \def (minus n TMP_3) in (let TMP_5 \def (r k i) in (eq nat TMP_4 
TMP_5))))) in (let TMP_7 \def (r k i) in (let TMP_9 \def (\lambda (n: 
nat).(let TMP_8 \def (r k i) in (eq nat n TMP_8))) in (let TMP_10 \def (r k 
i) in (let TMP_11 \def (refl_equal nat TMP_10) in (let TMP_12 \def (r k i) in 
(let TMP_13 \def (S TMP_12) in (let TMP_14 \def (S O) in (let TMP_15 \def 
(minus TMP_13 TMP_14) in (let TMP_16 \def (r k i) in (let TMP_17 \def 
(minus_Sx_SO TMP_16) in (let TMP_18 \def (eq_ind_r nat TMP_7 TMP_9 TMP_11 
TMP_15 TMP_17) in (let TMP_19 \def (S i) in (let TMP_20 \def (r k TMP_19) in 
(let TMP_21 \def (r_S k i) in (eq_ind_r nat TMP_2 TMP_6 TMP_18 TMP_20 
TMP_21))))))))))))))))))).

theorem r_arith1:
 \forall (k: K).(\forall (i: nat).(\forall (j: nat).(eq nat (minus (r k (S 
i)) (S j)) (minus (r k i) j))))
\def
 \lambda (k: K).(\lambda (i: nat).(\lambda (j: nat).(let TMP_1 \def (r k i) 
in (let TMP_2 \def (S TMP_1) in (let TMP_7 \def (\lambda (n: nat).(let TMP_3 
\def (S j) in (let TMP_4 \def (minus n TMP_3) in (let TMP_5 \def (r k i) in 
(let TMP_6 \def (minus TMP_5 j) in (eq nat TMP_4 TMP_6)))))) in (let TMP_8 
\def (r k i) in (let TMP_9 \def (minus TMP_8 j) in (let TMP_10 \def 
(refl_equal nat TMP_9) in (let TMP_11 \def (S i) in (let TMP_12 \def (r k 
TMP_11) in (let TMP_13 \def (r_S k i) in (eq_ind_r nat TMP_2 TMP_7 TMP_10 
TMP_12 TMP_13)))))))))))).

theorem r_arith2:
 \forall (k: K).(\forall (i: nat).(\forall (j: nat).((le (S i) (s k j)) \to 
(le (r k i) j))))
\def
 \lambda (k: K).(let TMP_2 \def (\lambda (k0: K).(\forall (i: nat).(\forall 
(j: nat).((le (S i) (s k0 j)) \to (let TMP_1 \def (r k0 i) in (le TMP_1 
j)))))) in (let TMP_3 \def (\lambda (_: B).(\lambda (i: nat).(\lambda (j: 
nat).(\lambda (H: (le (S i) (S j))).(let H_y \def (le_S_n i j H) in H_y))))) 
in (let TMP_4 \def (\lambda (_: F).(\lambda (i: nat).(\lambda (j: 
nat).(\lambda (H: (le (S i) j)).H)))) in (K_ind TMP_2 TMP_3 TMP_4 k)))).

theorem r_arith3:
 \forall (k: K).(\forall (i: nat).(\forall (j: nat).((le (s k j) (S i)) \to 
(le j (r k i)))))
\def
 \lambda (k: K).(let TMP_2 \def (\lambda (k0: K).(\forall (i: nat).(\forall 
(j: nat).((le (s k0 j) (S i)) \to (let TMP_1 \def (r k0 i) in (le j 
TMP_1)))))) in (let TMP_3 \def (\lambda (_: B).(\lambda (i: nat).(\lambda (j: 
nat).(\lambda (H: (le (S j) (S i))).(let H_y \def (le_S_n j i H) in H_y))))) 
in (let TMP_4 \def (\lambda (_: F).(\lambda (i: nat).(\lambda (j: 
nat).(\lambda (H: (le j (S i))).H)))) in (K_ind TMP_2 TMP_3 TMP_4 k)))).

theorem r_arith4:
 \forall (k: K).(\forall (i: nat).(\forall (j: nat).(eq nat (minus (S i) (s k 
j)) (minus (r k i) j))))
\def
 \lambda (k: K).(let TMP_6 \def (\lambda (k0: K).(\forall (i: nat).(\forall 
(j: nat).(let TMP_1 \def (S i) in (let TMP_2 \def (s k0 j) in (let TMP_3 \def 
(minus TMP_1 TMP_2) in (let TMP_4 \def (r k0 i) in (let TMP_5 \def (minus 
TMP_4 j) in (eq nat TMP_3 TMP_5))))))))) in (let TMP_10 \def (\lambda (b: 
B).(\lambda (i: nat).(\lambda (j: nat).(let TMP_7 \def (Bind b) in (let TMP_8 
\def (r TMP_7 i) in (let TMP_9 \def (minus TMP_8 j) in (refl_equal nat 
TMP_9))))))) in (let TMP_14 \def (\lambda (f: F).(\lambda (i: nat).(\lambda 
(j: nat).(let TMP_11 \def (Flat f) in (let TMP_12 \def (r TMP_11 i) in (let 
TMP_13 \def (minus TMP_12 j) in (refl_equal nat TMP_13))))))) in (K_ind TMP_6 
TMP_10 TMP_14 k)))).

theorem r_arith5:
 \forall (k: K).(\forall (i: nat).(\forall (j: nat).((lt (s k j) (S i)) \to 
(lt j (r k i)))))
\def
 \lambda (k: K).(let TMP_2 \def (\lambda (k0: K).(\forall (i: nat).(\forall 
(j: nat).((lt (s k0 j) (S i)) \to (let TMP_1 \def (r k0 i) in (lt j 
TMP_1)))))) in (let TMP_3 \def (\lambda (_: B).(\lambda (i: nat).(\lambda (j: 
nat).(\lambda (H: (lt (S j) (S i))).(lt_S_n j i H))))) in (let TMP_4 \def 
(\lambda (_: F).(\lambda (i: nat).(\lambda (j: nat).(\lambda (H: (lt j (S 
i))).H)))) in (K_ind TMP_2 TMP_3 TMP_4 k)))).

theorem r_arith6:
 \forall (k: K).(\forall (i: nat).(\forall (j: nat).(eq nat (minus (r k i) (S 
j)) (minus i (s k j)))))
\def
 \lambda (k: K).(let TMP_6 \def (\lambda (k0: K).(\forall (i: nat).(\forall 
(j: nat).(let TMP_1 \def (r k0 i) in (let TMP_2 \def (S j) in (let TMP_3 \def 
(minus TMP_1 TMP_2) in (let TMP_4 \def (s k0 j) in (let TMP_5 \def (minus i 
TMP_4) in (eq nat TMP_3 TMP_5))))))))) in (let TMP_10 \def (\lambda (b: 
B).(\lambda (i: nat).(\lambda (j: nat).(let TMP_7 \def (Bind b) in (let TMP_8 
\def (s TMP_7 j) in (let TMP_9 \def (minus i TMP_8) in (refl_equal nat 
TMP_9))))))) in (let TMP_14 \def (\lambda (f: F).(\lambda (i: nat).(\lambda 
(j: nat).(let TMP_11 \def (Flat f) in (let TMP_12 \def (s TMP_11 j) in (let 
TMP_13 \def (minus i TMP_12) in (refl_equal nat TMP_13))))))) in (K_ind TMP_6 
TMP_10 TMP_14 k)))).

theorem r_arith7:
 \forall (k: K).(\forall (i: nat).(\forall (j: nat).((eq nat (S i) (s k j)) 
\to (eq nat (r k i) j))))
\def
 \lambda (k: K).(let TMP_2 \def (\lambda (k0: K).(\forall (i: nat).(\forall 
(j: nat).((eq nat (S i) (s k0 j)) \to (let TMP_1 \def (r k0 i) in (eq nat 
TMP_1 j)))))) in (let TMP_3 \def (\lambda (_: B).(\lambda (i: nat).(\lambda 
(j: nat).(\lambda (H: (eq nat (S i) (S j))).(eq_add_S i j H))))) in (let 
TMP_4 \def (\lambda (_: F).(\lambda (i: nat).(\lambda (j: nat).(\lambda (H: 
(eq nat (S i) j)).H)))) in (K_ind TMP_2 TMP_3 TMP_4 k)))).

