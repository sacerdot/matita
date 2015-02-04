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

include "basic_1/s/defs.ma".

theorem s_S:
 \forall (k: K).(\forall (i: nat).(eq nat (s k (S i)) (S (s k i))))
\def
 \lambda (k: K).(let TMP_5 \def (\lambda (k0: K).(\forall (i: nat).(let TMP_1 
\def (S i) in (let TMP_2 \def (s k0 TMP_1) in (let TMP_3 \def (s k0 i) in 
(let TMP_4 \def (S TMP_3) in (eq nat TMP_2 TMP_4))))))) in (let TMP_9 \def 
(\lambda (b: B).(\lambda (i: nat).(let TMP_6 \def (Bind b) in (let TMP_7 \def 
(s TMP_6 i) in (let TMP_8 \def (S TMP_7) in (refl_equal nat TMP_8)))))) in 
(let TMP_13 \def (\lambda (f: F).(\lambda (i: nat).(let TMP_10 \def (Flat f) 
in (let TMP_11 \def (s TMP_10 i) in (let TMP_12 \def (S TMP_11) in 
(refl_equal nat TMP_12)))))) in (K_ind TMP_5 TMP_9 TMP_13 k)))).

theorem s_plus:
 \forall (k: K).(\forall (i: nat).(\forall (j: nat).(eq nat (s k (plus i j)) 
(plus (s k i) j))))
\def
 \lambda (k: K).(let TMP_5 \def (\lambda (k0: K).(\forall (i: nat).(\forall 
(j: nat).(let TMP_1 \def (plus i j) in (let TMP_2 \def (s k0 TMP_1) in (let 
TMP_3 \def (s k0 i) in (let TMP_4 \def (plus TMP_3 j) in (eq nat TMP_2 
TMP_4)))))))) in (let TMP_9 \def (\lambda (b: B).(\lambda (i: nat).(\lambda 
(j: nat).(let TMP_6 \def (Bind b) in (let TMP_7 \def (s TMP_6 i) in (let 
TMP_8 \def (plus TMP_7 j) in (refl_equal nat TMP_8))))))) in (let TMP_13 \def 
(\lambda (f: F).(\lambda (i: nat).(\lambda (j: nat).(let TMP_10 \def (Flat f) 
in (let TMP_11 \def (s TMP_10 i) in (let TMP_12 \def (plus TMP_11 j) in 
(refl_equal nat TMP_12))))))) in (K_ind TMP_5 TMP_9 TMP_13 k)))).

theorem s_plus_sym:
 \forall (k: K).(\forall (i: nat).(\forall (j: nat).(eq nat (s k (plus i j)) 
(plus i (s k j)))))
\def
 \lambda (k: K).(let TMP_5 \def (\lambda (k0: K).(\forall (i: nat).(\forall 
(j: nat).(let TMP_1 \def (plus i j) in (let TMP_2 \def (s k0 TMP_1) in (let 
TMP_3 \def (s k0 j) in (let TMP_4 \def (plus i TMP_3) in (eq nat TMP_2 
TMP_4)))))))) in (let TMP_17 \def (\lambda (_: B).(\lambda (i: nat).(\lambda 
(j: nat).(let TMP_6 \def (S j) in (let TMP_7 \def (plus i TMP_6) in (let 
TMP_10 \def (\lambda (n: nat).(let TMP_8 \def (S j) in (let TMP_9 \def (plus 
i TMP_8) in (eq nat n TMP_9)))) in (let TMP_11 \def (S j) in (let TMP_12 \def 
(plus i TMP_11) in (let TMP_13 \def (refl_equal nat TMP_12) in (let TMP_14 
\def (plus i j) in (let TMP_15 \def (S TMP_14) in (let TMP_16 \def (plus_n_Sm 
i j) in (eq_ind_r nat TMP_7 TMP_10 TMP_13 TMP_15 TMP_16))))))))))))) in (let 
TMP_21 \def (\lambda (f: F).(\lambda (i: nat).(\lambda (j: nat).(let TMP_18 
\def (Flat f) in (let TMP_19 \def (s TMP_18 j) in (let TMP_20 \def (plus i 
TMP_19) in (refl_equal nat TMP_20))))))) in (K_ind TMP_5 TMP_17 TMP_21 k)))).

theorem s_minus:
 \forall (k: K).(\forall (i: nat).(\forall (j: nat).((le j i) \to (eq nat (s 
k (minus i j)) (minus (s k i) j)))))
\def
 \lambda (k: K).(let TMP_5 \def (\lambda (k0: K).(\forall (i: nat).(\forall 
(j: nat).((le j i) \to (let TMP_1 \def (minus i j) in (let TMP_2 \def (s k0 
TMP_1) in (let TMP_3 \def (s k0 i) in (let TMP_4 \def (minus TMP_3 j) in (eq 
nat TMP_2 TMP_4))))))))) in (let TMP_17 \def (\lambda (_: B).(\lambda (i: 
nat).(\lambda (j: nat).(\lambda (H: (le j i)).(let TMP_6 \def (S i) in (let 
TMP_7 \def (minus TMP_6 j) in (let TMP_10 \def (\lambda (n: nat).(let TMP_8 
\def (S i) in (let TMP_9 \def (minus TMP_8 j) in (eq nat n TMP_9)))) in (let 
TMP_11 \def (S i) in (let TMP_12 \def (minus TMP_11 j) in (let TMP_13 \def 
(refl_equal nat TMP_12) in (let TMP_14 \def (minus i j) in (let TMP_15 \def 
(S TMP_14) in (let TMP_16 \def (minus_Sn_m i j H) in (eq_ind_r nat TMP_7 
TMP_10 TMP_13 TMP_15 TMP_16)))))))))))))) in (let TMP_21 \def (\lambda (f: 
F).(\lambda (i: nat).(\lambda (j: nat).(\lambda (_: (le j i)).(let TMP_18 
\def (Flat f) in (let TMP_19 \def (s TMP_18 i) in (let TMP_20 \def (minus 
TMP_19 j) in (refl_equal nat TMP_20)))))))) in (K_ind TMP_5 TMP_17 TMP_21 
k)))).

theorem minus_s_s:
 \forall (k: K).(\forall (i: nat).(\forall (j: nat).(eq nat (minus (s k i) (s 
k j)) (minus i j))))
\def
 \lambda (k: K).(let TMP_5 \def (\lambda (k0: K).(\forall (i: nat).(\forall 
(j: nat).(let TMP_1 \def (s k0 i) in (let TMP_2 \def (s k0 j) in (let TMP_3 
\def (minus TMP_1 TMP_2) in (let TMP_4 \def (minus i j) in (eq nat TMP_3 
TMP_4)))))))) in (let TMP_7 \def (\lambda (_: B).(\lambda (i: nat).(\lambda 
(j: nat).(let TMP_6 \def (minus i j) in (refl_equal nat TMP_6))))) in (let 
TMP_9 \def (\lambda (_: F).(\lambda (i: nat).(\lambda (j: nat).(let TMP_8 
\def (minus i j) in (refl_equal nat TMP_8))))) in (K_ind TMP_5 TMP_7 TMP_9 
k)))).

theorem s_le:
 \forall (k: K).(\forall (i: nat).(\forall (j: nat).((le i j) \to (le (s k i) 
(s k j)))))
\def
 \lambda (k: K).(let TMP_3 \def (\lambda (k0: K).(\forall (i: nat).(\forall 
(j: nat).((le i j) \to (let TMP_1 \def (s k0 i) in (let TMP_2 \def (s k0 j) 
in (le TMP_1 TMP_2))))))) in (let TMP_4 \def (\lambda (_: B).(\lambda (i: 
nat).(\lambda (j: nat).(\lambda (H: (le i j)).(le_n_S i j H))))) in (let 
TMP_5 \def (\lambda (_: F).(\lambda (i: nat).(\lambda (j: nat).(\lambda (H: 
(le i j)).H)))) in (K_ind TMP_3 TMP_4 TMP_5 k)))).

theorem s_lt:
 \forall (k: K).(\forall (i: nat).(\forall (j: nat).((lt i j) \to (lt (s k i) 
(s k j)))))
\def
 \lambda (k: K).(let TMP_3 \def (\lambda (k0: K).(\forall (i: nat).(\forall 
(j: nat).((lt i j) \to (let TMP_1 \def (s k0 i) in (let TMP_2 \def (s k0 j) 
in (lt TMP_1 TMP_2))))))) in (let TMP_4 \def (\lambda (_: B).(\lambda (i: 
nat).(\lambda (j: nat).(\lambda (H: (lt i j)).(lt_n_S i j H))))) in (let 
TMP_5 \def (\lambda (_: F).(\lambda (i: nat).(\lambda (j: nat).(\lambda (H: 
(lt i j)).H)))) in (K_ind TMP_3 TMP_4 TMP_5 k)))).

theorem s_inc:
 \forall (k: K).(\forall (i: nat).(le i (s k i)))
\def
 \lambda (k: K).(let TMP_2 \def (\lambda (k0: K).(\forall (i: nat).(let TMP_1 
\def (s k0 i) in (le i TMP_1)))) in (let TMP_30 \def (\lambda (b: B).(\lambda 
(i: nat).(let TMP_3 \def (Bind b) in (let TMP_4 \def (s TMP_3 i) in (let 
TMP_5 \def (S i) in (let TMP_6 \def (Bind b) in (let TMP_7 \def (s TMP_6 i) 
in (let TMP_8 \def (S TMP_7) in (let TMP_9 \def (S i) in (let TMP_10 \def (S 
TMP_9) in (let TMP_11 \def (Bind b) in (let TMP_12 \def (s TMP_11 i) in (let 
TMP_13 \def (S TMP_12) in (let TMP_14 \def (S TMP_13) in (let TMP_15 \def (S 
i) in (let TMP_16 \def (S TMP_15) in (let TMP_17 \def (S TMP_16) in (let 
TMP_18 \def (Bind b) in (let TMP_19 \def (s TMP_18 i) in (let TMP_20 \def (S 
TMP_19) in (let TMP_21 \def (S TMP_20) in (let TMP_22 \def (Bind b) in (let 
TMP_23 \def (s TMP_22 i) in (let TMP_24 \def (S TMP_23) in (let TMP_25 \def 
(S TMP_24) in (let TMP_26 \def (le_n TMP_25) in (let TMP_27 \def (le_S TMP_17 
TMP_21 TMP_26) in (let TMP_28 \def (le_S_n TMP_10 TMP_14 TMP_27) in (let 
TMP_29 \def (le_S_n TMP_5 TMP_8 TMP_28) in (le_S_n i TMP_4 
TMP_29)))))))))))))))))))))))))))))) in (let TMP_33 \def (\lambda (f: 
F).(\lambda (i: nat).(let TMP_31 \def (Flat f) in (let TMP_32 \def (s TMP_31 
i) in (le_n TMP_32))))) in (K_ind TMP_2 TMP_30 TMP_33 k)))).

theorem s_arith0:
 \forall (k: K).(\forall (i: nat).(eq nat (minus (s k i) (s k O)) i))
\def
 \lambda (k: K).(\lambda (i: nat).(let TMP_1 \def (minus i O) in (let TMP_2 
\def (\lambda (n: nat).(eq nat n i)) in (let TMP_3 \def (\lambda (n: nat).(eq 
nat n i)) in (let TMP_4 \def (refl_equal nat i) in (let TMP_5 \def (minus i 
O) in (let TMP_6 \def (minus_n_O i) in (let TMP_7 \def (eq_ind nat i TMP_3 
TMP_4 TMP_5 TMP_6) in (let TMP_8 \def (s k i) in (let TMP_9 \def (s k O) in 
(let TMP_10 \def (minus TMP_8 TMP_9) in (let TMP_11 \def (minus_s_s k i O) in 
(eq_ind_r nat TMP_1 TMP_2 TMP_7 TMP_10 TMP_11))))))))))))).

theorem s_arith1:
 \forall (b: B).(\forall (i: nat).(eq nat (minus (s (Bind b) i) (S O)) i))
\def
 \lambda (_: B).(\lambda (i: nat).(let TMP_1 \def (\lambda (n: nat).(eq nat n 
i)) in (let TMP_2 \def (refl_equal nat i) in (let TMP_3 \def (minus i O) in 
(let TMP_4 \def (minus_n_O i) in (eq_ind nat i TMP_1 TMP_2 TMP_3 TMP_4)))))).

