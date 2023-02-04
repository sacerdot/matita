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

(* ********************************************************************** *)
(*                                                                        *)
(* Sviluppato da:                                                         *)
(*   Cosimo Oliboni, oliboni@cs.unibo.it                                  *)
(*                                                                        *)
(* ********************************************************************** *)

include "freescale/byte8.ma".

(* ************************** *)
(* DEFINIZIONE ASCII MINIMALE *)
(* ************************** *)

inductive ascii_min : Type ≝
(* numeri *)  
  ch_0: ascii_min
| ch_1: ascii_min
| ch_2: ascii_min
| ch_3: ascii_min
| ch_4: ascii_min
| ch_5: ascii_min
| ch_6: ascii_min
| ch_7: ascii_min
| ch_8: ascii_min
| ch_9: ascii_min

(* simboli *)
| ch__: ascii_min

(* maiuscole *)
| ch_A: ascii_min
| ch_B: ascii_min
| ch_C: ascii_min
| ch_D: ascii_min
| ch_E: ascii_min
| ch_F: ascii_min
| ch_G: ascii_min
| ch_H: ascii_min
| ch_I: ascii_min
| ch_J: ascii_min
| ch_K: ascii_min
| ch_L: ascii_min
| ch_M: ascii_min
| ch_N: ascii_min
| ch_O: ascii_min
| ch_P: ascii_min
| ch_Q: ascii_min
| ch_R: ascii_min
| ch_S: ascii_min
| ch_T: ascii_min
| ch_U: ascii_min
| ch_V: ascii_min
| ch_W: ascii_min
| ch_X: ascii_min
| ch_Y: ascii_min
| ch_Z: ascii_min

(* minuscole *)
| ch_a: ascii_min
| ch_b: ascii_min
| ch_c: ascii_min
| ch_d: ascii_min
| ch_e: ascii_min
| ch_f: ascii_min
| ch_g: ascii_min
| ch_h: ascii_min
| ch_i: ascii_min
| ch_j: ascii_min
| ch_k: ascii_min
| ch_l: ascii_min
| ch_m: ascii_min
| ch_n: ascii_min
| ch_o: ascii_min
| ch_p: ascii_min
| ch_q: ascii_min
| ch_r: ascii_min
| ch_s: ascii_min
| ch_t: ascii_min
| ch_u: ascii_min
| ch_v: ascii_min
| ch_w: ascii_min
| ch_x: ascii_min
| ch_y: ascii_min
| ch_z: ascii_min.

(* ascii_min → byte8 *)
definition magic_of_ascii_min ≝
λc:ascii_min.match c with
(* numeri *)  
[ ch_0 ⇒ 〈x0,x0〉
| ch_1 ⇒ 〈x0,x1〉
| ch_2 ⇒ 〈x0,x2〉
| ch_3 ⇒ 〈x0,x3〉
| ch_4 ⇒ 〈x0,x4〉
| ch_5 ⇒ 〈x0,x5〉
| ch_6 ⇒ 〈x0,x6〉
| ch_7 ⇒ 〈x0,x7〉
| ch_8 ⇒ 〈x0,x8〉
| ch_9 ⇒ 〈x0,x9〉

(* simboli *)
| ch__ ⇒ 〈x0,xA〉

(* maiuscole *)
| ch_A ⇒ 〈x0,xB〉
| ch_B ⇒ 〈x0,xC〉
| ch_C ⇒ 〈x0,xD〉
| ch_D ⇒ 〈x0,xE〉
| ch_E ⇒ 〈x0,xF〉
| ch_F ⇒ 〈x1,x0〉
| ch_G ⇒ 〈x1,x1〉
| ch_H ⇒ 〈x1,x2〉
| ch_I ⇒ 〈x1,x3〉
| ch_J ⇒ 〈x1,x4〉
| ch_K ⇒ 〈x1,x5〉
| ch_L ⇒ 〈x1,x6〉
| ch_M ⇒ 〈x1,x7〉
| ch_N ⇒ 〈x1,x8〉
| ch_O ⇒ 〈x1,x9〉
| ch_P ⇒ 〈x1,xA〉
| ch_Q ⇒ 〈x1,xB〉
| ch_R ⇒ 〈x1,xC〉
| ch_S ⇒ 〈x1,xD〉
| ch_T ⇒ 〈x1,xE〉
| ch_U ⇒ 〈x1,xF〉
| ch_V ⇒ 〈x2,x0〉
| ch_W ⇒ 〈x2,x1〉
| ch_X ⇒ 〈x2,x2〉
| ch_Y ⇒ 〈x2,x3〉
| ch_Z ⇒ 〈x2,x4〉

(* minuscole *)
| ch_a ⇒ 〈x2,x5〉
| ch_b ⇒ 〈x2,x6〉
| ch_c ⇒ 〈x2,x7〉
| ch_d ⇒ 〈x2,x8〉
| ch_e ⇒ 〈x2,x9〉
| ch_f ⇒ 〈x2,xA〉
| ch_g ⇒ 〈x2,xB〉
| ch_h ⇒ 〈x2,xC〉
| ch_i ⇒ 〈x2,xD〉
| ch_j ⇒ 〈x2,xE〉
| ch_k ⇒ 〈x2,xF〉
| ch_l ⇒ 〈x3,x0〉
| ch_m ⇒ 〈x3,x1〉
| ch_n ⇒ 〈x3,x2〉
| ch_o ⇒ 〈x3,x3〉
| ch_p ⇒ 〈x3,x4〉
| ch_q ⇒ 〈x3,x5〉
| ch_r ⇒ 〈x3,x6〉
| ch_s ⇒ 〈x3,x7〉
| ch_t ⇒ 〈x3,x8〉
| ch_u ⇒ 〈x3,x9〉
| ch_v ⇒ 〈x3,xA〉
| ch_w ⇒ 〈x3,xB〉
| ch_x ⇒ 〈x3,xC〉
| ch_y ⇒ 〈x3,xD〉
| ch_z ⇒ 〈x3,xE〉
].

(* confronto fra ascii_min *)
definition eqAsciiMin ≝
λc,c':ascii_min.(eq_b8 (magic_of_ascii_min c) (magic_of_ascii_min c')).

lemma eq_to_eqasciimin : ∀a1,a2.a1 = a2 → eqAsciiMin a1 a2 = true.
 do 3 intro;
 unfold eqAsciiMin;
 rewrite > H;
 elim a2;
 reflexivity.
qed.

(* 63^2 casi... *)
lemma eqasciimin_to_eq_00 : ∀a.eqAsciiMin ch_0 a = true → ch_0 = a. intro; elim a 0; normalize; intro; try destruct H; reflexivity. qed.
lemma eqasciimin_to_eq_01 : ∀a.eqAsciiMin ch_1 a = true → ch_1 = a. intro; elim a 0; normalize; intro; try destruct H; reflexivity. qed.
lemma eqasciimin_to_eq_02 : ∀a.eqAsciiMin ch_2 a = true → ch_2 = a. intro; elim a 0; normalize; intro; try destruct H; reflexivity. qed.
lemma eqasciimin_to_eq_03 : ∀a.eqAsciiMin ch_3 a = true → ch_3 = a. intro; elim a 0; normalize; intro; try destruct H; reflexivity. qed.
lemma eqasciimin_to_eq_04 : ∀a.eqAsciiMin ch_4 a = true → ch_4 = a. intro; elim a 0; normalize; intro; try destruct H; reflexivity. qed.
lemma eqasciimin_to_eq_05 : ∀a.eqAsciiMin ch_5 a = true → ch_5 = a. intro; elim a 0; normalize; intro; try destruct H; reflexivity. qed.
lemma eqasciimin_to_eq_06 : ∀a.eqAsciiMin ch_6 a = true → ch_6 = a. intro; elim a 0; normalize; intro; try destruct H; reflexivity. qed.
lemma eqasciimin_to_eq_07 : ∀a.eqAsciiMin ch_7 a = true → ch_7 = a. intro; elim a 0; normalize; intro; try destruct H; reflexivity. qed.
lemma eqasciimin_to_eq_08 : ∀a.eqAsciiMin ch_8 a = true → ch_8 = a. intro; elim a 0; normalize; intro; try destruct H; reflexivity. qed.
lemma eqasciimin_to_eq_09 : ∀a.eqAsciiMin ch_9 a = true → ch_9 = a. intro; elim a 0; normalize; intro; try destruct H; reflexivity. qed.
lemma eqasciimin_to_eq_10 : ∀a.eqAsciiMin ch__ a = true → ch__ = a. intro; elim a 0; normalize; intro; try destruct H; reflexivity. qed.
lemma eqasciimin_to_eq_11 : ∀a.eqAsciiMin ch_A a = true → ch_A = a. intro; elim a 0; normalize; intro; try destruct H; reflexivity. qed.
lemma eqasciimin_to_eq_12 : ∀a.eqAsciiMin ch_B a = true → ch_B = a. intro; elim a 0; normalize; intro; try destruct H; reflexivity. qed.
lemma eqasciimin_to_eq_13 : ∀a.eqAsciiMin ch_C a = true → ch_C = a. intro; elim a 0; normalize; intro; try destruct H; reflexivity. qed.
lemma eqasciimin_to_eq_14 : ∀a.eqAsciiMin ch_D a = true → ch_D = a. intro; elim a 0; normalize; intro; try destruct H; reflexivity. qed.
lemma eqasciimin_to_eq_15 : ∀a.eqAsciiMin ch_E a = true → ch_E = a. intro; elim a 0; normalize; intro; try destruct H; reflexivity. qed.
lemma eqasciimin_to_eq_16 : ∀a.eqAsciiMin ch_F a = true → ch_F = a. intro; elim a 0; normalize; intro; try destruct H; reflexivity. qed.
lemma eqasciimin_to_eq_17 : ∀a.eqAsciiMin ch_G a = true → ch_G = a. intro; elim a 0; normalize; intro; try destruct H; reflexivity. qed.
lemma eqasciimin_to_eq_18 : ∀a.eqAsciiMin ch_H a = true → ch_H = a. intro; elim a 0; normalize; intro; try destruct H; reflexivity. qed.
lemma eqasciimin_to_eq_19 : ∀a.eqAsciiMin ch_I a = true → ch_I = a. intro; elim a 0; normalize; intro; try destruct H; reflexivity. qed.
lemma eqasciimin_to_eq_20 : ∀a.eqAsciiMin ch_J a = true → ch_J = a. intro; elim a 0; normalize; intro; try destruct H; reflexivity. qed.
lemma eqasciimin_to_eq_21 : ∀a.eqAsciiMin ch_K a = true → ch_K = a. intro; elim a 0; normalize; intro; try destruct H; reflexivity. qed.
lemma eqasciimin_to_eq_22 : ∀a.eqAsciiMin ch_L a = true → ch_L = a. intro; elim a 0; normalize; intro; try destruct H; reflexivity. qed.
lemma eqasciimin_to_eq_23 : ∀a.eqAsciiMin ch_M a = true → ch_M = a. intro; elim a 0; normalize; intro; try destruct H; reflexivity. qed.
lemma eqasciimin_to_eq_24 : ∀a.eqAsciiMin ch_N a = true → ch_N = a. intro; elim a 0; normalize; intro; try destruct H; reflexivity. qed.
lemma eqasciimin_to_eq_25 : ∀a.eqAsciiMin ch_O a = true → ch_O = a. intro; elim a 0; normalize; intro; try destruct H; reflexivity. qed.
lemma eqasciimin_to_eq_26 : ∀a.eqAsciiMin ch_P a = true → ch_P = a. intro; elim a 0; normalize; intro; try destruct H; reflexivity. qed.
lemma eqasciimin_to_eq_27 : ∀a.eqAsciiMin ch_Q a = true → ch_Q = a. intro; elim a 0; normalize; intro; try destruct H; reflexivity. qed.
lemma eqasciimin_to_eq_28 : ∀a.eqAsciiMin ch_R a = true → ch_R = a. intro; elim a 0; normalize; intro; try destruct H; reflexivity. qed.
lemma eqasciimin_to_eq_29 : ∀a.eqAsciiMin ch_S a = true → ch_S = a. intro; elim a 0; normalize; intro; try destruct H; reflexivity. qed.
lemma eqasciimin_to_eq_30 : ∀a.eqAsciiMin ch_T a = true → ch_T = a. intro; elim a 0; normalize; intro; try destruct H; reflexivity. qed.
lemma eqasciimin_to_eq_31 : ∀a.eqAsciiMin ch_U a = true → ch_U = a. intro; elim a 0; normalize; intro; try destruct H; reflexivity. qed.
lemma eqasciimin_to_eq_32 : ∀a.eqAsciiMin ch_V a = true → ch_V = a. intro; elim a 0; normalize; intro; try destruct H; reflexivity. qed.
lemma eqasciimin_to_eq_33 : ∀a.eqAsciiMin ch_W a = true → ch_W = a. intro; elim a 0; normalize; intro; try destruct H; reflexivity. qed.
lemma eqasciimin_to_eq_34 : ∀a.eqAsciiMin ch_X a = true → ch_X = a. intro; elim a 0; normalize; intro; try destruct H; reflexivity. qed.
lemma eqasciimin_to_eq_35 : ∀a.eqAsciiMin ch_Y a = true → ch_Y = a. intro; elim a 0; normalize; intro; try destruct H; reflexivity. qed.
lemma eqasciimin_to_eq_36 : ∀a.eqAsciiMin ch_Z a = true → ch_Z = a. intro; elim a 0; normalize; intro; try destruct H; reflexivity. qed.
lemma eqasciimin_to_eq_37 : ∀a.eqAsciiMin ch_a a = true → ch_a = a. intro; elim a 0; normalize; intro; try destruct H; reflexivity. qed.
lemma eqasciimin_to_eq_38 : ∀a.eqAsciiMin ch_b a = true → ch_b = a. intro; elim a 0; normalize; intro; try destruct H; reflexivity. qed.
lemma eqasciimin_to_eq_39 : ∀a.eqAsciiMin ch_c a = true → ch_c = a. intro; elim a 0; normalize; intro; try destruct H; reflexivity. qed.
lemma eqasciimin_to_eq_40 : ∀a.eqAsciiMin ch_d a = true → ch_d = a. intro; elim a 0; normalize; intro; try destruct H; reflexivity. qed.
lemma eqasciimin_to_eq_41 : ∀a.eqAsciiMin ch_e a = true → ch_e = a. intro; elim a 0; normalize; intro; try destruct H; reflexivity. qed.
lemma eqasciimin_to_eq_42 : ∀a.eqAsciiMin ch_f a = true → ch_f = a. intro; elim a 0; normalize; intro; try destruct H; reflexivity. qed.
lemma eqasciimin_to_eq_43 : ∀a.eqAsciiMin ch_g a = true → ch_g = a. intro; elim a 0; normalize; intro; try destruct H; reflexivity. qed.
lemma eqasciimin_to_eq_44 : ∀a.eqAsciiMin ch_h a = true → ch_h = a. intro; elim a 0; normalize; intro; try destruct H; reflexivity. qed.
lemma eqasciimin_to_eq_45 : ∀a.eqAsciiMin ch_i a = true → ch_i = a. intro; elim a 0; normalize; intro; try destruct H; reflexivity. qed.
lemma eqasciimin_to_eq_46 : ∀a.eqAsciiMin ch_j a = true → ch_j = a. intro; elim a 0; normalize; intro; try destruct H; reflexivity. qed.
lemma eqasciimin_to_eq_47 : ∀a.eqAsciiMin ch_k a = true → ch_k = a. intro; elim a 0; normalize; intro; try destruct H; reflexivity. qed.
lemma eqasciimin_to_eq_48 : ∀a.eqAsciiMin ch_l a = true → ch_l = a. intro; elim a 0; normalize; intro; try destruct H; reflexivity. qed.
lemma eqasciimin_to_eq_49 : ∀a.eqAsciiMin ch_m a = true → ch_m = a. intro; elim a 0; normalize; intro; try destruct H; reflexivity. qed.
lemma eqasciimin_to_eq_50 : ∀a.eqAsciiMin ch_n a = true → ch_n = a. intro; elim a 0; normalize; intro; try destruct H; reflexivity. qed.
lemma eqasciimin_to_eq_51 : ∀a.eqAsciiMin ch_o a = true → ch_o = a. intro; elim a 0; normalize; intro; try destruct H; reflexivity. qed.
lemma eqasciimin_to_eq_52 : ∀a.eqAsciiMin ch_p a = true → ch_p = a. intro; elim a 0; normalize; intro; try destruct H; reflexivity. qed.
lemma eqasciimin_to_eq_53 : ∀a.eqAsciiMin ch_q a = true → ch_q = a. intro; elim a 0; normalize; intro; try destruct H; reflexivity. qed.
lemma eqasciimin_to_eq_54 : ∀a.eqAsciiMin ch_r a = true → ch_r = a. intro; elim a 0; normalize; intro; try destruct H; reflexivity. qed.
lemma eqasciimin_to_eq_55 : ∀a.eqAsciiMin ch_s a = true → ch_s = a. intro; elim a 0; normalize; intro; try destruct H; reflexivity. qed.
lemma eqasciimin_to_eq_56 : ∀a.eqAsciiMin ch_t a = true → ch_t = a. intro; elim a 0; normalize; intro; try destruct H; reflexivity. qed.
lemma eqasciimin_to_eq_57 : ∀a.eqAsciiMin ch_u a = true → ch_u = a. intro; elim a 0; normalize; intro; try destruct H; reflexivity. qed.
lemma eqasciimin_to_eq_58 : ∀a.eqAsciiMin ch_v a = true → ch_v = a. intro; elim a 0; normalize; intro; try destruct H; reflexivity. qed.
lemma eqasciimin_to_eq_59 : ∀a.eqAsciiMin ch_w a = true → ch_w = a. intro; elim a 0; normalize; intro; try destruct H; reflexivity. qed.
lemma eqasciimin_to_eq_60 : ∀a.eqAsciiMin ch_x a = true → ch_x = a. intro; elim a 0; normalize; intro; try destruct H; reflexivity. qed.
lemma eqasciimin_to_eq_61 : ∀a.eqAsciiMin ch_y a = true → ch_y = a. intro; elim a 0; normalize; intro; try destruct H; reflexivity. qed.
lemma eqasciimin_to_eq_62 : ∀a.eqAsciiMin ch_z a = true → ch_z = a. intro; elim a 0; normalize; intro; try destruct H; reflexivity. qed.

lemma eqasciimin_to_eq : ∀a1.∀a2.eqAsciiMin a1 a2 = true → a1 = a2.
 do 1 intro;
 elim a1 0;
 [  1: apply eqasciimin_to_eq_00 |  2: apply eqasciimin_to_eq_01 |  3: apply eqasciimin_to_eq_02 |  4: apply eqasciimin_to_eq_03
 |  5: apply eqasciimin_to_eq_04 |  6: apply eqasciimin_to_eq_05 |  7: apply eqasciimin_to_eq_06 |  8: apply eqasciimin_to_eq_07
 |  9: apply eqasciimin_to_eq_08 | 10: apply eqasciimin_to_eq_09 | 11: apply eqasciimin_to_eq_10 | 12: apply eqasciimin_to_eq_11
 | 13: apply eqasciimin_to_eq_12 | 14: apply eqasciimin_to_eq_13 | 15: apply eqasciimin_to_eq_14 | 16: apply eqasciimin_to_eq_15
 | 17: apply eqasciimin_to_eq_16 | 18: apply eqasciimin_to_eq_17 | 19: apply eqasciimin_to_eq_18 | 20: apply eqasciimin_to_eq_19
 | 21: apply eqasciimin_to_eq_20 | 22: apply eqasciimin_to_eq_21 | 23: apply eqasciimin_to_eq_22 | 24: apply eqasciimin_to_eq_23
 | 25: apply eqasciimin_to_eq_24 | 26: apply eqasciimin_to_eq_25 | 27: apply eqasciimin_to_eq_26 | 28: apply eqasciimin_to_eq_27
 | 29: apply eqasciimin_to_eq_28 | 30: apply eqasciimin_to_eq_29 | 31: apply eqasciimin_to_eq_30 | 32: apply eqasciimin_to_eq_31
 | 33: apply eqasciimin_to_eq_32 | 34: apply eqasciimin_to_eq_33 | 35: apply eqasciimin_to_eq_34 | 36: apply eqasciimin_to_eq_35
 | 37: apply eqasciimin_to_eq_36 | 38: apply eqasciimin_to_eq_37 | 39: apply eqasciimin_to_eq_38 | 40: apply eqasciimin_to_eq_39
 | 41: apply eqasciimin_to_eq_40 | 42: apply eqasciimin_to_eq_41 | 43: apply eqasciimin_to_eq_42 | 44: apply eqasciimin_to_eq_43
 | 45: apply eqasciimin_to_eq_44 | 46: apply eqasciimin_to_eq_45 | 47: apply eqasciimin_to_eq_46 | 48: apply eqasciimin_to_eq_47
 | 49: apply eqasciimin_to_eq_48 | 50: apply eqasciimin_to_eq_49 | 51: apply eqasciimin_to_eq_50 | 52: apply eqasciimin_to_eq_51
 | 53: apply eqasciimin_to_eq_52 | 54: apply eqasciimin_to_eq_53 | 55: apply eqasciimin_to_eq_54 | 56: apply eqasciimin_to_eq_55
 | 57: apply eqasciimin_to_eq_56 | 58: apply eqasciimin_to_eq_57 | 59: apply eqasciimin_to_eq_58 | 60: apply eqasciimin_to_eq_59
 | 61: apply eqasciimin_to_eq_60 | 62: apply eqasciimin_to_eq_61 | 63: apply eqasciimin_to_eq_62 ].
qed.
