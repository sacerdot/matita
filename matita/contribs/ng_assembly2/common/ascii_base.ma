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
(*                          Progetto FreeScale                            *)
(*                                                                        *)
(*   Sviluppato da: Ing. Cosimo Oliboni, oliboni@cs.unibo.it              *)
(*   Sviluppo: 2008-2010                                                  *)
(*                                                                        *)
(* ********************************************************************** *)

include "num/bool.ma".

(* ************************** *)
(* DEFINIZIONE ASCII MINIMALE *)
(* ************************** *)

ninductive ascii : Type ≝
(* numeri *)  
  ch_0: ascii
| ch_1: ascii
| ch_2: ascii
| ch_3: ascii
| ch_4: ascii
| ch_5: ascii
| ch_6: ascii
| ch_7: ascii
| ch_8: ascii
| ch_9: ascii

(* simboli *)
| ch__: ascii

(* maiuscole *)
| ch_A: ascii
| ch_B: ascii
| ch_C: ascii
| ch_D: ascii
| ch_E: ascii
| ch_F: ascii
| ch_G: ascii
| ch_H: ascii
| ch_I: ascii
| ch_J: ascii
| ch_K: ascii
| ch_L: ascii
| ch_M: ascii
| ch_N: ascii
| ch_O: ascii
| ch_P: ascii
| ch_Q: ascii
| ch_R: ascii
| ch_S: ascii
| ch_T: ascii
| ch_U: ascii
| ch_V: ascii
| ch_W: ascii
| ch_X: ascii
| ch_Y: ascii
| ch_Z: ascii

(* minuscole *)
| ch_a: ascii
| ch_b: ascii
| ch_c: ascii
| ch_d: ascii
| ch_e: ascii
| ch_f: ascii
| ch_g: ascii
| ch_h: ascii
| ch_i: ascii
| ch_j: ascii
| ch_k: ascii
| ch_l: ascii
| ch_m: ascii
| ch_n: ascii
| ch_o: ascii
| ch_p: ascii
| ch_q: ascii
| ch_r: ascii
| ch_s: ascii
| ch_t: ascii
| ch_u: ascii
| ch_v: ascii
| ch_w: ascii
| ch_x: ascii
| ch_y: ascii
| ch_z: ascii.

(* iteratore sugli ascii *)
ndefinition forall_ascii ≝ λP.
 P ch_0 ⊗ P ch_1 ⊗ P ch_2 ⊗ P ch_3 ⊗ P ch_4 ⊗ P ch_5 ⊗ P ch_6 ⊗ P ch_7 ⊗
 P ch_8 ⊗ P ch_9 ⊗ P ch__ ⊗ P ch_A ⊗ P ch_B ⊗ P ch_C ⊗ P ch_D ⊗ P ch_E ⊗
 P ch_F ⊗ P ch_G ⊗ P ch_H ⊗ P ch_I ⊗ P ch_J ⊗ P ch_K ⊗ P ch_L ⊗ P ch_M ⊗
 P ch_N ⊗ P ch_O ⊗ P ch_P ⊗ P ch_Q ⊗ P ch_R ⊗ P ch_S ⊗ P ch_T ⊗ P ch_U ⊗
 P ch_V ⊗ P ch_W ⊗ P ch_X ⊗ P ch_Y ⊗ P ch_Z ⊗ P ch_a ⊗ P ch_b ⊗ P ch_c ⊗
 P ch_d ⊗ P ch_e ⊗ P ch_f ⊗ P ch_g ⊗ P ch_h ⊗ P ch_i ⊗ P ch_j ⊗ P ch_k ⊗
 P ch_l ⊗ P ch_m ⊗ P ch_n ⊗ P ch_o ⊗ P ch_p ⊗ P ch_q ⊗ P ch_r ⊗ P ch_s ⊗
 P ch_t ⊗ P ch_u ⊗ P ch_v ⊗ P ch_w ⊗ P ch_x ⊗ P ch_y ⊗ P ch_z.

(* confronto fra ascii *)
ndefinition eq_ascii ≝
λc,c':ascii.match c with
 [ ch_0 ⇒ match c' with [ ch_0 ⇒ true | _ ⇒ false ] | ch_1 ⇒ match c' with [ ch_1 ⇒ true | _ ⇒ false ]
 | ch_2 ⇒ match c' with [ ch_2 ⇒ true | _ ⇒ false ] | ch_3 ⇒ match c' with [ ch_3 ⇒ true | _ ⇒ false ]
 | ch_4 ⇒ match c' with [ ch_4 ⇒ true | _ ⇒ false ] | ch_5 ⇒ match c' with [ ch_5 ⇒ true | _ ⇒ false ]
 | ch_6 ⇒ match c' with [ ch_6 ⇒ true | _ ⇒ false ] | ch_7 ⇒ match c' with [ ch_7 ⇒ true | _ ⇒ false ]
 | ch_8 ⇒ match c' with [ ch_8 ⇒ true | _ ⇒ false ] | ch_9 ⇒ match c' with [ ch_9 ⇒ true | _ ⇒ false ]
 | ch__ ⇒ match c' with [ ch__ ⇒ true | _ ⇒ false ] | ch_A ⇒ match c' with [ ch_A ⇒ true | _ ⇒ false ]
 | ch_B ⇒ match c' with [ ch_B ⇒ true | _ ⇒ false ] | ch_C ⇒ match c' with [ ch_C ⇒ true | _ ⇒ false ]
 | ch_D ⇒ match c' with [ ch_D ⇒ true | _ ⇒ false ] | ch_E ⇒ match c' with [ ch_E ⇒ true | _ ⇒ false ]
 | ch_F ⇒ match c' with [ ch_F ⇒ true | _ ⇒ false ] | ch_G ⇒ match c' with [ ch_G ⇒ true | _ ⇒ false ]
 | ch_H ⇒ match c' with [ ch_H ⇒ true | _ ⇒ false ] | ch_I ⇒ match c' with [ ch_I ⇒ true | _ ⇒ false ]
 | ch_J ⇒ match c' with [ ch_J ⇒ true | _ ⇒ false ] | ch_K ⇒ match c' with [ ch_K ⇒ true | _ ⇒ false ]
 | ch_L ⇒ match c' with [ ch_L ⇒ true | _ ⇒ false ] | ch_M ⇒ match c' with [ ch_M ⇒ true | _ ⇒ false ]
 | ch_N ⇒ match c' with [ ch_N ⇒ true | _ ⇒ false ] | ch_O ⇒ match c' with [ ch_O ⇒ true | _ ⇒ false ]
 | ch_P ⇒ match c' with [ ch_P ⇒ true | _ ⇒ false ] | ch_Q ⇒ match c' with [ ch_Q ⇒ true | _ ⇒ false ]
 | ch_R ⇒ match c' with [ ch_R ⇒ true | _ ⇒ false ] | ch_S ⇒ match c' with [ ch_S ⇒ true | _ ⇒ false ]
 | ch_T ⇒ match c' with [ ch_T ⇒ true | _ ⇒ false ] | ch_U ⇒ match c' with [ ch_U ⇒ true | _ ⇒ false ]
 | ch_V ⇒ match c' with [ ch_V ⇒ true | _ ⇒ false ] | ch_W ⇒ match c' with [ ch_W ⇒ true | _ ⇒ false ]
 | ch_X ⇒ match c' with [ ch_X ⇒ true | _ ⇒ false ] | ch_Y ⇒ match c' with [ ch_Y ⇒ true | _ ⇒ false ]
 | ch_Z ⇒ match c' with [ ch_Z ⇒ true | _ ⇒ false ] | ch_a ⇒ match c' with [ ch_a ⇒ true | _ ⇒ false ]
 | ch_b ⇒ match c' with [ ch_b ⇒ true | _ ⇒ false ] | ch_c ⇒ match c' with [ ch_c ⇒ true | _ ⇒ false ]
 | ch_d ⇒ match c' with [ ch_d ⇒ true | _ ⇒ false ] | ch_e ⇒ match c' with [ ch_e ⇒ true | _ ⇒ false ]
 | ch_f ⇒ match c' with [ ch_f ⇒ true | _ ⇒ false ] | ch_g ⇒ match c' with [ ch_g ⇒ true | _ ⇒ false ]
 | ch_h ⇒ match c' with [ ch_h ⇒ true | _ ⇒ false ] | ch_i ⇒ match c' with [ ch_i ⇒ true | _ ⇒ false ]
 | ch_j ⇒ match c' with [ ch_j ⇒ true | _ ⇒ false ] | ch_k ⇒ match c' with [ ch_k ⇒ true | _ ⇒ false ]
 | ch_l ⇒ match c' with [ ch_l ⇒ true | _ ⇒ false ] | ch_m ⇒ match c' with [ ch_m ⇒ true | _ ⇒ false ]
 | ch_n ⇒ match c' with [ ch_n ⇒ true | _ ⇒ false ] | ch_o ⇒ match c' with [ ch_o ⇒ true | _ ⇒ false ]
 | ch_p ⇒ match c' with [ ch_p ⇒ true | _ ⇒ false ] | ch_q ⇒ match c' with [ ch_q ⇒ true | _ ⇒ false ]
 | ch_r ⇒ match c' with [ ch_r ⇒ true | _ ⇒ false ] | ch_s ⇒ match c' with [ ch_s ⇒ true | _ ⇒ false ]
 | ch_t ⇒ match c' with [ ch_t ⇒ true | _ ⇒ false ] | ch_u ⇒ match c' with [ ch_u ⇒ true | _ ⇒ false ]
 | ch_v ⇒ match c' with [ ch_v ⇒ true | _ ⇒ false ] | ch_w ⇒ match c' with [ ch_w ⇒ true | _ ⇒ false ]
 | ch_x ⇒ match c' with [ ch_x ⇒ true | _ ⇒ false ] | ch_y ⇒ match c' with [ ch_y ⇒ true | _ ⇒ false ]
 | ch_z ⇒ match c' with [ ch_z ⇒ true | _ ⇒ false ]
 ].
