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

include "num/oct.ma".
include "num/bitrigesim.ma".

(* ********************************************** *)
(* MATTONI BASE PER DEFINIRE LE TABELLE DELLE MCU *)
(* ********************************************** *)

(* enumerazione delle modalita' di indirizzamento = caricamento degli operandi *)
ninductive IP2022_instr_mode: Type ≝
  (* nessun operando : formato xxxxxxxx xxxxxxxx *)
  MODE_INH  : IP2022_instr_mode
  (* operando implicito [ADDR] : formato xxxxxxxx xxxxxxxx *)
| MODE_INHADDR : IP2022_instr_mode
  (* operando implicito [ADDR]/ADDR+=2 : formato xxxxxxxx xxxxxxxx *)
| MODE_INHADDRpp : IP2022_instr_mode

  (* #lit3 → / : formato xxxxxxxx xxxxxkkk *)
| MODE_IMM3 : oct → IP2022_instr_mode
  (* W, #lit8 → W : formato xxxxxxxx kkkkkkkk [load 1 byte arg] *)
| MODE_IMM8 : IP2022_instr_mode
  (* #lit13 → / : formato xxxkkkkk kkkkkkkk [load 1 byte arg] *)
| MODE_IMM13 : bitrigesim → IP2022_instr_mode

  (* FR, W → FR : formato xxxxxxx0 ffffffff [load 1 byte arg] *)
| MODE_FR0_and_W : IP2022_instr_mode
  (* FR, W → FR : formato xxxxxxx1 ffffffff [load 1 byte arg] *)
| MODE_FR1_and_W : IP2022_instr_mode
  (* W, FR → W : formato xxxxxxx0 ffffffff [load 1 byte arg] *)
| MODE_W_and_FR0 : IP2022_instr_mode
  (* W, FR → W : formato xxxxxxx1 ffffffff [load 1 byte arg] *)
| MODE_W_and_FR1 : IP2022_instr_mode

  (* FR(bitN) → FR(bitN) : formato xxxxbbb0 ffffffff [load 1 byte arg] *)
| MODE_FR0n : oct → IP2022_instr_mode
  (* FR(bitN) → FR(bitN) : formato xxxxbbb1 ffffffff [load 1 byte arg] *)
| MODE_FR1n : oct → IP2022_instr_mode
.

ndefinition eq_IP2022_im ≝
λi1,i2:IP2022_instr_mode.
 match i1 with
  [ MODE_INH ⇒ match i2 with [ MODE_INH ⇒ true | _ ⇒ false ]
  | MODE_INHADDR ⇒ match i2 with [ MODE_INHADDR ⇒ true | _ ⇒ false ]
  | MODE_INHADDRpp ⇒ match i2 with [ MODE_INHADDRpp ⇒ true | _ ⇒ false ]
  | MODE_IMM3 o1 ⇒ match i2 with [ MODE_IMM3 o2 ⇒ eqc ? o1 o2 | _ ⇒ false ]
  | MODE_IMM8 ⇒ match i2 with [ MODE_IMM8 ⇒ true | _ ⇒ false ]
  | MODE_IMM13 t1 ⇒ match i2 with [ MODE_IMM13 t2 ⇒ eqc ? t1 t2 | _ ⇒ false ]
  | MODE_FR0_and_W ⇒ match i2 with [ MODE_FR0_and_W ⇒ true | _ ⇒ false ]
  | MODE_FR1_and_W ⇒ match i2 with [ MODE_FR1_and_W ⇒ true | _ ⇒ false ]
  | MODE_W_and_FR0 ⇒ match i2 with [ MODE_W_and_FR0 ⇒ true | _ ⇒ false ]
  | MODE_W_and_FR1 ⇒ match i2 with [ MODE_W_and_FR1 ⇒ true | _ ⇒ false ]
  | MODE_FR0n o1 ⇒ match i2 with [ MODE_FR0n o2 ⇒ eqc ? o1 o2 | _ ⇒ false ]
  | MODE_FR1n o1 ⇒ match i2 with [ MODE_FR1n o2 ⇒ eqc ? o1 o2 | _ ⇒ false ]
  ].

ndefinition forall_IP2022_im ≝ λP:IP2022_instr_mode → bool.
  P MODE_INH
⊗ P MODE_INHADDR
⊗ P MODE_INHADDRpp
⊗ forallc ? (λo.P (MODE_IMM3 o))
⊗ P MODE_IMM8
⊗ forallc ? (λt.P (MODE_IMM13 t))
⊗ P MODE_FR0_and_W
⊗ P MODE_FR1_and_W
⊗ P MODE_W_and_FR0
⊗ P MODE_W_and_FR1
⊗ forallc ? (λo.P (MODE_FR0n o))
⊗ forallc ? (λo.P (MODE_FR1n o)).
