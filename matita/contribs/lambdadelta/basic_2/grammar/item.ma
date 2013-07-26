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

include "ground_2/arith.ma".

(* ITEMS ********************************************************************)

(* atomic items *)
inductive item0: Type[0] ≝
   | Sort: nat → item0 (* sort: starting at 0 *)
   | LRef: nat → item0 (* reference by index: starting at 0 *)
   | GRef: nat → item0 (* reference by position: starting at 0 *)
.

(* binary binding items *)
inductive bind2: Type[0] ≝
  | Abbr: bind2 (* abbreviation *)
  | Abst: bind2 (* abstraction *)
.

(* binary non-binding items *)
inductive flat2: Type[0] ≝
  | Appl: flat2 (* application *)
  | Cast: flat2 (* explicit type annotation *)
.

(* binary items *)
inductive item2: Type[0] ≝
  | Bind2: bool → bind2 → item2 (* polarized binding item *)
  | Flat2: flat2 → item2        (* non-binding item *)
.

(* Basic properties *********************************************************)

axiom item0_eq_dec: ∀I1,I2:item0. Decidable (I1 = I2).

(* Basic_1: was: bind_dec *)
axiom bind2_eq_dec: ∀I1,I2:bind2. Decidable (I1 = I2).

(* Basic_1: was: flat_dec *)
axiom flat2_eq_dec: ∀I1,I2:flat2. Decidable (I1 = I2).

(* Basic_1: was: kind_dec *)
axiom item2_eq_dec: ∀I1,I2:item2. Decidable (I1 = I2).

(* Basic_1: removed theorems 21:
            s_S s_plus s_plus_sym s_minus minus_s_s s_le s_lt s_inj s_inc
            s_arith0 s_arith1
            r_S r_plus r_plus_sym r_minus r_dis s_r r_arith0 r_arith1
            not_abbr_abst bind_dec_not
*)
