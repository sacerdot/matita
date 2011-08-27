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

(* THE FORMAL SYSTEM λδ - MATITA SOURCE SCRIPTS 
 * Specification started: 2011 April 17
 * - Patience on me so that I gain peace and perfection! -
 * [ suggested invocation to start formal specifications with ]
 *)

include "Ground-2/list.ma".
include "Basic-2/notation.ma".

(* BINARY ITEMS *************************************************************)

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
| Bind: bind2 → item2 (* binding item *)
| Flat: flat2 → item2 (* non-binding item *)
.

coercion item2_of_bind2: ∀I:bind2.item2 ≝ Bind on _I:bind2 to item2.

coercion item2_of_flat2: ∀I:flat2.item2 ≝ Flat on _I:flat2 to item2.

(* Basic-1: removed theorems 19:
            s_S s_plus s_plus_sym s_minus minus_s_s s_le s_lt s_inj s_inc
            s_arith0 s_arith1
            r_S r_plus r_plus_sym r_minus r_dis s_r r_arith0 r_arith1
*)
