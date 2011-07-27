(*
    ||M||  This file is part of HELM, an Hypertextual, Electronic
    ||A||  Library of Mathematics, developed at the Computer Science
    ||T||  Department of the University of Bologna, Italy.
    ||I||
    ||T||
    ||A||  This file is distributed under the terms of the
    \   /  GNU General Public License Version 2
     \ /
      V_______________________________________________________________ *)

(* THE FORMAL SYSTEM λδ - MATITA SOURCE SCRIPTS 
 * Specification started: 2011 April 17
 * - Patience on me so that I gain peace and perfection! -
 * [ suggested invocation to start formal specifications with ]
 *)

include "lambda-delta/ground.ma".
include "lambda-delta/xoa_defs.ma".
include "lambda-delta/xoa_notation.ma".
include "lambda-delta/notation.ma".

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
