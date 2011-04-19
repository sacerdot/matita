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

include "lambda-delta/language/item2.ma".

(* TERMS ********************************************************************)

(* terms *)
inductive term: Type[0] ≝
   | TSort: nat → term                 (* sort: starting at 0 *)
   | TLRef: nat → term                 (* reference by index: starting at 0 *)
   | TCon2: item2 → term → term → term (* binary construction *)
.

interpretation "sort (term)" 'Star k = (TSort k).

interpretation "local reference (term)" 'Weight i = (TLRef i).

interpretation "term construction (binary)" 'SCon I T1 T2 = (TCon2 I T1 T2).
