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

include "lambda-delta/language/term.ma".

(* LOCAL ENVIRONMENTS *******************************************************)

(* local environments *)
inductive lenv: Type[0] ≝
   | LSort: lenv                       (* empty *)
   | LCon2: lenv → item2 → term → lenv (* binary item construction *)
.

interpretation "sort (local environment)" 'Star = LSort.

interpretation "environment construction (binary)" 'DCon L I T = (LCon2 L I T).
