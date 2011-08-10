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

include "Basic-2/syntax/term.ma".

(* LOCAL ENVIRONMENTS *******************************************************)

(* local environments *)
inductive lenv: Type[0] ≝
| LSort: lenv                       (* empty *)
| LPair: lenv → bind2 → term → lenv (* binary binding construction *)
.

interpretation "sort (local environment)" 'Star = LSort.

interpretation "environment binding construction (binary)" 'DBind L I T = (LPair L I T).
