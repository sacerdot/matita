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

include "lambda-delta/ground.ma".

(* SORT HIERARCHY ***********************************************************)

(* sort hierarchy specifications *)
record sh: Type[0] ≝ {
   next: nat → nat;        (* next sort in the hierarchy *)
   next_lt: ∀k. k < next k (* strict monotonicity condition *)
}.
