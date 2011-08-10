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

include "Basic-2/syntax/lenv.ma".

(* LENGTH *******************************************************************)

(* the length of a local environment *)
let rec length L ≝ match L with
[ LSort       ⇒ 0
| LPair L _ _ ⇒ length L + 1
].

interpretation "length (local environment)" 'card L = (length L).
