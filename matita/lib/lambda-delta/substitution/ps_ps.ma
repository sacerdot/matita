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

include "lambda-delta/substitution/ps_defs.ma".

(* PARALLEL SUBSTITUTION ****************************************************)

axiom ps_conf: ∀L,T0,d,e,T1. L ⊢ T0 [d, e] ≫ T1 → ∀T2. L ⊢ T0 [d, e] ≫ T2 →
                 ∃∃T. L ⊢ T1 [d, e] ≫ T & L ⊢ T2 [d, e] ≫ T.
