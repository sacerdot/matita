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

include "lambda-delta/substitution/subst.ma".

(* THINNING *****************************************************************)

inductive thin: lenv → nat → nat → lenv → Prop ≝
   | thin_refl: ∀L. thin L 0 0 L
   | thin_thin: ∀L1,L2,I,V,e.
                thin L1 0 e L2 → thin (L1. ♭I V) 0 (e + 1) L2
   | thin_skip: ∀L1,L2,I,V1,V2,d,e.
                thin L1 d e L2 → [d,e]← L1 / V1 ≡ V2 → 
                thin (L1. ♭I V1) (d + 1) e (L2. ♭I V2)
.

interpretation "thinning" 'RThin L1 d e L2 = (thin L1 d e L2).
