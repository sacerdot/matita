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

include "lambda-delta/syntax/lenv.ma".

(* WEIGHTS ******************************************************************)

(* the weight of a term *)
let rec tw T ≝ match T with
[ TSort _     ⇒ 1
| TLRef _     ⇒ 1
| TPair _ V T ⇒ tw V + tw T + 1
].

interpretation "weight (term)" 'Weight T = (tw T).

(* the weight of a local environment *)
let rec lw L ≝ match L with
[ LSort       ⇒ 0
| LPair L _ V ⇒ lw L + #V
].

interpretation "weight (local environment)" 'Weight L = (lw L).

(* the weight of a closure *)
definition cw: lenv → term → ? ≝ λL,T. #L + #T.

interpretation "weight (closure)" 'Weight L T = (cw L T).

axiom cw_wf_ind: ∀P:lenv→term→Prop.
                 (∀L2,T2. (∀L1,T1. #[L1,T1] < #[L2,T2] → P L1 T1) → P L2 T2) →
                 ∀L,T. P L T.
