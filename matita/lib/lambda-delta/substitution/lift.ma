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

(* RELOCATION ***************************************************************)

inductive lift: term → nat → nat → term → Prop ≝
   | lift_sort   : ∀k,d,e. lift (⋆k) d e (⋆k)
   | lift_lref_lt: ∀i,d,e. i < d → lift (#i) d e (#i)
   | lift_lref_ge: ∀i,d,e. d ≤ i → lift (#i) d e (#(i + e))
   | lift_con2   : ∀I,V1,V2,T1,T2,d,e.
                   lift V1 d e V2 → lift T1 (d + 1) e T2 →
                   lift (♭I V1. T1) d e (♭I V2. T2)
.

interpretation "relocation" 'RLift T1 d e T2 = (lift T1 d e T2).

(* The basic inversion lemmas ***********************************************)

lemma lift_inv_sort2_aux: ∀d,e,T1,T2. ↑[d,e] T1 ≡ T2 → ∀k. T2 = ⋆k → T1 = ⋆k.
#d #e #T1 #T2 #H elim H -H d e T1 T2 //
   [ #i #d #e #_ #k #H destruct (***) (* DESTRUCT FAILS *)

lemma lift_inv_sort2: ∀d,e,T1,k. ↑[d,e] T1 ≡ ⋆k → T1 = ⋆k.
#d #e #T1 #k #H lapply (lift_inv_sort2_aux … H) /2/
qed.  
