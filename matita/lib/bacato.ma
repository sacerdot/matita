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

include "basics/pts.ma".

inductive ex3_2 (A0,A1:Type[0]) (P0,P1,P2:A0→A1→Prop) : Prop ≝
   | ex3_2_intro: ∀x0,x1. (P0 x0 x1)→(P1 x0 x1)→(P2 x0 x1)→(ex3_2 ? ? ? ? ?).

lemma bacato: ∀A0,A1:Type[0]. ∀P0,P1,P2:A0→A1→Prop. ∀x0,x1.
              P0 x0 x1 → P1 x0 x1 → P2 x0 x1 →
              ex3_2 … (λx0,x1. P0 x0 x1) (λx0,x1. P1 x0 x1) (λx0,x1. P2 x0 x1).
#A0 #A1 #P0 #P1 #P2 #x0 #x1 #H0 #H1 #H2
@ex3_2_intro //
