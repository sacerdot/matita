 (*
    ||M||  This file is part of HELM, an Hypertextual, Electronic        
    ||A||  Library of Mathematics, developed at the Computer Science     
    ||T||  Department of the University of Bologna, Italy.                     
    ||I||                                                                 
    ||T||  
    ||A||  
    \   /  This file is distributed under the terms of the       
     \ /   GNU General Public License Version 2   
      V_______________________________________________________________ *)

universe constraint Type[U] < Type[U].

include "basics/logic.ma".

definition EQ: ∀A:Type[0]. A → A → Prop ≝ λA,x,y.
               ∀P:A→Prop. P x → P y.

lemma pippo1: ∀A,x,y. x = y → EQ A x y.
#A #x #y #H destruct //
qed.

lemma pippo2: ∀A,x,y. EQ A x y → x = y.
/2 width=1/ qed.
