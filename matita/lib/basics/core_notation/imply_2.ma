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

(* Core notation *******************************************************)

notation "hvbox(a break \to b)" 
  right associative with precedence 20
for @{ \forall $_:$a.$b }.

notation < "hvbox(a break \to b)" 
  right associative with precedence 20
for @{ \Pi $_:$a.$b }.
