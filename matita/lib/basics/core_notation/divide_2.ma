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

notation < "a \frac b" 
  non associative with precedence 90
for @{ 'divide $a $b }.

notation "a \over b" 
  left associative with precedence 60
for @{ 'divide $a $b }.

notation "hvbox(a break / b)" 
  left associative with precedence 60
for @{ 'divide $a $b }.
