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

notation > "hvbox( a break = opt ( ❪ term 19 S ❫ break ) b)" 
  non associative with precedence 45
  for @{ 'eq ${default @{$S}@{?}} $a $b }.

notation < "hvbox(term 46 a break maction (=) (=\sub t) term 46 b)" 
  non associative with precedence 45
  for @{ 'eq $t $a $b }.
