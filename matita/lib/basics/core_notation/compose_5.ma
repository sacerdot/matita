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

notation > "hvbox( g break \circ opt ( { term 19 A, term 19 B, term 19 C } ) term 61 f )" 
  non associative with precedence 60
for @{ 'compose ${default @{$A}@{?}} ${default @{$B}@{?}} ${default @{$C}@{?}} $g $f }.

notation < "hvbox( g break \circ f )" 
  left associative with precedence 60
for @{ 'compose $A $B $C $g $f }.

