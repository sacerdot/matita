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

notation < "term 76 a \sup term 90 b" non associative with precedence 75 for @{ 'exp $a $b}.
notation > "a \sup term 90 b" non associative with precedence 75 for @{ 'exp $a $b}.
notation > "a ^ term 90 b"  non associative with precedence 75 for @{ 'exp $a $b}.
