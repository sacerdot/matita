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

notation > "x ⊩ y" with precedence 45 for @{'Vdash2 $x $y ?}.

notation > "x ⊩⎽ term 90 c y" with precedence 45 for @{'Vdash2 $x $y $c}.

notation "x (⊩ \sub term 90 c) y" with precedence 45 for @{'Vdash2 $x $y $c}.
