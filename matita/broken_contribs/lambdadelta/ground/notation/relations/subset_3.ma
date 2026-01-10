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

(* NOTATION FOR GROUND ******************************************************)

notation < "hvbox( term 46 u1 ⊂ break term 46 u2 )"
  non associative with precedence 45
  for @{ 'Subset $S $u1 $u2 }.

notation > "hvbox( u1 ⊂ opt ( ❪ break term 46 S ❫ ) break term 46 u2 )"
  non associative with precedence 45
  for @{ 'Subset ${default @{$S}@{?}} $u1 $u2 }.
