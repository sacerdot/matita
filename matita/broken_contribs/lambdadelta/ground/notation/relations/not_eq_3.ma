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

notation > "hvbox( a ⧸= opt ( { break term 46 S } ) break b )"
  non associative with precedence 45
  for @{ 'NotEq ${default @{$S}@{?}} $a $b }.

notation < "hvbox( term 46 a ⧸= break term 46 b )"
  non associative with precedence 45
  for @{ 'NotEq $S $a $b }.
