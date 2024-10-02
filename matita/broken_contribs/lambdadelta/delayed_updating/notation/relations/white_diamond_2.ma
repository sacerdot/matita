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

(* NOTATION FOR DELAYED UPDATING ********************************************)

notation "hvbox( ◇[ break term 46 t ]❨ break term 46 u ❩ )"
  non associative with precedence 45
  for @{ 'WhiteDiamond $t $u }.
