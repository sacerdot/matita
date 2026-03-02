(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2
*)

(* NOTATION FOR CONVERGENCE *************************************************)

notation < "hvbox( D1 ⋢ break term 46 D2 )"
  non associative with precedence 45
  for @{ 'NotSqImageEq $X $D1 $D2 }.

notation > "hvbox( D1 ⋢ opt ( ❪ break term 46 X ❫ ) break term 46 D2 )"
  non associative with precedence 45
  for @{ 'NotSqImageEq ${default @{$X}@{?}} $D1 $D2 }.
