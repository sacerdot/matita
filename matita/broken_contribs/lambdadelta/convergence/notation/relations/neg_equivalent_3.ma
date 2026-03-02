(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2
*)

(* NOTATION FOR CONVERGENCE *************************************************)

notation > "hvbox( x1 ⧸≍ opt ( ❪ break term 46 X ❫ ) break term 46 x2 )"
  non associative with precedence 45
  for @{ 'NegEquivalent ${default @{$X}@{?}} $x1 $x2 }.
