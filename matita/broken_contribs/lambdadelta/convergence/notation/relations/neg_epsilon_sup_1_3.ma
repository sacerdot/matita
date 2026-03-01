(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2
*)

(* NOTATION FOR CONVERGENCE *************************************************)

notation < "hvbox( a ⧸ϵ¹ break term 46 u )"
  non associative with precedence 45
  for @{ 'NegEpsilonSup1 $S $a $u }.

notation > "hvbox( a ⧸ϵ¹ opt ( ❪ break term 46 S ❫ ) break term 46 u )"
  non associative with precedence 45
  for @{ 'NegEpsilonSup1 ${default @{$S}@{?}} $a $u }.
