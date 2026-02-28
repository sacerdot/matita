(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2
*)

(* NOTATION FOR CONVERGENCE *************************************************)

notation > "hvbox( d1 ⧸≍𝘀 opt ( ❪ break term 46 D ❫ ) break term 46 d2 )"
  non associative with precedence 45
  for @{ 'NegEquivalent_s ${default @{$D}@{?}} $d1 $d2 }.
