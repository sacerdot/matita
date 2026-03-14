(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2
*)

(* NOTATION FOR CONVERGENCE *************************************************)

notation < "hvbox( 𝗜𝗌 )"
  non associative with precedence 70
  for @{ 'FunctionI_s $X }.

notation > "hvbox( 𝗜𝗌 opt ( ❪ break term 46 X ❫ ) )"
  non associative with precedence 70
  for @{ 'FunctionI_s ${default @{$X}@{?}} }.
