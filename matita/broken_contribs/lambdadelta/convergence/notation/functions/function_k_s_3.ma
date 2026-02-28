(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2
*)

(* NOTATION FOR CONVERGENCE *************************************************)

notation < "hvbox( 𝗞𝗌 break term 70 y )"
  non associative with precedence 70
  for @{ 'FunctionK_s $X $Y $y }.

notation > "hvbox( 𝗞𝗌❪ break term 46 X, break term 46 Y ❫ break term 70 y )"
  non associative with precedence 70
  for @{ 'FunctionK_s $X $Y $y }.

notation > "hvbox( 𝗞𝗌 break term 70 y )"
  non associative with precedence 70
  for @{ 'FunctionK_s ? ? $y }.
