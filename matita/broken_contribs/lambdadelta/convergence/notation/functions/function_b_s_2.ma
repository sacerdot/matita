(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2
*)

(* NOTATION FOR CONVERGENCE *************************************************)

notation < "hvbox( 𝗕𝗌❨ break term 46 D ❩ )"
  non associative with precedence 69
  for @{ 'FunctionB_s $X $D }.

notation > "hvbox( 𝗕𝗌 opt ( ❪ break term 46 X ❫ ) ❨ break term 46 D ❩ )"
  non associative with precedence 69
  for @{ 'FunctionB_s ${default @{$X}@{?}} $D }.
