(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2
*)

(* NOTATION FOR CONVERGENCE *************************************************)

notation < "hvbox( 𝗱＠❨ break term 46 i ❩ )"
  non associative with precedence 70
  for @{ 'ElementD $X $D $i }.

notation > "hvbox( 𝗱＠ opt ( ❪ break term 46 X ❫ ) opt ( [ break term 46 D ] ) ❨ break term 46 i ❩ )"
  non associative with precedence 70
  for @{ 'ElementD ${default @{$X}@{?}} ${default @{$D}@{?}} $i }.
