(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2
*)

(* NOTATION FOR LIMITS ******************************************************)

notation < "hvbox( 𝗜𝗱𝘅❨ break term 46 D ❩ )"
  non associative with precedence 70
  for @{ 'SetIDX $X $D }.

notation > "hvbox( 𝗜𝗱𝘅 opt ( ❪ break term 46 X ❫ ) ❨ break term 46 D ❩ )"
  non associative with precedence 70
  for @{ 'SetIDX ${default @{$X}@{?}} $D }.
