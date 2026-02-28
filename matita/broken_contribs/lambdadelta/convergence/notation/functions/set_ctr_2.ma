(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2
*)

(* NOTATION FOR CONVERGENCE *************************************************)

notation < "hvbox( 𝗖𝘁𝗿 break term 70 D )"
  non associative with precedence 70
  for @{ 'SetCTR $X $D }.

notation > "hvbox( 𝗖𝘁𝗿 opt ( ❪ break term 46 X ❫ ) break term 70 D )"
  non associative with precedence 70
  for @{ 'SetCTR ${default @{$X}@{?}} $D }.
