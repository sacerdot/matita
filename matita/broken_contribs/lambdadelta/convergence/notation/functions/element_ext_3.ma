(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2
*)

(* NOTATION FOR CONVERGENCE *************************************************)

notation < "hvbox( 𝗲𝘅𝘁 break term 70 f )"
  non associative with precedence 70
  for @{ 'ElementExt $A1 $A0 $f }.

notation > "hvbox( 𝗲𝘅𝘁❪ break term 46 A1, break term 46 A0 ❫ break term 70 f )"
  non associative with precedence 70
  for @{ 'ElementExt $A1 $A0 $f }.

notation > "hvbox( 𝗲𝘅𝘁 break term 70 f )"
  non associative with precedence 70
  for @{ 'ElementExt ? ? $f }.
