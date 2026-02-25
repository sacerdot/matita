(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2
*)

(* NOTATION FOR LIMITS ******************************************************)

notation < "hvbox( 𝗶[ break term 46 D ] )"
  non associative with precedence 70
  for @{ 'ElementI $X $D }.

notation > "hvbox( 𝗶 opt ( ❪ break term 46 X ❫ ) opt ( [ break term 46 D ] ) )"
  non associative with precedence 70
  for @{ 'ElementI ${default @{$X}@{?}} ${default @{$D}@{?}} }.
