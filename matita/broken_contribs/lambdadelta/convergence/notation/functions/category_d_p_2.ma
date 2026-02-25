(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2
*)

(* NOTATION FOR LIMITS ******************************************************)

notation < "hvbox( 𝔻𝗽❨ break term 46 D ❩ )"
  non associative with precedence 70
  for @{ 'CategoryD_p $S $D }.

notation > "hvbox( 𝔻𝗽 opt ( ❪ break term 46 S ❫ ) ❨ break term 46 D ❩ )"
  non associative with precedence 70
  for @{ 'CategoryD_p ${default @{$S}@{?}} $D }.
