(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2
*)

(* NOTATION FOR CONVERGENCE *************************************************)

notation < "hvbox( 𝔻𝗽 )"
  non associative with precedence 70
  for @{ 'CategoryD_p $S }.

notation > "hvbox( 𝔻𝗽 opt ( ❪ break term 46 S ❫ ) )"
  non associative with precedence 70
  for @{ 'CategoryD_p ${default @{$S}@{?}} }.
