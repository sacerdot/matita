(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2
*)

(* NOTATION FOR CONVERGENCE *************************************************)

notation < "hvbox( 𝔽𝗉 )"
  non associative with precedence 70
  for @{ 'CategoryF_p $X }.

notation > "hvbox( 𝔽𝗉 opt ( ❪ break term 46 X ❫ ) )"
  non associative with precedence 70
  for @{ 'CategoryF_p ${default @{$X}@{?}} }.
