(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2
*)

(* NOTATION FOR CONVERGENCE *************************************************)

notation < "hvbox( 𝝙𝗌[ break term 46 f ] ❨ break term 46 x ❩ )"
  non associative with precedence 69
  for @{ 'FunctionDelta_s $X $f $x }.

notation > "hvbox( 𝝙𝗌 opt ( ❪ break term 46 X ❫ ) [ break term 46 f ] ❨ break term 46 x ❩ )"
  non associative with precedence 69
  for @{ 'FunctionDelta_s ${default @{$X}@{?}} $f $x }.
