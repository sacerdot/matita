(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2
*)

(* NOTATION FOR CONVERGENCE *************************************************)

notation < "hvbox( f ＠𝗌❨ break term 46 x ❩ )"
  non associative with precedence 69
  for @{ 'At_s $X $Y $f $x }.

notation > "hvbox( f ＠𝗌❪ break term 46 X, break term 46 Y ❫❨ break term 46 x ❩ )"
  non associative with precedence 69
  for @{ 'At_s $X $Y $f $x }.

notation > "hvbox( f ＠𝗌❨ break term 46 x ❩ )"
  non associative with precedence 69
  for @{ 'At_s ? ? $f $x }.
