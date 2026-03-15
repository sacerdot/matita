(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2
*)

(* NOTATION FOR CONVERGENCE *************************************************)

notation < "hvbox( f ＠❨ break term 46 x ❩ )"
  non associative with precedence 69
  for @{ 'At $X $Y $f $x }.

notation > "hvbox( f ＠❪ break term 46 X, break term 46 Y ❫❨ break term 46 x ❩ )"
  non associative with precedence 69
  for @{ 'At $X $Y $f $x }.

notation > "hvbox( f ＠❨ break term 46 x ❩ )"
  non associative with precedence 69
  for @{ 'At ? ? $f $x }.
