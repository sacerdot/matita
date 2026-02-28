(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2
*)

(* NOTATION FOR CONVERGENCE *************************************************)

notation < "hvbox( f ＠❨ break term 46 a ❩ )"
  non associative with precedence 69
  for @{ 'At $X $f $a }.

notation > "hvbox( f ＠ opt ( ❪ break term 46 X ❫ ) ❨ break term 46 a ❩ )"
  non associative with precedence 69
  for @{ 'At ${default @{$X}@{?}} $f $a }.
