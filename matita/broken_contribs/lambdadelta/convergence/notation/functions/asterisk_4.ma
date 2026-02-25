(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2
*)

(* NOTATION FOR LIMITS ******************************************************)

notation < "hvbox( i1 *[ break term 46 D ] break term 61 i2 )"
  non associative with precedence 60
  for @{ 'Asterisk $X $D $i1 $i2 }.

notation > "hvbox( i1 * opt ( ❪ break term 46 X ❫ ) opt ( [ break term 46 D ] ) break term 61 i2 )"
  non associative with precedence 60
  for @{ 'Asterisk ${default @{$X}@{?}} ${default @{$D}@{?}} $i1 $i2 }.
