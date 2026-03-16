(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2
*)

(* NOTATION FOR CONVERGENCE *************************************************)

notation < "hvbox( 𝗹𝗶𝗺[ break term 46 x, break term 46 F, break term 46 G ] break term 46 f ≘ break term 46 y )"
  non associative with precedence 45
  for @{ 'Lim $X $Y $f $F $G $x $y }.

notation > "hvbox( 𝗹𝗶𝗺[ break term 46 x, break term 46 F, break term 46 G ] break term 46 f ≘ break term 46 y )"
  non associative with precedence 45
  for @{ 'Lim ? ? $f $F $G $x $y }.

notation > "hvbox( 𝗹𝗶𝗺❪ break term 46 X, break term 46 Y ❫[ break term 46 x, break term 46 F, break term 46 G ] break term 46 f ≘ break term 46 y )"
  non associative with precedence 45
  for @{ 'Lim $X $Y $f $F $G $x $y }.
