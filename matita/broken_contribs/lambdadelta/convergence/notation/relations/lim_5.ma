(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2
*)

(* NOTATION FOR CONVERGENCE *************************************************)

notation < "hvbox( 𝗹𝗶𝗺[ break term 46 D ] break term 46 f ≘ break term 46 C )"
  non associative with precedence 45
  for @{ 'Lim $X $Y $f $D $C }.

notation > "hvbox( 𝗹𝗶𝗺[ break term 46 D ] break term 46 f ≘ break term 46 C )"
  non associative with precedence 45
  for @{ 'Lim ? ? $f $D $C }.

notation > "hvbox( 𝗹𝗶𝗺❪ break term 46 X, break term 46 Y ❫[ break term 46 D ] break term 46 f ≘ break term 46 C )"
  non associative with precedence 45
  for @{ 'Lim $X $Y $f $D $C }.
