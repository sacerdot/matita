(* Questo documento fa parte della libreria digitale HELM (http://helm.cs.unibo.it)
   ed è distribuito ai sensi della licenza GNU GPL versione 2
*)

(* Notazione per i discriminatori *******************************************)

notation > "hvbox( ❨ term 46 x ❩ term 46 Y | opt ( ❪ term 46 X ❫ ) term 70 Z )"
  non associative with precedence 70
  for @{ 'Discriminatore ${default @{$X}@{?}} $x $Y $Z }.

notation < "hvbox( ❨ term 46 x ❩ term 46 Y | term 70 Z )"
  non associative with precedence 70
  for @{ 'Discriminatore $X $x $Y $Z }.
