(* Questo documento fa parte della libreria digitale HELM (http://helm.cs.unibo.it)
   ed è distribuito ai sensi della licenza GNU GPL versione 2
*)

(* Notazione per l'guaglianza computazionale ********************************)

notation > "hvbox( ❨! term 46 x1 ⇔ term 46 x2 ❩ term 46 Y | opt ( ❪ term 46 X ❫ ) term 70 Z )"
  non associative with precedence 70
  for @{ 'UguaglianzaComputazionale ${default @{$X}@{?}} $x1 $x2 $Y $Z }.

notation < "hvbox( ❨! term 46 x1 ⇔ term 46 x2 ❩ term 46 Y | term 70 Z )"
  non associative with precedence 70
  for @{ 'UguaglianzaComputazionale $X $x1 $x2 $Y $Z }.
