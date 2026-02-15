(* Questo documento fa parte della libreria digitale HELM (http://helm.cs.unibo.it)
   ed è distribuito ai sensi della licenza GNU GPL versione 2
*)

(* Notazione per la sostituzione ********************************************)

notation "hvbox( ⦋ term 46 V / term 46 x ⦌ term 70 T )"
  non associative with precedence 70
  for @{ 'Sostituzione $V $x $T }.
