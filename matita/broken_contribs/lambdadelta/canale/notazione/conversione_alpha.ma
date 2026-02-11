(* Questo documento fa parte della libreria digitale HELM (http://helm.cs.unibo.it)
   ed è distribuito ai sensi della licenza GNU GPL versione 2
*)

(* Notazione per la conversione alpha ***************************************)

notation "hvbox( T1 ⪰α term 46 T2 )"
  non associative with precedence 45
  for @{ 'PassoAlpha $T1 $T2 }.
