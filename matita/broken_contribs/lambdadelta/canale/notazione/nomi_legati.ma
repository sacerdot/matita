(* Questo documento fa parte della libreria digitale HELM (http://helm.cs.unibo.it)
   ed è distribuito ai sensi della licenza GNU GPL versione 2
*)

(* Notazione per i nomi legati **********************************************)

notation "hvbox( ℬ term 70 T )"
  non associative with precedence 70
  for @{ 'NomiLegati $T }.

notation "hvbox( ℬ[ term 46 x ] term 70 T )"
  non associative with precedence 70
  for @{ 'NomiLegati $x $T }.
