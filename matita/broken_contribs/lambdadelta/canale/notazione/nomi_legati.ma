(* Questo documento fa parte della libreria digitale HELM (http://helm.cs.unibo.it)
   ed è distribuito ai sensi della licenza GNU GPL versione 2
*)

(* Notazione per i nomi legati **********************************************)

notation "hvbox( ℬ term 70 U )"
  non associative with precedence 70
  for @{ 'NomiLegati $U }.

notation "hvbox( ℬ[ term 46 y ] term 70 U )"
  non associative with precedence 70
  for @{ 'NomiLegati $y $U }.

notation "hvbox( ℬ[ term 46 R1, term 46 R2 ] term 70 U )"
  non associative with precedence 70
  for @{ 'NomiLegati $R1 $R2 $U }.

notation "hvbox( ℬ[ term 46 y1, term 46 y2, term 46 W ] term 70 U )"
  non associative with precedence 70
  for @{ 'NomiLegati $y1 $y2 $W $U }.
