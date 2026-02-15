(* Questo documento fa parte della libreria digitale HELM (http://helm.cs.unibo.it)
   ed è distribuito ai sensi della licenza GNU GPL versione 2
*)

(* Notazione per i nomi liberi **********************************************)

notation "hvbox( ℱ term 70 T )"
  non associative with precedence 70
  for @{ 'NomiLiberi $T }.

notation "hvbox( ℱ[ term 46 v / term 46 x ] term 70 T )"
  non associative with precedence 70
  for @{ 'NomiLiberi $v $x $T }.
