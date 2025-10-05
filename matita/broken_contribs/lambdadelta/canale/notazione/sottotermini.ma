(* Questo documento fa parte della libreria digitale HELM (http://helm.cs.unibo.it)
   ed è distribuito ai sensi della licenza GNU GPL versione 2
*)

(* Notazione per i sottotermini *********************************************)

include "basics/core_notation/subseteq_2.ma".

notation "hvbox( U ⊂ term 46 T )"
  non associative with precedence 45
  for @{ 'PSub $U $T }.

notation "hvbox( U ⧸⊆ term 46 T )"
  non associative with precedence 45
  for @{ 'NoSub $U $T }.

notation "hvbox( U ⧸⊂ term 46 T )"
  non associative with precedence 45
  for @{ 'NoPSub $U $T }.
