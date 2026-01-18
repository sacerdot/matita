(* Questo documento fa parte della libreria digitale HELM (http://helm.cs.unibo.it)
   ed è distribuito ai sensi della licenza GNU GPL versione 2
*)

(* Notazione per le trasformazioni di indicizzazione ************************)

notation "hvbox( ⫯˃[ term 46 x ] term 70 f )"
  non associative with precedence 70
  for @{ 'UpSpoonDx $x $f }.

notation "hvbox( f ＠⧣˃❨ term 46 a ❩ )"
  non associative with precedence 69
  for @{ 'AtSharpDx $f $a }.
