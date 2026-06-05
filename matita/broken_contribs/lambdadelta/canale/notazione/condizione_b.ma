(* Questo documento fa parte della libreria digitale HELM (http://helm.cs.unibo.it)
   ed è distribuito ai sensi della licenza GNU GPL versione 2
*)

(* Notazione per la condizione B (nomi legati alla portata) *****************)

notation "hvbox( 𝐁 )"
  non associative with precedence 45
  for @{ 'CondizioneB }.

notation < "hvbox( 𝐁 ␣ term 90 x ␣ term 90 T )"
  non associative with precedence 45
  for @{ 'CondizioneBAppl $x $T }.

notation "hvbox( 𝐁[ term 46 y ] )"
  non associative with precedence 45
  for @{ 'CondizioneB $y }.

notation < "hvbox( 𝐁[ term 46 y ] ␣ term 90 x ␣ term 90 T )"
  non associative with precedence 45
  for @{ 'CondizioneBAppl $y $x $T }.

notation "hvbox( 𝐁[ term 46 W, term 46 y1, term 46 y2 ] )"
  non associative with precedence 45
  for @{ 'CondizioneB $W $y1 $y2 }.

notation < "hvbox( 𝐁[ term 46 W, term 46 y1, term 46 y2 ] ␣ term 90 x ␣ term 90 T )"
  non associative with precedence 45
  for @{ 'CondizioneBAppl $W $y1 $y2 $x $T }.
