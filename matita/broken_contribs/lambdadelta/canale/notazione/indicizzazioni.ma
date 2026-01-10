(* Questo documento fa parte della libreria digitale HELM (http://helm.cs.unibo.it)
   ed è distribuito ai sensi della licenza GNU GPL versione 2
*)

(* Notazione per le funzioni di indicizzazione ******************************)

notation "hvbox( 𝕀𝕏 )"
  non associative with precedence 70
  for @{ 'CategoriaIX }.

notation "hvbox( f ˃ )"
  non associative with precedence 70
  for @{ 'SupRightArrowhead $f }.

notation "hvbox( f ˂ )"
  non associative with precedence 70
  for @{ 'SupLeftArrowhead $f }.

notation "hvbox( ⫯[ term 46 x ] term 70 f )"
  non associative with precedence 70
  for @{ 'UpSpoon $x $f }.
