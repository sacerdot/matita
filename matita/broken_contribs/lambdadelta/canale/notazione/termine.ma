(* Questo documento fa parte della libreria digitale HELM (http://helm.cs.unibo.it)
   ed è distribuito ai sensi della licenza GNU GPL versione 2
*)

(* Notazione per i termini **************************************************)

notation "hvbox( 𝕋 )"
  non associative with precedence 70
  for @{ 'CategoriaT }.

notation "hvbox( 𝛌 term 46 x. term 70 T )"
  non associative with precedence 70
  for @{ 'AstrazioneNome $x $T }.

notation "hvbox( T ❨ term 46 V ❩ )"
  non associative with precedence 70
  for @{ 'Applicazione $T $V }.

notation "hvbox( 𝛌. term 70 T )"
  non associative with precedence 70
  for @{ 'Astrazione $T }.

notation "hvbox( 𝗜 )"
  non associative with precedence 70
  for @{ 'TermineI }.

notation "hvbox( 𝗞 )"
  non associative with precedence 70
  for @{ 'TermineK }.

notation "hvbox( 𝗭 )"
  non associative with precedence 70
  for @{ 'TermineZ }.

notation "hvbox( 𝗦 )"
  non associative with precedence 70
  for @{ 'TermineS }.

notation "hvbox( 𝗕 )"
  non associative with precedence 70
  for @{ 'TermineB }.

notation "hvbox( 𝗖 )"
  non associative with precedence 70
  for @{ 'TermineC }.

notation "hvbox( 𝗪 )"
  non associative with precedence 70
  for @{ 'TermineW }.

notation "hvbox( 𝗧 )"
  non associative with precedence 70
  for @{ 'TermineT }.

notation "hvbox( 𝚯 )"
  non associative with precedence 70
  for @{ 'TermineTheta }.
