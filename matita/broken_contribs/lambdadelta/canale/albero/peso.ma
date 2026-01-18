(* Questo documento fa parte della libreria digitale HELM (http://helm.cs.unibo.it)
   ed è distribuito ai sensi della licenza GNU GPL versione 2
*)

include "ground/arith/pnat_lt_plus.ma".
include "canale/albero/termine.ma".
include "canale/notazione/peso.ma".

(* Peso di un termine *******************************************************)

rec definition peso (U) on U: ℕ⁺ ≝
match U with
[ Refs _   ⇒ (𝟏)
| NAbs _ T ⇒ ↑(peso T)
| Appl T V ⇒ ↑(peso T + peso V)
| AAbs T   ⇒ ↑(peso T)
].

interpretation
  "peso (termine)"
  'Peso T = (peso T).

(* Riscritture **************************************************************)

lemma peso_refs (r:ℝ): 𝟏 = ♯r.
//
qed.

lemma peso_nabs (x) (T): ↑♯T = ♯𝛌x.T.
//
qed.

lemma peso_appl (T) (V): ↑(♯T+♯V) = ♯T❨V❩.
//
qed.

lemma peso_aabs (T): ↑♯T = ♯𝛌.T.
//
qed.

(* Proprietà con l'ordine ***************************************************)

lemma peso_nabs_lt (x) (T): ♯T < ♯𝛌x.T.
//
qed.

lemma peso_appl_lt (T) (V): ♯T < ♯T❨V❩.
//
qed.

lemma peso_side_lt (T) (V): ♯V < ♯T❨V❩.
//
qed.

lemma peso_aabs_lt (T): ♯T < ♯𝛌.T.
//
qed.
