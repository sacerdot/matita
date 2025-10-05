(* Questo documento fa parte della libreria digitale HELM (http://helm.cs.unibo.it)
   ed è distribuito ai sensi della licenza GNU GPL versione 2
*)

include "ground/subsets/subset_or.ma".
include "ground/subsets/subset_listed_1.ma".
include "canale/albero/termine.ma".
include "canale/notazione/nomi_legati.ma".

(* Nomi legati **************************************************************)

rec definition legati (t) on t: 𝒫❨𝕍❩ ≝
match t with
[ NRef _   ⇒ (Ⓕ)
| NAbs x T ⇒ ❴x❵ ∪ (legati T)
| Appl T V ⇒ (legati T) ∪ (legati V)
].

interpretation
  "nomi legati (sottoinsieme di nomi)"
  'NomiLegati T = (legati T).

(* Riscritture **************************************************************)

lemma legati_nref (x:𝕍): Ⓕ = ℬx.
//
qed.

lemma legati_nabs (x) (T): ❴x❵ ∪ ℬT = ℬ𝛌x.T.
//
qed.

lemma legati_appl (T) (V): ℬT ∪ ℬV = ℬT❨V❩.
//
qed.
