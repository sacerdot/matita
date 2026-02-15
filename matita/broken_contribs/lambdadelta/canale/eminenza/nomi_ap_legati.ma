(* Questo documento fa parte della libreria digitale HELM (http://helm.cs.unibo.it)
   ed è distribuito ai sensi della licenza GNU GPL versione 2
*)

include "ground/subsets/subset_rest.ma".
include "canale/albero/nomi_liberi.ma".
include "canale/notazione/nomi_legati.ma".

(* Nomi legati alla portata *************************************************)

(* Nota: nomi legati in U diversi da y e con y libero nella portata *)
rec definition ap_legati (y) (U) on U: 𝒫❨𝕍❩ ≝
match U with
[ Refs _   ⇒ (Ⓕ)
| NAbs x T ⇒ (❨y⧸=x❩❨yϵℱT❩❴x❵) ∪ (ap_legati y T)
| Appl T V ⇒ (ap_legati y T) ∪ (ap_legati y V)
| AAbs T   ⇒ ap_legati y T
].

interpretation
  "nomi legati alla portata (sottoinsieme di nomi)"
  'NomiLegati x T = (ap_legati x T).

(* Riscritture **************************************************************)

lemma ap_legati_refs (y) (r:ℝ): Ⓕ = ℬ[y]r.
//
qed.

lemma ap_legati_nabs (y) (x) (T):
      (❨y⧸=x❩❨yϵℱT❩❴x❵) ∪ ℬ[y]T = ℬ[y]𝛌x.T.
//
qed.

lemma ap_legati_appl (y) (T) (V): ℬ[y]T ∪ ℬ[y]V = ℬ[y]T❨V❩.
//
qed.

lemma ap_legati_aabs (y) (T):
      ℬ[y]T = ℬ[y]𝛌.T.
//
qed.
