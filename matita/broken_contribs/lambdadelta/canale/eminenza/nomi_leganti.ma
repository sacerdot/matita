(* Questo documento fa parte della libreria digitale HELM (http://helm.cs.unibo.it)
   ed è distribuito ai sensi della licenza GNU GPL versione 2
*)

include "ground/subsets/subset_or.ma".
include "ground/subsets/subset_listed_1.ma".
include "canale/albero/nomi_liberi.ma".
include "canale/notazione/nomi_legati.ma".

(* Nomi leganti *************************************************************)

rec definition leganti (y) (U) on U: 𝒫❨𝕍❩ ≝
match U with
[ Refs _   ⇒ (Ⓕ)
| NAbs x T ⇒ {z | ∨∨ ∧∧ y ϵ ℱT & z ϵ ❴x❵ ∪ (leganti y T)
                    | ∧∧ y ⧸ϵ ℱT & z ϵ (leganti y T)
              }
| Appl T V ⇒ (leganti y T) ∪ (leganti y V)
| AAbs T   ⇒ leganti y T
].

interpretation
  "nomi leganti (sottoinsieme di nomi)"
  'NomiLegati x T = (leganti x T).

(* Riscritture **************************************************************)

lemma leganti_refs (y) (r:ℝ): Ⓕ = ℬ[y]r.
//
qed.

lemma leganti_nabs (y) (x) (T):
      {z | ∨∨ ∧∧ y ϵ ℱT & z ϵ ❴x❵ ∪ ℬ[y]T
            | ∧∧ y ⧸ϵ ℱT & z ϵ ℬ[y]T
      } = ℬ[y]𝛌x.T.
//
qed.

lemma leganti_appl (y) (T) (V): ℬ[y]T ∪ ℬ[y]V = ℬ[y]T❨V❩.
//
qed.

lemma leganti_aabs (y) (T):
      ℬ[y]T = ℬ[y]𝛌.T.
//
qed.
