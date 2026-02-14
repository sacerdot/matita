(* Questo documento fa parte della libreria digitale HELM (http://helm.cs.unibo.it)
   ed è distribuito ai sensi della licenza GNU GPL versione 2
*)

include "ground/subsets/subset_and.ma".
include "canale/albero/nomi_liberi.ma".
include "canale/notazione/nomi_legati.ma".

(* Nomi ∀-legati ************************************************************)

rec definition u_legati (y) (U) on U: 𝒫❨𝕍❩ ≝
match U with
[ Refs _   ⇒ (Ⓕ)
| NAbs x T ⇒ {z | ∨∨ ∧∧ y ϵ ℱT & y ⧸= x & z = x | z ϵ (u_legati y T)}
| Appl T V ⇒ (u_legati y T) ∩ (u_legati y V)
| AAbs T   ⇒ u_legati y T
].

interpretation
  "nomi ∀-legati (sottoinsieme di nomi)"
  'NomiLegatiU x T = (u_legati x T).

(* Riscritture **************************************************************)

lemma u_legati_refs (y) (r:ℝ): Ⓕ = ℬ﹗[y]r.
//
qed.

lemma u_legati_nabs (y) (x) (T):
      {z | ∨∨ ∧∧ y ϵ ℱT & y ⧸= x & z = x | z ϵ ℬ﹗[y]T} = ℬ﹗[y]𝛌x.T.
//
qed.

lemma u_legati_appl (y) (T) (V): ℬ﹗[y]T ∩ ℬ﹗[y]V = ℬ﹗[y]T❨V❩.
//
qed.

lemma u_legati_aabs (y) (T):
      ℬ﹗[y]T = ℬ﹗[y]𝛌.T.
//
qed.

(* Costruzioni avanzate *****************************************************)

axiom in_u_legati_dec (x) (y) (T):
      Decidable (xϵℬ﹗[y]T).
