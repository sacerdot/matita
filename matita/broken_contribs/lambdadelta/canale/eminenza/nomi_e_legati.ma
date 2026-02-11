(* Questo documento fa parte della libreria digitale HELM (http://helm.cs.unibo.it)
   ed è distribuito ai sensi della licenza GNU GPL versione 2
*)

include "canale/albero/nomi_liberi.ma".
include "canale/notazione/nomi_legati.ma".

(* Nomi ∃-legati ************************************************************)

rec definition e_legati (y) (U) on U: 𝒫❨𝕍❩ ≝
match U with
[ Refs _   ⇒ (Ⓕ)
| NAbs x T ⇒ {z | ∨∨ ∧∧ y ϵ ℱT & y ⧸= x & z = x | z ϵ (e_legati y T)}
| Appl T V ⇒ (e_legati y T) ∪ (e_legati y V)
| AAbs T   ⇒ e_legati y T
].

interpretation
  "nomi ∃-legati (sottoinsieme di nomi)"
  'NomiLegatiE x T = (e_legati x T).

(* Riscritture **************************************************************)

lemma e_legati_refs (y) (r:ℝ): Ⓕ = ℬ﹖[y]r.
//
qed.

lemma e_legati_nabs (y) (x) (T):
      {z | ∨∨ ∧∧ y ϵ ℱT & y ⧸= x & z = x | z ϵ ℬ﹖[y]T} = ℬ﹖[y]𝛌x.T.
//
qed.

lemma e_legati_appl (y) (T) (V): ℬ﹖[y]T ∪ ℬ﹖[y]V = ℬ﹖[y]T❨V❩.
//
qed.

lemma e_legati_aabs (y) (T):
      ℬ﹖[y]T = ℬ﹖[y]𝛌.T.
//
qed.
