(* Questo documento fa parte della libreria digitale HELM (http://helm.cs.unibo.it)
   ed è distribuito ai sensi della licenza GNU GPL versione 2
*)

include "ground/subsets/subset_or.ma".
include "ground/subsets/subset_nimply.ma".
include "ground/subsets/subset_rest.ma".
include "ground/subsets/subset_listed_1.ma".
include "canale/albero/termine.ma".
include "canale/notazione/nomi_liberi.ma".

(* Nomi liberi alla portata *************************************************)

(* Nota: nomi in w per cui almeno un y libero in U non sta nella loro portata *)
rec definition ap_liberi (y) (w) (U) on U: 𝒫❨𝕍❩ ≝
match U with
[ Refs r   ⇒ ❨y=❪ℝ❫r❩w
| NAbs x T ⇒ ❨y⧸=x❩((ap_liberi y w T) ⧵ ❴x❵)
| Appl T V ⇒ (ap_liberi y w T) ∪ (ap_liberi y w V)
| AAbs T   ⇒ ap_liberi y w T
].

interpretation
  "nomi liberi alla portata (sottoinsieme di nomi)"
  'NomiLiberi w y U = (ap_liberi y w U).

(* Riscritture **************************************************************)

lemma ap_liberi_refs (y:𝕍) (w) (r):
      ❨y=❪ℝ❫r❩w = ℱ[w/y]r.
//
qed.

lemma ap_liberi_nabs (y) (w) (x) (T):
      ❨y⧸=x❩(ℱ[w/y]T⧵❴x❵) = ℱ[w/y]𝛌x.T.
//
qed.

lemma ap_liberi_appl (y) (w) (T) (V):
      ℱ[w/y]T ∪ ℱ[w/y]V = ℱ[w/y]T❨V❩.
//
qed.

lemma ap_liberi_aabs (y) (w) (T):
      ℱ[w/y]T = ℱ[w/y]𝛌.T.
//
qed.
