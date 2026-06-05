(* Questo documento fa parte della libreria digitale HELM (http://helm.cs.unibo.it)
   ed è distribuito ai sensi della licenza GNU GPL versione 2
*)

include "ground/subsets/subset_or.ma".
include "ground/subsets/subset_listed_1.ma".
include "ground/subsets/subset_rest.ma".
include "canale/albero/termine.ma".
include "canale/notazione/nomi_legati.ma".

(* Nomi legati alla portata *************************************************)

(* Nota: nomi legati in U la cui portata soddisfa la condizione R *)
rec definition ap_legati (R1) (R2) (U) on U: 𝒫❨𝕍❩ ≝
match U with
[ Refs _   ⇒ (Ⓕ)
| NAbs x T ⇒ (❨R1 x T❩❴x❵) ∪ (❨R2 x T❩(ap_legati R1 R2 T))
| Appl T V ⇒ (ap_legati R1 R2 T) ∪ (ap_legati R1 R2 V)
| AAbs T   ⇒ ap_legati R1 R2 T
].

interpretation
  "nomi legati alla portata (sottoinsieme di nomi)"
  'NomiLegati R1 R2 T = (ap_legati R1 R2 T).

(* Riscritture **************************************************************)

lemma ap_legati_refs (R1) (R2) (r:ℝ):
      (Ⓕ) = ℬ[R1,R2]r.
//
qed.

lemma ap_legati_nabs (R1) (R2) (x) (T):
      (❨R1 x T❩❴x❵) ∪ ❨R2 x T❩ℬ[R1,R2]T = ℬ[R1,R2]𝛌x.T.
//
qed.

lemma ap_legati_appl (R1) (R2) (T) (V):
      ℬ[R1,R2]T ∪ ℬ[R1,R2]V = ℬ[R1,R2]T❨V❩.
//
qed.

lemma ap_legati_aabs (R1) (R2) (T):
      ℬ[R1,R2]T = ℬ[R1,R2]𝛌.T.
//
qed.
