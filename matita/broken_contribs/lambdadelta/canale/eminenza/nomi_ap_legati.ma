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

(* Inversioni avanzate ******************************************************)

lemma sestesso_nin_ap_legati (y) (T):
      y ⧸ϵ ℬ[y]T.
#y #T elim T -T
[ #r <ap_legati_refs
  /2 width=3 by subset_nin_inv_empty/
| #x #T #IH <ap_legati_nabs
  @subset_nin_or [| // ] -IH
  @subset_nin_rest #Hnyx
  @subset_nin_rest #_ -T
  /2 width=5 by subset_nin_single/
| #T #V #IHT #IHV <ap_legati_appl
  /2 width=7 by subset_nin_or/
| #T #IH <ap_legati_aabs //
]
qed-.

lemma nin_ap_legati_gen (x) (y) (T):
      (x ⧸= y → x ⧸ϵ ℬ[y]T) → x ⧸ϵ ℬ[y]T.
#x #y #T #IH
elim (eq_nome_dec x y) #Nnxy destruct
/2 width=3 by sestesso_nin_ap_legati/
qed-.
