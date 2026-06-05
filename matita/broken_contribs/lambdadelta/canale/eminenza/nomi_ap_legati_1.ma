(* Questo documento fa parte della libreria digitale HELM (http://helm.cs.unibo.it)
   ed è distribuito ai sensi della licenza GNU GPL versione 2
*)

include "canale/albero/nomi_liberi.ma".
include "canale/albero/nomi_ap_legati.ma".
include "canale/notazione/condizione_b.ma".

(* Nomi legati alla portata *************************************************)

definition condizione_b1_sx: 𝕍 → relation2 (𝕍) (𝕋) ≝
           λy,x,T. ∧∧ y ⧸=x & y ϵ ℱT.

interpretation
  "nomi legati alla portata (condizione sinistra)"
  'CondizioneB y = (condizione_b1_sx y).

interpretation
  "nomi legati alla portata (condizione sinistra applicata)"
  'CondizioneBAppl y x T= (condizione_b1_sx y x T).

definition condizione_b1_dx: relation2 (𝕍) (𝕋) ≝
           λ_,_. ⊤.

interpretation
  "nomi legati alla portata (condizione destra)"
  'CondizioneB = (condizione_b1_dx).

interpretation
  "nomi legati alla portata (condizione destra applicata)"
  'CondizioneBAppl x T= (condizione_b1_dx x T).

(* Nota: nomi legati in U diversi da y e con y libero nella portata *)
interpretation
  "nomi legati alla portata (sottoinsieme di nomi)"
  'NomiLegati y U = (ap_legati (condizione_b1_sx y) condizione_b1_dx U).

(* Inversioni avanzate ******************************************************)

lemma sestesso_nin_ap_legati_1 (y) (T):
      y ⧸ϵ ℬ[y]T.
#y #T elim T -T
[ #r <ap_legati_refs
  /2 width=3 by subset_nin_inv_empty/
| #x #T #IH
  @subset_nin_or
  @subset_nin_rest [| // ] -IH
  * #Hnyx #_ -T
  /2 width=5 by subset_nin_single/
| #T #V #IHT #IHV <ap_legati_appl
  /2 width=7 by subset_nin_or/
| #T #IH <ap_legati_aabs //
]
qed-.

lemma nin_ap_legati_1_gen (x) (y) (T):
      (x ⧸= y → x ⧸ϵ ℬ[y]T) → x ⧸ϵ ℬ[y]T.
#x #y #T #IH
elim (eq_nome_dec x y) #Nnxy destruct
/2 width=3 by sestesso_nin_ap_legati_1/
qed-.
