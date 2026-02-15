(* Questo documento fa parte della libreria digitale HELM (http://helm.cs.unibo.it)
   ed è distribuito ai sensi della licenza GNU GPL versione 2
*)

include "canale/albero/riferimento_uguaglianza.ma".
include "canale/albero/termine.ma".
include "canale/notazione/sostituzione.ma".

(* Sostituzione completa ****************************************************)

rec definition sost (y:𝕍) (W) (U) on U: 𝕋 ≝
match U with
[ Refs r   ⇒ ❨!y ⇔ r❩ W | U
| NAbs x T ⇒ ❨!y ⇔ x❩ U | 𝛌x.(sost y W T)
| Appl T V ⇒ (sost y W T)❨sost y W V❩
| AAbs T   ⇒ (𝛌.(sost y W T))
].

interpretation
  "sostituzione (termine)"
  'Sostituzione W y U = (sost y W U).

(* Riscritture di base ******************************************************)

lemma sost_refs (W:𝕋) (y:𝕍) (r:ℝ):
      ❨!y ⇔ r❩ W | r = ⦋W / y⦌ r.
//
qed.

lemma sost_nabs (W) (T) (y) (x):
      ❨!y ⇔ x❩ 𝛌x.T | 𝛌x.⦋W / y⦌T = ⦋W / y⦌ 𝛌x.T.
//
qed.

lemma sost_appl (W) (T) (V) (y):
      (⦋W / y⦌T)❨⦋W / y⦌V❩ = ⦋W / y⦌ T❨V❩.
//
qed.

lemma sost_aabs (W) (T) (y):
      (𝛌.⦋W / y⦌T) = ⦋W / y⦌ 𝛌.T.
//
qed.


(* Riscritture avanzate *****************************************************)

lemma sost_refs_eq (W) (x):
      W = ⦋W / x⦌ x.
#W #x <sost_refs //
qed.

lemma sost_refs_neq (W) (y:𝕍) (r:ℝ):
      y ⧸=❪ℝ❫ r → r =❪𝕋❫ ⦋W / y⦌ r.
/2 width=1 by ruc_neq/
qed.

lemma sost_nabs_eq (W) (T) (x):
      (𝛌x.T) = ⦋W / x⦌ 𝛌x.T.
//
qed.

lemma sost_nabs_neq (W) (T) (y) (x):
      y ⧸= x → 𝛌x.⦋W / y⦌T = ⦋W / y⦌ 𝛌x.T.
/2 width=1 by nuc_neq/
qed.

lemma sost_eq (y) (T):
      T = ⦋y / y⦌ T.
#y #T elim T -T
[ #r elim (eq_riferimento_dec y r) #Hnyr destruct
  [ <sost_refs_eq //
  | <(sost_refs_neq … Hnyr) //
  ]
| #x #T #IH elim (eq_nome_dec y x) #Hnyx //
  <(sost_nabs_neq … Hnyx) //
| #T #V #IHT #IHV
  <sost_appl //
| #T #IHT
  <sost_aabs //
]
qed.

(* Riscritture principali ***************************************************)

(* Nota: primo lemma della sostituzione sequenziale *)
theorem sost_sost_eq (y) (V2) (V1) (T):
        ⦋⦋V2 / y⦌V1 / y⦌ T = ⦋V2 / y⦌ ⦋V1 / y⦌ T.
#y #V2 #V1 #T elim T -T
[ #r elim (eq_riferimento_dec y r) #Hnyr destruct
  [ <sost_refs_eq //
  | <(sost_refs_neq … Hnyr)
    <(sost_refs_neq … Hnyr) <(sost_refs_neq … Hnyr) //
  ]  
| #x #T #IH elim (eq_nome_dec y x) #Hnyx //
  <(sost_nabs_neq … Hnyx)
  <(sost_nabs_neq … Hnyx) <(sost_nabs_neq … Hnyx) //
| #T #V #IHT #IHV
  <sost_appl <sost_appl //
| #T #IHT
  <sost_aabs <sost_aabs //
]
qed.
