(* Questo documento fa parte della libreria digitale HELM (http://helm.cs.unibo.it)
   ed è distribuito ai sensi della licenza GNU GPL versione 2
*)

include "ground/subsets/subset_or_le.ma".
include "ground/subsets/subset_listed_le_1.ma".
include "canale/albero/nomi_legati.ma".
include "canale/eminenza/passo_alpha.ma".

(* Passo alpha **************************************************************)

(* Inversioni coi nomi legati ***********************************************)

lemma astep_inv_applicativo_sx (T1) (T2):
      T1 ⪰α T2 → ℬT1 ⊆ Ⓕ → T1 = T2.
#T1 #T2 #HT12 elim HT12 -T1 -T2
[ //
| #T1 #T2 #x #_ #_ <legati_nabs #H0
  lapply (subset_le_or_inv_sx_sx … H0) -H0 #H0
  elim (subset_nle_single_empty ?? H0)
| #T1 #T2 #x1 #x2 #_ #_ #_ #_ #_ <legati_nabs #H0
  lapply (subset_le_or_inv_sx_sx … H0) -H0 #H0
  elim (subset_nle_single_empty ?? H0)
| #T1 #T2 #V1 #V2 #_ #_ #IHT #IHV <legati_appl #H0
  <IHT -IHT
  [ <IHV -IHV /2 width=4 by subset_le_or_inv_sx_dx/
  | -IHV /2 width=4 by subset_le_or_inv_sx_sx/
  ]
| #T1 #T2 #_ #IH <legati_aabs #H0
  <IH -IH //
]
qed-.
