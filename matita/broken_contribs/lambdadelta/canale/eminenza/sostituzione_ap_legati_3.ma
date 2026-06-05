(* Questo documento fa parte della libreria digitale HELM (http://helm.cs.unibo.it)
   ed è distribuito ai sensi della licenza GNU GPL versione 2
*)

include "ground/subsets/subset_or_3_or_le.ma".
include "canale/eminenza/nomi_ap_legati_3_le.ma".
include "canale/eminenza/sostituzione_ap_legati_1.ma".
include "canale/eminenza/sostituzione_ap_liberi.ma".

(* Sostituzione *************************************************************)

(* Costruzioni coi nomi legati alla portata ristretta e l'inclusione ********)

lemma ap_legati_sost_ge_rc (y1) (y2) (W) (T):
      ℬ[y1,y2,ℱW]T ⊆ ℬ[y1]⦋W/y2⦌T.
#y1 #y2 #W #T elim T -T
[ #r <ap_legati_refs //
| #x #T #IH
  @ap_legati_3_nabs_inv_le
  [ #Hy1 #Hny1x #Hny2x -IH
    <(sost_nabs_neq … Hny2x) -Hny2x
    @ap_legati_1_nabs_ge_sx [ // ] -Hny1x
    @liberi_sost_ge_sx //
  | #Hny2x <(sost_nabs_neq … Hny2x) -Hny2x
    @(subset_le_trans … @ IH …) -IH //
  ]
| #T #V #IHT #IHV
  <sost_appl <ap_legati_appl <ap_legati_appl
  @subset_or_le_repl //
| #T #IH
  <sost_aabs <ap_legati_aabs <ap_legati_aabs //
]
qed.

lemma ap_legati_sost_ge (y1) (y2) (W) (T):
      y1 ⧸= y2 →
      ∪∪ ❨y2ϵℱT❩ℬ[y1]W | ℬ[y1,y2,ℱW]T | ℬ[y1]T ⊆ ℬ[y1]⦋W/y2⦌T.
#y1 #Hy2 #W #T #Hny12
@subset_le_or_3_sx
/2 width=1 by ap_legati_sost_ge_rc, ap_legati_sost_ge_dx, ap_legati_sost_ge_sx/
qed.

lemma ap_legati_sost_le (y1) (y2) (W) (T):
      ℬ[y1]⦋W/y2⦌T ⊆ ∪∪ ❨y2ϵℱT❩ℬ[y1]W | ℬ[y1,y2,ℱW]T | ℬ[y1]T.
#y1 #y2 #W #T elim T -T
[ #r
  elim (eq_riferimento_dec y2 r) #Hny2r destruct
  [ <sost_refs_eq
    /3 width=3 by subset_rest_ge_refl, subset_le_or_3_dx_sx/
  | <(sost_refs_neq … Hny2r) <ap_legati_refs //
  ]
| #x #T #IH
  elim (eq_nome_dec y2 x) #Hny2x destruct
  [ <sost_nabs_eq //
  | <(sost_nabs_neq … Hny2x)
    @ap_legati_1_nabs_inv_le
    [ #Hny1x #Hny1 -IH
      elim (liberi_sost_le … Hny1) -Hny1 #Hy1
      [ @subset_le_or_3_dx_rc
        /2 width=1 by ap_legati_3_nabs_ge_sx/
      | @subset_le_or_3_dx_dx
        /3 width=2 by ap_legati_1_nabs_ge_sx, subset_le_nimp_sx_refl_sx/
      ]
    | @(subset_le_trans … IH) -IH
      @subset_or_3_le_repl [3: // ]
      [ @(subset_rest_le_inv_gen … Hny2x) -Hny2x //
      | /2 width=1 by ap_legati_3_nabs_ge_dx/
      ]
    ]
  ]
| #T #V #IHT #IHV
  <sost_appl <ap_legati_appl <ap_legati_appl
  @(subset_le_trans … @ subset_or_le_repl … IHT … IHV) -IHT -IHV
  @(subset_le_trans … @ subset_le_or_or_3_bi …)
  @subset_or_3_le_repl //
| #T #IH <sost_aabs <ap_legati_aabs <ap_legati_aabs
  @(subset_le_trans … IH) -IH
  @subset_or_3_le_repl //
]
qed.
