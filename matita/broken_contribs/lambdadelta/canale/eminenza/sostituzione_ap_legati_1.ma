(* Questo documento fa parte della libreria digitale HELM (http://helm.cs.unibo.it)
   ed è distribuito ai sensi della licenza GNU GPL versione 2
*)

include "canale/albero/nomi_liberi_restrizione.ma".
include "canale/eminenza/nomi_ap_legati_1_le.ma".
include "canale/eminenza/sostituzione_liberi.ma".

(* Sostituzione *************************************************************)

(* Costruzioni coi nomi legati alla portata e l'inclusione ******************)

lemma ap_legati_sost_ge_sx (y1) (y2) (W) (T):
      ❨y2ϵℱT❩ℬ[y1]W ⊆ ℬ[y1]⦋W/y2⦌T.
#y1 #y2 #W #T elim T -T
[ #r
  @(subset_le_trans … @ liberi_rest_refs_le …)
  @subset_rest_le_gen #H0 destruct
  <sost_refs_eq //
| #x #T #IH
  @(subset_le_trans … @ liberi_rest_nabs_le …)
  @subset_rest_le_gen #Hny2x
  @subset_rest_le_gen #Hy2
  <(sost_nabs_neq … Hny2x)
  @(subset_le_trans … @ subset_rest_le_inv_gen ???? Hy2 IH) //
| #T #V #IHT #IHV
  <sost_appl <ap_legati_appl
  @(subset_le_trans … @ liberi_rest_appl_le …)
  @(subset_or_le_repl … IHT … IHV)
| #T #IH <sost_aabs <ap_legati_aabs <liberi_aabs //
]
qed.

lemma ap_legati_sost_ge_dx (y1) (y2) (W) (T):
      y1 ⧸= y2 → ℬ[y1]T ⊆ ℬ[y1]⦋W/y2⦌T.
#y1 #y2 #W #T #Hny12 elim T -T
[ #r <ap_legati_refs //
| #x #T #IH
  @ap_legati_1_nabs_inv_le
  [ #Hny1x #Hy1
    elim (eq_nome_dec y2 x) #Hny2x destruct
    [ /2 width=1 by ap_legati_1_nabs_ge_sx/ ]
    <(sost_nabs_neq … Hny2x)
    @ap_legati_1_nabs_ge_sx [ // ]
    @liberi_sost_ge_dx
    /4 width=1 by subset_in_inv_single, subset_in_nimp/
  | elim (eq_nome_dec y2 x) #Hny2x destruct
    [ <sost_nabs_eq -IH
      @(subset_le_trans ????? @ ap_legati_nabs_ge_dx …) //
    | @(subset_le_trans … IH) -IH
      <(sost_nabs_neq … Hny2x) //
    ]
  ]
| #T #V #IHT #IHV
  <sost_appl <ap_legati_appl <ap_legati_appl
  @(subset_le_trans … @ subset_or_le_repl … IHT … IHV) -IHT -IHV
  @subset_or_le_repl //
| #T #IH
  <sost_aabs <ap_legati_aabs <ap_legati_aabs //
]
qed.

(* Riscritture principali coi nomi legati alla portata **********************)

(* Nota: terzo lemma della sostituzione sequenziale *)
(* Nota: vale anche senza le premesse 2 e 3 nel caso V1 = y1 *)
theorem sost_sost_neq_non_ap_legato (y2) (y1) (V2) (V1) (T):
        y2 ⧸= y1 → y1 ⧸ϵ ℱV2 → y2 ⧸ϵ ℬ[y1]T →
        (⦋⦋V2 / y2⦌V1 / y1⦌ ⦋V2 / y2⦌ T) = ⦋V2 / y2⦌ ⦋V1 / y1⦌ T.
#y2 #y1 #V2 #V1 #T elim T -T
[ #r #Hny21 #Hny1 #_
  elim (eq_riferimento_dec y1 r) #Hny1r destruct
  [ <(sost_refs_neq … @ neq_nome_riferimento … Hny21)
    <sost_refs_eq <sost_refs_eq //
  | <(sost_refs_neq … Hny1r)
    elim (eq_riferimento_dec y2 r) #Hny2r destruct
    [ <sost_refs_eq <sost_non_libero //
    | <(sost_refs_neq … Hny2r) <(sost_refs_neq … Hny1r) //
    ]
  ]
| #x #T #IH #Hny21 #Hny1 #Hny2
  elim (eq_nome_dec y1 x) #Hny1x destruct
  [ <sost_nabs_eq <(sost_nabs_neq … Hny21) <sost_nabs_eq //
  | <(sost_nabs_neq … Hny1x)
    elim (eq_nome_dec y2 x) #Hny2x destruct
    [ <sost_nabs_eq <sost_nabs_eq <(sost_nabs_neq … Hny1x)
      elim (in_liberi_dec T y1) #Hy1
      [ <(sost_non_libero … x) //
        /3 width=1 by ap_legati_1_nabs_ge_sx/
      | <(sost_non_libero … Hy1) <(sost_non_libero … Hy1) //
      ]
    | <(sost_nabs_neq … Hny2x) <(sost_nabs_neq … Hny2x)
      <(sost_nabs_neq … Hny1x) <IH -IH //
      /3 width=1 by ap_legati_1_nabs_ge_dx/
    ]
  ]
| #T #V #IHT #IHV #Hny21 #Hny1 <ap_legati_appl #Hny2
  <sost_appl <sost_appl
  elim (subset_nin_inv_or ???? Hny2) -Hny2 #H1ny2 #H2ny2
  <IHT -IHT // <IHV -IHV //
| #T #IH #Hny21 #Hny1 <ap_legati_aabs #Hny2
  <sost_aabs <sost_aabs <IH -IH //
]
qed.

(* Nota: lemma della sostituzione sequenziale integra *)
theorem sost_sost_neq_integra (y2) (y1) (V2) (V1) (T):
        y2 ⧸= y1 → y1 ⧸ϵ ℱV2 → ℱV1 ⧸≬ ℬ[y1]T →
        (⦋⦋V2 / y2⦌V1 / y1⦌ ⦋V2 / y2⦌ T) = ⦋V2 / y2⦌ ⦋V1 / y1⦌ T.
#y2 #y1 #V2 #V1 #T #Hny21 #Hny1 #HN1
elim (in_liberi_dec V1 y2) #Hy2
[ @(sost_sost_neq_non_ap_legato … Hny21 Hny1)
  /3 width=3 by subset_ol_i/
| <(sost_non_libero … Hy2)
  @(sost_sost_neq_non_libero … Hny21 Hny1) //
]
qed.

(* Nota: quarto lemma della sostituzione sequenziale *)
theorem sost_sost_interna (y2) (y1) (V2) (V1) (T):
        y2 ⧸ϵ ℱT → y2 ⧸ϵ ℬ[y1]T →
        (⦋ ⦋V2 / y2⦌V1 / y1⦌ T) = ⦋V2 / y2⦌ ⦋V1 / y1⦌ T.
#y2 #y1 #V2 #V1 #T elim T -T
[ #r #Hny2 #_
  elim (eq_riferimento_dec y1 r) #Hny1r destruct
  [ <sost_refs_eq <sost_refs_eq //
  | <(sost_refs_neq … Hny1r) <(sost_refs_neq … Hny1r)
    <(sost_non_libero … Hny2) //
  ]
| #x #T #IH #H1ny2 #H2ny2
  elim (in_liberi_dec (𝛌x.T) y1) #Hny1
  [ elim (in_liberi_inv_nabs … Hny1) -Hny1 #Hy1 #Hny1x
    elim (eq_nome_dec y2 x) #Hny2x destruct
    [ elim H2ny2 -H1ny2 -H2ny2 -IH
      /3 width=1 by ap_legati_1_nabs_ge_sx/
    | <(sost_nabs_neq … Hny1x) <(sost_nabs_neq … Hny1x)
      <(sost_nabs_neq … Hny2x) <IH -IH
      /3 width=1 by ap_legati_nabs_ge_dx, in_liberi_nabs/
    ]
  | <(sost_non_libero … Hny1) <(sost_non_libero … Hny1)
    <(sost_non_libero … H1ny2) //
  ]
| #T #V #IHT #IHV #H1y2 #H2y2
  <sost_appl <sost_appl
  <IHT -IHT [2,3: /3 width=1 by subset_or_in_sx/ ]
  <IHV -IHV [ // |*: /3 width=1 by subset_or_in_dx/ ]
| #T #IHT #H1y2 #H2y2
  <sost_aabs <sost_aabs
  <IHT -IHT /2 width=1 by/
]
qed.

theorem sost_sost_trans (y2) (y1) (V) (T):
        y2 ⧸ϵ ℱT → y2 ⧸ϵ ℬ[y1]T → ⦋V / y1⦌ T = ⦋V / y2⦌ ⦋y2 / y1⦌ T.
/2 width=1 by sost_sost_interna/
qed.

lemma sost_sost_inversa (y1) (y2) (T):
      y2 ⧸ϵ ℱT → y2 ⧸ϵ ℬ[y1]T → T = ⦋y1 / y2⦌ ⦋y2 / y1⦌ T.
/2 width=1 by sost_sost_trans/
qed.
