(* Questo documento fa parte della libreria digitale HELM (http://helm.cs.unibo.it)
   ed è distribuito ai sensi della licenza GNU GPL versione 2
*)

include "ground/subsets/subset_nimply_or_le.ma".
include "ground/subsets/subset_listed_nimply.ma".
include "ground/subsets/subset_rest_le.ma".
include "ground/subsets/subset_help.ma".
include "canale/albero/nomi_liberi.ma".
include "canale/eminenza/nomi_ap_liberi.ma".
include "canale/eminenza/sostituzione.ma".

(* Sostituzione *************************************************************)

(* Costruzioni coi nomi liberi alla portata *********************************)

lemma liberi_sost_ge_sx (x) (V) (T):
      ℱ[ℱV/x]T ⊆ ℱ⦋V/x⦌T.
#y #W #T elim T -T
[ #r <ap_liberi_refs
  @subset_rest_le_gen #H0 destruct //
| #x #T #IH <ap_liberi_nabs
  @subset_rest_le_gen #Hnyx
  <sost_nabs_neq // <liberi_nabs -Hnyx
  /2 width=5 by subset_le_nimp_bi/
| #T #V #IHT #IHV <ap_liberi_appl <sost_appl <liberi_appl
  /2 width=5 by subset_or_le_repl/
| #T #IH <ap_liberi_aabs <sost_aabs <liberi_aabs //
]
qed.

lemma liberi_sost_le (x) (V) (T):
      ℱ⦋V/x⦌T ⊆ ℱ[ℱV/x]T ∪ (ℱT ⧵ ❴x❵).
#y #W #T elim T -T
[ #r <ap_liberi_refs
  elim (eq_riferimento_dec y r) #Hnyr destruct
  [ @(subset_le_trans ????? @ subset_le_or_dx_refl_sx …)
    /2 width=1 by subset_rest_ge_refl/
  | <sost_refs_neq //
    /5 width=3 by in_libero_inv_gen, subset_ge_nimp_refl_single, subset_dx_le_or/
  ]
| #x #T #IH <ap_liberi_nabs <liberi_nabs
  elim (eq_nome_dec y x) #Hnyx destruct
  [ <sost_nabs_eq <liberi_nabs -IH
    /4 width=4 by subset_ge_nimp_refl_single, subset_nin_nimp_single_dx_refl, subset_dx_le_or/
  | <sost_nabs_neq // <liberi_nabs
    @(subset_le_trans … @ subset_le_nimp_bi … IH @ subset_le_refl …) -IH
    @(subset_le_trans … @ subset_le_nimp_or_sx …)
    @subset_or_le_repl [| // ]
    /2 width=1 by subset_rest_ge_refl/
  ]
| #T #V #IHT #IHV <ap_liberi_appl <sost_appl <liberi_appl <liberi_appl
  @(subset_le_trans … @ subset_or_le_repl … IHT … IHV) -IHT -IHV
  @(subset_le_trans … @ subset_le_help_1 …)
  @subset_or_le_repl //
| #T #IHT <ap_liberi_aabs <sost_aabs <liberi_aabs <liberi_aabs //
]
qed.
