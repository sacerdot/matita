(* Questo documento fa parte della libreria digitale HELM (http://helm.cs.unibo.it)
   ed è distribuito ai sensi della licenza GNU GPL versione 2
*)

include "ground/subsets/subset_rest_nimply_le.ma".
include "canale/eminenza/sostituzione_ap_liberi_liberi.ma".
include "canale/eminenza/passo_alpha.ma".

(* Distruzioni coi nomi liberi **********************************************)

lemma astep_liberi_le (T1) (T2):
      T1 ⪰α T2 → ℱT1 ⊆ ℱT2.
#T1 #T2 #HT elim HT -T1 -T2
[ //
| #T1 #T2 #x #_ #IH <liberi_nabs <liberi_nabs
  /2 width=5 by subset_le_nimp_bi/
| #T1 #T2 #x1 #x2 #Hnx #H1nx #H2nx #HT #IH
  <liberi_nabs <liberi_nabs
  @(subset_le_trans … @ subset_le_nimp_bi … IH @ subset_le_refl …) -IH
  @(subset_le_trans ????? @ subset_le_nimp_bi … (liberi_sost_ge_dx …) @ subset_le_refl …)
  @(subset_le_trans ????? @ subset_le_nimp_comm_dx …)
  /3 width=5 by subset_ge_nimp_refl_single, subset_le_nimp_bi/
| #T1 #T2 #V1 #V2 #_ #_ #IHT #IHV <liberi_appl <liberi_appl
  /2 width=5 by subset_or_le_repl/
| #T1 #T2 #_ #IH <liberi_aabs <liberi_aabs //
]
qed-.

lemma astep_liberi_ge (T1) (T2):
      T1 ⪰α T2 → ℱT2 ⊆ ℱT1.
#T1 #T2 #HT elim HT -T1 -T2
[ //
| #T1 #T2 #x #_ #IH <liberi_nabs <liberi_nabs
  /2 width=5 by subset_le_nimp_bi/
| #T1 #T2 #x1 #x2 #Hnx #H1nx #H2nx #HT #IH
  <liberi_nabs <liberi_nabs
  @(subset_le_trans … @ subset_le_nimp_bi … (liberi_sost_le_integra …) @ subset_le_refl …)
  @(subset_le_trans … @ subset_le_nimp_or_sx …)
  @subset_le_or_sx
  [ @(subset_le_trans … @ subset_rest_nimp_ge …)
    @subset_rest_le_gen #_ //
  | @(subset_le_trans … @ subset_le_nimp_comm_dx …)
    @subset_le_nimp_bi [| // ]
    @(subset_le_trans ????? IH) -IH //
  ]
| #T1 #T2 #V1 #V2 #_ #_ #IHT #IHV <liberi_appl <liberi_appl
  /2 width=5 by subset_or_le_repl/
| #T1 #T2 #_ #IH <liberi_aabs <liberi_aabs //
]
qed-.
