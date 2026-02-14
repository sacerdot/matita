(* Questo documento fa parte della libreria digitale HELM (http://helm.cs.unibo.it)
   ed è distribuito ai sensi della licenza GNU GPL versione 2
*)

include "ground/subsets/subset_nimply_and_or_le.ma".
include "ground/subsets/subset_rest_or_le.ma".
include "ground/subsets/subset_help.ma".
include "canale/albero/nomi_liberi_restrizione.ma".
include "canale/eminenza/nomi_u_legati_le.ma".
include "canale/eminenza/sostituzione_liberi.ma".

(* Sostituzione *************************************************************)

(* Costruzioni avanzate coi nomi liberi *************************************)
(*
lemma liberi_sost_ge_sx (x) (V) (T):
      ❨xϵℱT❩(ℱV ⧵ ℬ﹗[x]T) ⊆ ℱ[V/x]T.
#y #W #T elim T -T
[ #r
(*
  #H0 <(in_liberi_inv_refs … H0) -r
  <sost_refs_eq
  /2 width=2 by subset_le_nimp_sx_refl_sx/
*)
| #x #T #IH
  @(subset_le_trans … @ liberi_rest_nabs_le …)
  @subset_rest_le #Hnyx
  @subset_rest_le #Hy
  lapply (subset_le_trans … (subset_rest_ge_refl … Hy) … IH) -IH #IH
  <(sost_nabs_neq … Hnyx) <liberi_nabs
  lapply (u_legati_nabs_libero_ge … Hy Hnyx) -Hnyx #HB1
  lapply (u_legati_nabs_ge y x T) #HB2
  @(subset_le_trans ????? @ subset_le_nimp_bi … IH @ subset_le_refl …) -IH -Hy
  @(subset_le_trans ????? @ subset_le_nimp_or_dx …)
  /3 width=5 by subset_le_nimp_bi, subset_le_or_sx/
| #T #V #IHT #IHV
  <u_legati_appl <sost_appl <liberi_appl <liberi_appl
  @(subset_le_trans … @ subset_rest_le_repl … @ subset_le_nimp_and_dx ?????)
  [ /2 width=1 by in_u_legati_dec, or_introl/ ]
  @subset_rest_le #Hy




  @(subset_le_trans … @ liberi_rest_appl_le …)

  
  
  @(subset_le_trans … @ subset_rest_or_le …)
   


  @(subset_le_trans … @ subset_le_nimp_and_dx …)
  
  elim Hy -Hy #Hy [ lapply (IHT ?) | lapply (IHV ?) ] // -IHT -IHV -Hy #HB
  @(subset_le_trans … @ subset_le_trans ????? HB) -HB
  [1,3: @subset_le_nimp_bi ] // (**) (* auto fails *)
| #T #IH <liberi_aabs #Hy <u_legati_aabs <sost_aabs <liberi_aabs
  /2 width=1 by/
]
qed.
*)

lemma liberi_sost_le (x) (V) (T):
      ℱ[V/x]T ⊆ (ℱV ⧵ ℬ﹗[x]T) ∪ (ℱT ⧵ ❴x❵).
#y #W #T elim T -T
[ #r <u_legati_refs
  elim (in_liberi_dec r y) #H0
  [ <(in_liberi_inv_refs … H0) -r <sost_refs_eq
    /3 width=1 by subset_or_in_sx, subset_le_nimp_dx_refl_empty/
  | /3 width=3 by liberi_sost_le_non_libero, subset_dx_le_or/
  ]
| #x #T #IH
  elim (in_liberi_dec (𝛌x.T) y)
  [ <liberi_nabs * #Hy #H0
    lapply (subset_nin_inv_single ??? H0) -H0 #Hnyx
    <(sost_nabs_neq … Hnyx) -Hnyx <liberi_nabs
    @(subset_le_trans … @ subset_le_nimp_bi … IH @ subset_le_refl …) -IH -Hy
    @(subset_le_trans … @ subset_le_nimp_or_sx …)
    @subset_or_le_repl [| // ]
    @(subset_le_trans … @ subset_le_nimp_comm_dx …)
    @(subset_le_trans … @ subset_ge_nimp_or_dx …)
    @subset_le_nimp_bi // (**) (* auto fails *)
  | /3 width=3 by liberi_sost_le_non_libero, subset_dx_le_or/
  ]
| #T #V #IHT #IHV <sost_appl <liberi_appl <u_legati_appl <liberi_appl
  @(subset_le_trans … @ subset_or_le_repl … IHT … IHV) -IHT -IHV
  @(subset_le_trans … @ subset_le_help_1 …)
  @subset_or_le_repl // (**) (* auto fails *)
| #T #IH <sost_aabs <liberi_aabs <u_legati_aabs <liberi_aabs //
]
qed.
