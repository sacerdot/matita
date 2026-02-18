(* Questo documento fa parte della libreria digitale HELM (http://helm.cs.unibo.it)
   ed è distribuito ai sensi della licenza GNU GPL versione 2
*)

include "ground/subsets/subset_and_le.ma".
include "ground/subsets/subset_or_le.ma".
include "ground/subsets/subset_nimply_le.ma".
include "ground/subsets/subset_nimply_ol_le.ma".
include "ground/subsets/subset_nimply_and_le.ma".
include "ground/subsets/subset_nimply_and_or_le.ma".
include "canale/albero/nomi_liberi_restrizione.ma".
include "canale/eminenza/nomi_ap_legati.ma".
include "canale/eminenza/nomi_ap_liberi.ma".

(* Nomi liberi alla portata *************************************************)

(* Costruzioni coi nomi liberi e l'inclusione *******************************)

lemma ap_liberi_le (y) (w) (T):
      ℱ[w/y]T ⊆ ❨yϵℱT❩w.
#y #w #T elim T -T
[ #r <ap_liberi_refs //
| #x #T #IH <ap_liberi_nabs
  @(subset_le_trans ????? @ liberi_rest_nabs_ge …)
  @subset_rest_le_repl
  @(subset_le_trans ????? IH) -IH //
| #T #V #IHT #IHV <ap_liberi_appl
  @(subset_le_trans ????? @ liberi_rest_appl_ge …)
  /2 width=5 by subset_or_le_repl/
| #T #IH <ap_liberi_aabs <liberi_aabs //
]
qed.

(* Nota: l'inclusione inversa non vale quando T è applicazione *)
lemma ap_liberi_ge (y) (w) (T):
      ❨yϵℱT❩(w ⧵ ℬ[y]T) ⊆ ℱ[w/y]T.
#y #w #T elim T -T
[ #r <ap_legati_refs <ap_liberi_refs
  @(subset_le_trans … @ liberi_rest_refs_le …)
  @subset_rest_le_repl //
| #x #T #IH <ap_legati_nabs <ap_liberi_nabs
  @(subset_le_trans … @ liberi_rest_nabs_le …)
  @subset_rest_le_gen #Hnyx
  @subset_rest_le_gen #Hy
  @(subset_le_trans … @ subset_le_nimp_or_dx …)
  @(subset_rest_le_inv_gen … Hnyx)
  @subset_rest_le_repl
  @(subset_le_trans … @ subset_ge_nimp_and_sx_assoc_sx …)
  @subset_le_nimp_bi
  [ @(subset_le_trans … @ subset_le_and_sx_refl_dx …)
    @(subset_rest_le_inv_gen … Hy) //
  | @(subset_rest_le_inv_gen … Hy)
    @(subset_rest_le_inv_gen … Hnyx) //
  ]
| #T #V #IHT #IHV <ap_legati_appl <ap_liberi_appl
  @(subset_le_trans … @ liberi_rest_appl_le …)
  @subset_or_le_repl
  @subset_rest_le_gen #Hy
  @(subset_le_trans … @ subset_le_nimp_or_dx …)
  [ @(subset_le_trans … @ subset_le_and_sx_refl_sx …)
  | @(subset_le_trans … @ subset_le_and_sx_refl_dx …)
  ]
  @(subset_rest_le_inv_gen … Hy) //
| #T #IH <ap_legati_aabs <ap_liberi_aabs <liberi_aabs //
]
qed.

lemma ap_liberi_ge_integra (y) (w) (T):
      w ⧸≬ ℬ[y]T → ❨yϵℱT❩w ⊆ ℱ[w/y]T.
#y #w #T #H0
@(subset_le_trans ????? @ ap_liberi_ge …)
/3 width=3 by subset_rest_le_repl, subset_le_nimp_dx_refl_sx_fwd/
qed.
